/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

Elaboration of syntax quotations as terms and patterns (in `match_syntax`). See also `./Hygiene.lean` for the basic
hygiene workings and data types.
-/
prelude
import Init.Lean.Syntax
import Init.Lean.Elab.ResolveName
import Init.Lean.Elab.Term
import Init.Lean.Parser -- TODO: remove after removing old elaborator

/- TODO

Quotations are currently integrated hackily into the old frontend. This implies the following restrictions:
* quotations have to fit in a single line, because that's how the old scanner works :)
* no namespace information: references to constants must use full names
* antiquotation terms have to be trivial (locals, fully-qualified consts, and apps (no projections), basically)

After removing the old frontend, quotations in this and other files should be cleaned up.
-/

namespace Lean

/-- Reflect a runtime datum back to surface syntax (best-effort). -/
class HasQuote (α : Type) :=
(quote : α → Syntax)

export HasQuote (quote)

instance Syntax.HasQuote : HasQuote Syntax := ⟨id⟩
instance String.HasQuote : HasQuote String := ⟨mkStxStrLit⟩
instance Nat.HasQuote : HasQuote Nat := ⟨fun n => mkStxNumLit $ toString n⟩

private def quoteName : Name → Syntax
| Name.anonymous => Unhygienic.run `(_root_.Lean.Name.anonymous)
| Name.str n s _ => Unhygienic.run `(_root_.Lean.mkNameStr %%(quoteName n) %%(Lean.HasQuote.quote s))
| Name.num n i _ => Unhygienic.run `(_root_.Lean.mkNameNum %%(quoteName n) %%(Lean.HasQuote.quote i))

instance Name.HasQuote : HasQuote Name := ⟨quoteName⟩

private def appN (fn : Syntax) (args : Array Syntax) : Syntax :=
args.foldl (fun fn arg => Unhygienic.run `(%%fn %%arg)) fn

instance Prod.HasQuote {α β : Type} [HasQuote α] [HasQuote β] : HasQuote (α × β) :=
⟨fun ⟨a, b⟩ => Unhygienic.run `(_root_.Prod.mk %%(Lean.HasQuote.quote a) %%(Lean.HasQuote.quote b))⟩

private def quoteList {α : Type} [HasQuote α] : List α → Syntax
| [] =>      Unhygienic.run `(_root_.List.nil)
| (x::xs) => Unhygienic.run `(_root_.List.cons %%(Lean.HasQuote.quote x) %%(quoteList xs))

instance List.HasQuote {α : Type} [HasQuote α] : HasQuote (List α) := ⟨quoteList⟩

instance Array.HasQuote {α : Type} [HasQuote α] : HasQuote (Array α) :=
⟨fun xs => let stx := quote xs.toList; Unhygienic.run `(_root_.List.toArray %%stx)⟩

namespace Elab
namespace Term

-- `%%e*` is an antiquotation "splice" matching an arbitrary number of syntax nodes
private def isAntiquotSplice (stx : Syntax) : Bool :=
stx.isOfKind `Lean.Parser.Term.antiquot && (stx.getArg 3).getOptional.isSome

-- If an antiquotation splice is the sole item of a `many` node, its result should
-- be substituted for the `many` node
private def isAntiquotSplicePat (stx : Syntax) : Bool :=
stx.isOfKind nullKind && stx.getArgs.size == 1 && isAntiquotSplice (stx.getArg 0)

-- Elaborate the content of a syntax quotation term
private partial def quoteSyntax (env : Environment) : Syntax → TermElabM Syntax
| Syntax.ident info rawVal val preresolved => do
  -- Add global scopes at compilation time (now), add macro scope at runtime (in the quotation).
  -- See the paper for details.
  currNamespace ← getCurrNamespace;
  openDecls     ← getOpenDecls;
  let preresolved := resolveGlobalName env currNamespace openDecls val ++ preresolved;
  let val := quote val;
  -- `scp` is bound in stxQuot.expand
  val ← `(Lean.addMacroScope %%val scp);
  let args := quote preresolved;
  -- TODO: simplify quotations when we're no longer limited by name resolution in the old frontend
  `(Lean.Syntax.ident Option.none (String.toSubstring %%(Lean.mkStxStrLit (HasToString.toString rawVal))) %%val %%args)
-- if antiquotation, insert contents as-is, else recurse
| stx@(Syntax.node k args) =>
  if k == `Lean.Parser.Term.antiquot then
    -- splices must occur in a `many` node
    if isAntiquotSplice stx then throwError stx "unexpected antiquotation splice"
    else pure $ stx.getArg 1
  else if isAntiquotSplicePat stx then
    -- top-level antiquotation splice pattern: inject args array
    let quoted := (args.get! 0).getArg 1;
    `(Lean.Syntax.node Lean.nullKind %%quoted)
  else do
    let k := quote k;
    args ← quote <$> args.mapM quoteSyntax;
    `(Lean.Syntax.node %%k %%args)
| Syntax.atom info val =>
  `(Lean.Syntax.atom Option.none %%(Lean.mkStxStrLit val))
| Syntax.missing => unreachable!

def stxQuot.expand (env : Environment) (stx : Syntax) : TermElabM Syntax := do
let quoted := stx.getArg 1;
-- Syntax quotations are monadic values depending on the current macro scope. For efficiency, we bind
-- the macro scope once for each quotation, then build the syntax tree in a completely pure computation
-- depending on this binding.
-- TODO: simplify to `(do scp ← getCurrMacroScope; pure %%(quoteSyntax env 0 quoted))
stx ← quoteSyntax env 0 quoted;
`(HasBind.bind Lean.MonadQuotation.getCurrMacroScope (fun scp => HasPure.pure %%stx))

@[builtinTermElab stxQuot] def elabStxQuot : TermElab :=
fun stx expectedType? => do
  env ← getEnv;
  stx ← stxQuot.expand env (stx.getArg 1);
  elabTerm stx expectedType?

/- match_syntax -/

-- an "alternative" of patterns plus right-hand side
private abbrev Alt := List Syntax × Syntax

-- If `pat` is an unconditional pattern, return a transformation of the RHS that appropriately introduces
-- bindings on the RHS.
private def isVarPat? (pat : Syntax) : Option (Syntax → TermElabM Syntax) :=
-- TODO: reimplement using match_syntax
if pat.isOfKind `Lean.Parser.Term.id then some $ fun rhs => `(let %%pat := discr; %%rhs)
else if pat.isOfKind `Lean.Parser.Term.hole then some pure
else if pat.isOfKind `Lean.Parser.Term.stxQuot then
  let quoted := pat.getArg 1;
  -- We assume that atoms are uniquely determined by the surrounding node and never have to be checked
  if quoted.isAtom then some pure
  -- TODO: antiquotations with kinds (`%%id:id`) probably can't be handled as unconditional patterns
  else if quoted.isOfKind `Lean.Parser.Term.antiquot then
    let anti := quoted.getArg 1;
    if isAntiquotSplice quoted then some $ fun _ => throwError quoted "unexpected antiquotation splice"
    else if anti.isOfKind `Lean.Parser.Term.id then some $ fun rhs => `(let %%anti := discr; %%rhs)
    else unreachable!
  else if isAntiquotSplicePat quoted then
    let anti := (quoted.getArg 0).getArg 1;
    some $ fun rhs => `(let %%anti := Lean.Syntax.getArgs discr; %%rhs)
  else none
else none

-- If the first pattern of the alternative is a conditional pattern, return the node we should match against
private def altNextNode? : Alt → Option SyntaxNode
| (pat::_, _) =>
  if (isVarPat? pat).isNone && pat.isOfKind `Lean.Parser.Term.stxQuot then
    let quoted := pat.getArg 1;
    some quoted.asNode
  else none
| _ => none

-- Assuming that the first pattern of the alternative is taken, replace it with patterns (if any) for its
-- child nodes.
-- Ex: `(%%a + (- %%b)) => `(%%a), `(+), `(- %%b)
-- Note: The atom pattern `(+) will be discarded in a later step
private def explodeHeadPat (numArgs : Nat) : Alt → TermElabM Alt
| (pat::pats, rhs) => match isVarPat? pat with
  | some fnRhs => do
    -- unconditional pattern: replace with appropriate number of wildcards
    newPat ← `(_);
    let newPats := List.replicate numArgs newPat;
    rhs ← fnRhs rhs;
    pure (newPats ++ pats, rhs)
  | none =>
    if pat.isOfKind `Lean.Parser.Term.stxQuot then do
      let quoted := pat.getArg 1;
      let newPats := quoted.getArgs.toList.map $ fun arg => Syntax.node `Lean.Parser.Term.stxQuot #[mkAtom "`(", arg, mkAtom ")"];
      pure (newPats ++ pats, rhs)
    else throwError pat $ "unsupported `syntax_match` pattern kind " ++ toString pat.getKind
| _ => unreachable!

-- The "shape" is the information that should be compared in a single matching step. Currently, it is the node kind
-- and its arity (which is not constant in the case of `many` nodes)
private def nodeShape (n : SyntaxNode) : SyntaxNodeKind × Nat :=
(n.getKind, n.getArgs.size)

private partial def compileStxMatch (ref : Syntax) : List Syntax → List Alt → TermElabM Syntax
| [],            ([], rhs)::_ => pure rhs  -- nothing left to match
| _,             []           => throwError ref "non-exhaustive 'match_syntax'"
| discr::discrs, alts         =>
  match alts.findSome? altNextNode? with
  -- at least one conditional pattern: introduce an `if` for it and recurse
  | some node => do
    let shape := nodeShape node;
    -- introduce pattern matches on the discriminant's children
    newDiscrs ← (List.range node.getArgs.size).mapM $ fun i => `(Lean.Syntax.getArg discr %%(Lean.HasQuote.quote i));
    -- collect matching alternatives and explode them
    let yesAlts := alts.filter $ fun alt => match altNextNode? alt with some n => nodeShape n == shape | none => true;
    yesAlts ← yesAlts.mapM $ explodeHeadPat node.getArgs.size;
    -- non-matching alternatives are left as-is
    -- NOTE: unconditional patterns must go into both `yesAlts` and `noAlts`
    let noAlts  := alts.filter $ fun alt => match altNextNode? alt with some n => nodeShape n != shape | none => true;
    -- NOTE: use fresh macro scopes for recursion so that different `discr`s introduced by the quotation below do not collide
    yes ← withFreshMacroScope $ compileStxMatch (newDiscrs ++ discrs) yesAlts;
    no  ← withFreshMacroScope $ compileStxMatch (discr::discrs) noAlts;
    `(let discr := %%discr; if Lean.Syntax.isOfKind discr %%(Lean.HasQuote.quote (Prod.fst shape)) && Array.size (Lean.Syntax.getArgs discr) == %%(Lean.HasQuote.quote (Prod.snd shape)) then %%yes else %%no)
  -- only unconditional patterns: introduce binds and discard patterns
  | none => do
    alts ← alts.mapM $ explodeHeadPat 0;
    res ← withFreshMacroScope $ compileStxMatch discrs alts;
    `(let discr := %%discr; %%res)
| _, _ => unreachable!

private partial def getAntiquotVarsAux : Syntax → TermElabM (List Syntax)
| Syntax.node `Lean.Parser.Term.antiquot args =>
  let anti := args.get! 1;
  if anti.isOfKind `Lean.Parser.Term.id then pure [anti]
  else throwError anti "syntax_match: antiquotation must be variable"
| Syntax.node k args => do
  List.join <$> args.toList.mapM getAntiquotVarsAux
| _ => pure []

-- Get all antiquotations (as Term.id nodes) in `stx`
private partial def getAntiquotVars (stx : Syntax) : TermElabM (List Syntax) :=
if stx.isOfKind `Lean.Parser.Term.stxQuot then do
  let quoted := stx.getArg 1;
  getAntiquotVarsAux stx
else pure []

-- Transform alternatives by binding all right-hand sides to outside the match_syntax in order to prevent
-- code duplication during match_syntax compilation
private def letBindRhss (cont : List Alt → TermElabM Syntax) : List Alt → List Alt → TermElabM Syntax
| [],                altsRev' => cont altsRev'.reverse
| (pats, rhs)::alts, altsRev' => do
  vars ← List.join <$> pats.mapM getAntiquotVars;
  match vars with
  -- no antiquotations => introduce Unit parameter to preserve evaluation order
  | [] => do
    -- NOTE: references binding below
    rhs' ← `(rhs ());
    -- NOTE: new macro scope so that introduced bindings do not collide
    stx ← withFreshMacroScope $ letBindRhss alts ((pats, rhs')::altsRev');
    `(let rhs := fun _ => %%rhs; %%stx)
  | _ => do
    -- rhs ← `(fun %%vars* => %%rhs)
    let rhs := Syntax.node `Lean.Parser.Term.fun #[mkAtom "fun", Syntax.node `null vars.toArray, mkAtom "=>", rhs];
    rhs' ← `(rhs);
    stx ← withFreshMacroScope $ letBindRhss alts ((pats, rhs')::altsRev');
    `(let rhs := %%rhs; %%stx)

def match_syntax.expand (stx : SyntaxNode) : TermElabM Syntax := do
let discr := stx.getArg 1;
let alts := stx.getArg 3;
alts ← alts.getArgs.mapM $ fun alt => do {
  let pats := alt.getArg 1;
  pat ← if pats.getArgs.size == 1 then pure $ pats.getArg 0
    else throwError stx.val "syntax_match: expected exactly one pattern per alternative";
  let rhs := alt.getArg 3;
  pure ([pat], rhs)
};
-- letBindRhss (compileStxMatch stx.val [discr]) alts.toList []
compileStxMatch stx.val [discr] alts.toList

@[builtinTermElab «match_syntax»] def elabMatchSyntax : TermElab :=
fun stx expectedType? => do
  stx ← match_syntax.expand stx;
  elabTerm stx expectedType?

-- REMOVE with old frontend
private def exprPlaceholder := mkMVar Name.anonymous

private unsafe partial def toPreterm (env : Environment) : Syntax → Except String Expr
| stx =>
  let args := stx.getArgs;
  match stx.getKind with
  | `Lean.Parser.Term.id =>
    match args.get! 0 with
    | Syntax.ident _ _ val preresolved =>
      -- TODO: pass scope information
      let ns := Name.anonymous;
      let openDecls := [];
      let resolved := resolveGlobalName env ns openDecls val <|> preresolved;
      match resolved with
      | (pre,[])::_ => pure $ Lean.mkConst pre
      | [] => pure $ mkFVar val
      | _ => throw "stxQuot: unimplemented: projection notation"
    | _ => unreachable!
  | `Lean.Parser.Term.fun => do
    let params := (args.get! 1).getArgs;
    body ← toPreterm $ args.get! 3;
    params.foldrM (fun param e => do
      (n, ty) ← if param.isOfKind `Lean.Parser.Term.id then
          pure (param.getIdAt 0, exprPlaceholder)
        else if param.isOfKind `Lean.Parser.Term.hole then
          pure (`_a, exprPlaceholder)
        else do {
          let n := ((param.getArg 1).getArg 0).getIdAt 0;
          ty ← toPreterm $ (((param.getArg 1).getArg 1).getArg 0).getArg 1;
          pure (n, ty)
        };
      pure $ Lean.mkLambda n BinderInfo.default ty (Expr.abstract e #[mkFVar n]))
      body
  | `Lean.Parser.Term.let => do
    let ⟨n, val⟩ := show Name × Syntax from match (args.get! 1).getKind with
      | `Lean.Parser.Term.letIdDecl  => ((args.get! 1).getIdAt 0, (args.get! 1).getArg 4)
      | `Lean.Parser.Term.letPatDecl => (((args.get! 1).getArg 0).getIdAt 0, (args.get! 1).getArg 3)
      | _                            => unreachable!;
    val ← toPreterm val;
    body ← toPreterm $ args.get! 3;
    pure $ mkLet n exprPlaceholder val (Expr.abstract body #[mkFVar n])
  | `Lean.Parser.Term.app => do
    fn ← toPreterm $ args.get! 0;
    arg ← toPreterm $ args.get! 1;
    pure $ mkApp fn arg
  | `Lean.Parser.Term.if => do
    let con := args.get! 2;
    let yes := args.get! 4;
    let no := args.get! 6;
    toPreterm $ Unhygienic.run `(ite %%con %%yes %%no)
  | `Lean.Parser.Term.paren =>
    let inner := (args.get! 1).getArgs;
    if inner.size == 0 then pure $ Lean.mkConst `Unit.unit
    else toPreterm $ inner.get! 0
  | `Lean.Parser.Term.band =>
    let lhs := args.get! 0; let rhs := args.get! 2;
    toPreterm $ Unhygienic.run `(and %%lhs %%rhs)
  | `Lean.Parser.Term.beq =>
    let lhs := args.get! 0; let rhs := args.get! 2;
    toPreterm $ Unhygienic.run `(HasBeq.beq %%lhs %%rhs)
  | `strLit => pure $ mkStrLit $ stx.isStrLit?.getD ""
  | `numLit => pure $ mkNatLit $ stx.isNatLit?.getD 0
  | `expr => pure $ unsafeCast $ stx.getArg 0  -- HACK: see below
  | k => throw $ "stxQuot: unimplemented kind " ++ toString k

@[export lean_parse_expr]
def oldParseExpr (env : Environment) (input : String) (pos : String.Pos) : Except String (Syntax × String.Pos) := do
let c := Parser.mkParserContextCore env input "<foo>";
let c := c.toParserContext env;
let s := Parser.mkParserState c.input;
let s := s.setPos pos;
let s := (Parser.termParser : Parser.Parser).fn (0 : Nat) c s;
let stx := s.stxStack.back;
match s.errorMsg with
| some errorMsg =>
  Except.error $ toString errorMsg
| none =>
  Except.ok (stx, s.pos)

private def oldRunTermElabM {α} (env : Environment) (x : TermElabM α) : Except String α := do
match x {fileName := "foo", fileMap := FileMap.ofString "", cmdPos := 0, currNamespace := `foo} {env := env} with
| EStateM.Result.ok a _    => Except.ok a
| EStateM.Result.error msg _ => Except.error $ toString msg

@[export lean_expand_stx_quot]
unsafe def oldExpandStxQuot (env : Environment) (stx : Syntax) : Except String Expr := do
stx ← oldRunTermElabM env $ stxQuot.expand env stx;
toPreterm env stx

@[export lean_get_antiquot_vars]
def oldGetAntiquotVars (env : Environment) (pats : List Syntax) : Except String (List Name) := oldRunTermElabM env $ do
vars ← List.join <$> pats.mapM getAntiquotVars;
pure $ vars.map $ fun var => var.getIdAt 0

@[export lean_expand_match_syntax]
unsafe def oldExpandMatchSyntax (env : Environment) (discr : Syntax) (alts : List (List Syntax × Syntax)) : Except String Expr := do
stx ← oldRunTermElabM env $ do {
  -- HACK: discr and the RHSs are actually `Expr`
  let discr := Syntax.node `expr #[discr];
  let alts := alts.map $ fun alt => (alt.1, Syntax.node `expr #[alt.2]);
  -- letBindRhss (compileStxMatch Syntax.missing [discr]) alts []
  compileStxMatch Syntax.missing [discr] alts
};
toPreterm env stx

end Term
end Elab
end Lean
