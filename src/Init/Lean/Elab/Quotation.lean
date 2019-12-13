/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Init.Lean.Syntax
import Init.Lean.Elab.ResolveName
import Init.Lean.Elab.Term
import Init.Lean.Parser -- TODO: remove after removing old elaborator

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

private partial def quoteSyntax {m : Type → Type} [Monad m] [MonadQuotation m] (env : Environment) : Nat → Syntax → m Syntax
| _, Syntax.ident info rawVal val preresolved => do
  -- TODO: pass scope information
  let ns := Name.anonymous;
  let openDecls := [];
  let preresolved := resolveGlobalName env ns openDecls val <|> preresolved;
  let val := quote val;
  -- `scp` is bound in stxQuot.expand
  val ← `(Lean.addMacroScope %%val scp);
  let args := quote preresolved;
  `(Lean.Syntax.ident Option.none (String.toSubstring %%(Lean.mkStxStrLit (HasToString.toString rawVal))) %%val %%args)
| 0, Syntax.node `Lean.Parser.Term.antiquot args => pure $ args.get! 1
| lvl, Syntax.node k args => do
  let lvl := match k with
    | `Lean.Parser.Term.stxQuot => lvl + 1
    | `Lean.Parser.Term.antiquot => lvl - 1
    | _ => lvl;
  let k := quote k;
  args ← quote <$> args.mapM (quoteSyntax lvl);
  `(Lean.Syntax.node %%k %%args)
| _, Syntax.atom info val =>
  `(Lean.Syntax.atom Option.none %%(Lean.mkStxStrLit val))
| _, Syntax.missing => unreachable!

def stxQuot.expand {m : Type → Type} [Monad m] [MonadQuotation m] (env : Environment) (stx : Syntax) : m Syntax := do
let quoted := stx.getArg 1;
-- `(do msc ← getCurrMacroScope; pure %(quoteSyntax env 0 quoted))
stx ← quoteSyntax env 0 quoted;
`(HasBind.bind Lean.MonadQuotation.getCurrMacroScope (fun scp => HasPure.pure %%stx))

@[builtinTermElab stxQuot] def elabStxQuot : TermElab :=
fun stx expectedType? => do
  env ← getEnv;
  stx ← stxQuot.expand env (stx.getArg 1);
  elabTerm stx expectedType?

-- REMOVE with old frontend
private def exprPlaceholder := mkMVar Name.anonymous

private partial def toPreterm (env : Environment) : Syntax → Except String Expr
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
      | (pre,[])::_ => pure $ mkConst pre
      | [] => pure $ mkFVar val
      | _ => throw "stxQuot: unimplemented: projection notation"
    | _ => unreachable!
  | `Lean.Parser.Term.fun => do
    let ids := (args.get! 1).getArgs;
    body ← toPreterm $ args.get! 3;
    pure $ ids.foldr (fun id e =>
      let n := id.getIdAt 0;
      Lean.mkLambda n BinderInfo.default exprPlaceholder (Expr.abstract e #[mkFVar n]))
      body
  | `Lean.Parser.Term.let => do
    let n := (args.get! 1).getIdAt 0;
    val ← toPreterm $ (args.get! 1).getArg 4;
    body ← toPreterm $ args.get! 3;
    pure $ mkLet n exprPlaceholder val (Expr.abstract body #[mkFVar n])
  | `Lean.Parser.Term.app => do
    fn ← toPreterm $ args.get! 0;
    arg ← toPreterm $ args.get! 1;
    pure $ mkApp fn arg
  | `Lean.Parser.Term.paren => toPreterm $ (args.get! 1).getArg 0
  | `strLit => pure $ mkStrLit $ stx.isStrLit?.getD ""
  | `numLit => pure $ mkNatLit $ stx.isNatLit?.getD 0
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

@[export lean_expand_stx_quot]
unsafe def oldExpandStxQuot (env : Environment) (stx : Syntax) : Except String Expr := do
let stx := Unhygienic.run $ stxQuot.expand env stx;
toPreterm env stx

end Term
end Elab
end Lean
