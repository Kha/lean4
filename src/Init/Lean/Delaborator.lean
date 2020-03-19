/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

/-!
The delaborator is the first stage of the pretty printer, and the inverse of the
elaborator: it turns fully elaborated `Expr` core terms back into surface-level
`Syntax`, omitting some implicit information again and using higher-level syntax
abstractions like notations where possible. The exact behavior can be customized
using pretty printer options; activating `pp.all` should guarantee that the
delaborator is injective and that re-elaborating the resulting `Syntax`
round-trips.

Pretty printer options can be given not only for the whole term, but also
specific subterms. This is used both when automatically refining pp options
until round-trip and when interactively selecting pp options for a subterm (both
TBD). The association of options to subterms is done by assigning a unique,
synthetic Nat position to each subterm derived from its position in the full
term. This position is added to the corresponding Syntax object so that
elaboration errors and interactions with the pretty printer output can be traced
back to the subterm.

The delaborator is extensible via the `[delab]` attribute.
-/

prelude
import Init.Lean.KeyedDeclsAttribute
import Init.Lean.Parser.Level  -- for level quotations
import Init.Lean.Elab

namespace Lean

-- TODO: move, maybe
namespace Level
protected partial def quote : Level → Syntax
| zero _       => Unhygienic.run `(level|0)
| l@(succ _ _) => match l.toNat with
  | some n => Unhygienic.run `(level|$(mkStxNumLitAux n):numLit)
  | none   => Unhygienic.run `(level|$(quote l.getLevelOffset) + $(mkStxNumLitAux l.getOffset):numLit)
| max l1 l2 _  => match_syntax quote l2 with
  | `(level|max $ls*) => Unhygienic.run `(level|max $(quote l1) $ls*)
  | l2                => Unhygienic.run `(level|max $(quote l1) $l2)
| imax l1 l2 _ => match_syntax quote l2 with
  | `(level|imax $ls*) => Unhygienic.run `(level|imax $(quote l1) $ls*)
  | l2                 => Unhygienic.run `(level|imax $(quote l1) $l2)
| param n _    => Unhygienic.run `(level|$(mkIdent n):ident)
-- HACK: approximation
| mvar  n _    => Unhygienic.run `(level|_)

instance HasQuote : HasQuote Level := ⟨Level.quote⟩
end Level

def getPPBinderTypes (o : Options) : Bool := o.get `pp.binder_types true
def getPPExplicit (o : Options) : Bool := o.get `pp.explicit false
def getPPUniverses (o : Options) : Bool := o.get `pp.universes false
def getPPAll (o : Options) : Bool := o.get `pp.all false

@[init] def ppOptions : IO Unit := do
registerOption `pp.explicit { defValue := false, group := "pp", descr := "(pretty printer) display implicit arguments" };
-- TODO: register other options when old pretty printer is removed
--registerOption `pp.universes { defValue := false, group := "pp", descr := "(pretty printer) display universes" };
pure ()

/-- Associate pretty printer options to a specific subterm using a synthetic position. -/
abbrev OptionsPerPos := RBMap Nat Options (fun a b => a < b)

namespace Delaborator
open Lean.Meta

structure Context :=
-- In contrast to other systems like the elaborator, we do not pass the current term explicitly as a
-- parameter, but store it in the monad so that we can keep it in sync with `pos`.
(expr           : Expr)
(pos            : Nat)
(defaultOptions : Options)
(optionsPerPos  : OptionsPerPos)

-- Exceptions from delaborators are not expected, so use a simple `OptionT` to signal whether
-- the delaborator was able to produce a Syntax object.
abbrev DelabM := ReaderT Context $ OptionT MetaM
abbrev Delab := DelabM Syntax

instance DelabM.inhabited {α} : Inhabited (DelabM α) := ⟨failure⟩

-- Macro scopes in the delaborator output are ultimately ignored by the pretty printer,
-- so give a trivial implementation.
instance DelabM.monadQuotation : MonadQuotation DelabM := {
  getCurrMacroScope   := pure $ arbitrary _,
  getMainModule       := pure $ arbitrary _,
  withFreshMacroScope := fun α x => x,
}

unsafe def mkDelabAttribute : IO (KeyedDeclsAttribute Delab) :=
KeyedDeclsAttribute.init {
  builtinName := `builtinDelab,
  name := `delab,
  descr := "Register a delaborator.

[delab k] registers a declaration of type `Lean.Delaborator.Delab` for the `Lean.Expr`
constructor `k`. Multiple delaborators for a single constructor are tried in turn until
the first success. If the term to be delaborated is an application of a constant `c`,
elaborators for `app.c` are tried first; this is also done for `Expr.const`s (\"nullary applications\")
to reduce special casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k`
is tried first.",
  valueTypeName := `Lean.Delaborator.Delab
} `Lean.Delaborator.delabAttribute
@[init mkDelabAttribute] constant delabAttribute : KeyedDeclsAttribute Delab := arbitrary _

def getExpr : DelabM Expr := do
ctx ← read;
pure ctx.expr

def getExprKind : DelabM Name := do
e ← getExpr;
pure $ match e with
| Expr.bvar _ _        => `bvar
| Expr.fvar _ _        => `fvar
| Expr.mvar _ _        => `mvar
| Expr.sort _ _        => `sort
| Expr.const c _ _     =>
  -- we identify constants as "nullary applications" to reduce special casing
  `app ++ c
| Expr.app fn _ _      => match fn.getAppFn with
  | Expr.const c _ _ => `app ++ c
  | _                => `app
| Expr.lam _ _ _ _     => `lam
| Expr.forallE _ _ _ _ => `forallE
| Expr.letE _ _ _ _ _  => `letE
| Expr.lit _ _         => `lit
| Expr.mdata m _ _     => match m.entries with
  | [(key, _)] => `mdata ++ key
  | _   => `mdata
| Expr.proj _ _ _ _    => `proj
| Expr.localE _ _ _ _  => `localE

/-- Evaluate option accessor, using subterm-specific options if set. Default to `true` if `pp.all` is set. -/
def getPPOption (opt : Options → Bool) : DelabM Bool := do
ctx ← read;
let opt := fun opts => opt opts || getPPAll opts;
let val := opt ctx.defaultOptions;
match ctx.optionsPerPos.find? ctx.pos with
| some opts => pure $ opt opts
| none      => pure val

def whenPPOption (opt : Options → Bool) (d : Delab) : Delab := do
b ← getPPOption opt;
if b then d else failure

def whenNotPPOption (opt : Options → Bool) (d : Delab) : Delab := do
b ← getPPOption opt;
if b then failure else d

/-- Descend into subterm `child`, the `childIdex`-th out of `numChildren` subterms, and update position. -/
def descend {α} (child : Expr) (childIdx numChildren : Nat) (d : DelabM α) : DelabM α :=
adaptReader (fun (cfg : Context) => { cfg with expr := child, pos := (cfg.pos + childIdx) * numChildren }) d

def withAppFn {α} (d : DelabM α) : DelabM α := do
Expr.app fn _ _ ← getExpr | unreachable!;
descend fn 0 2 d

def withAppArg {α} (d : DelabM α) : DelabM α := do
Expr.app _ arg _ ← getExpr | unreachable!;
descend arg 1 2 d

partial def withAppFnArgs {α} : DelabM α → (α → DelabM α) → DelabM α
| fnD, argD => do
  Expr.app fn arg _ ← getExpr | fnD;
  a ← withAppFn (withAppFnArgs fnD argD);
  withAppArg (argD a)

def withBindingDomain {α} (d : DelabM α) : DelabM α := do
e ← getExpr;
descend e.bindingDomain! 0 2 d

def withBindingBody {α} (n : Name) (d : DelabM α) : DelabM α := do
e ← getExpr;
fun ctx => withLocalDecl n e.bindingDomain! e.binderInfo $ fun fvar =>
  let b := e.bindingBody!.instantiate1 fvar;
  descend b 1 2 d ctx

def infoForPos (pos : Nat) : SourceInfo :=
{ leading := " ".toSubstring, pos := pos, trailing := " ".toSubstring }

partial def annotatePos (pos : Nat) : Syntax → Syntax
| stx@(Syntax.ident _ _ _ _)                   => stx.setInfo (infoForPos pos)
-- Term.ids => annotate ident
-- TODO: universes?
| stx@(Syntax.node `Lean.Parser.Term.id args)  => stx.modifyArg 0 annotatePos
-- app => annotate function
| stx@(Syntax.node `Lean.Parser.Term.app args) => stx.modifyArg 0 annotatePos
-- otherwise, annotate first direct child token if any
| stx => match stx.getArgs.findIdx? Syntax.isAtom with
  | some idx => stx.modifyArg idx (Syntax.setInfo (infoForPos pos))
  | none     => stx

def annotateCurPos (stx : Syntax) : Delab := do
ctx ← read;
pure $ annotatePos ctx.pos stx

partial def delabFor : Name → Delab
| k => do
  env ← liftM getEnv;
  (match (delabAttribute.ext.getState env).table.find? k with
   | some delabs => delabs.firstM id >>= annotateCurPos
   | none        => failure) <|>
  (match k with
   | Name.str Name.anonymous _ _ => failure
   | Name.str n              _ _ => delabFor n.getRoot  -- have `app.Option.some` fall back to `app` etc.
   | _                           => failure)

def delab : Delab := do
k ← getExprKind;
delabFor k <|> (liftM $ show MetaM Syntax from throw $ Meta.Exception.other $ "don't know how to delaborate '" ++ toString k ++ "'")

@[builtinDelab fvar]
def delabFVar : Delab := do
Expr.fvar id _ ← getExpr | unreachable!;
l ← liftM $ getLocalDecl id;
pure $ mkTermId l.userName

@[builtinDelab mvar]
def delabMVar : Delab := do
Expr.mvar n _ ← getExpr | unreachable!;
`(?$(mkIdent n))

@[builtinDelab sort]
def delabSort : Delab := do
expr ← getExpr;
match expr with
| Expr.sort (Level.zero _) _ => `(Prop)
| Expr.sort (Level.succ (Level.zero _) _) _ => `(Type)
| Expr.sort l _ => match l.dec with
  | some l' => `(Type $(quote l'))
  | none    => `(Sort $(quote l))
| _ => unreachable!

-- NOTE: not a registered delaborator, as `const` is never called (see [delab] description)
def delabConst : Delab := do
Expr.const c ls _ ← getExpr | unreachable!;
ppUnivs ← getPPOption getPPUniverses;
if ls.isEmpty || !ppUnivs then
  `($(mkIdent c):ident)
else
  `($(mkIdent c):ident.{$(ls.toArray.map quote)*})

/-- Return array with n-th element set to `true` iff n-th parameter of `e` is implicit. -/
def getImplicitParams (e : Expr) : MetaM (Array Bool) := do
t ← inferType e;
forallTelescopeReducing t $ fun params _ =>
  params.mapM $ fun param => do
    l ← getLocalDecl param.fvarId!;
    pure (!l.binderInfo.isExplicit)

@[builtinDelab app]
def delabAppExplicit : Delab := do
(fnStx, argStxs) ← withAppFnArgs
  (do
    fn ← getExpr;
    stx ← if fn.isConst then delabConst else delab;
    implicitParams ← liftM $ getImplicitParams fn;
    stx ← if implicitParams.any id then `(@$stx) else pure stx;
    pure (stx, #[]))
  (fun ⟨fnStx, argStxs⟩ => do
    argStx ← delab;
    pure (fnStx, argStxs.push argStx));
-- avoid degenerate `app` node
if argStxs.isEmpty then pure fnStx else `($fnStx $argStxs*)

@[builtinDelab app]
def delabAppImplicit : Delab := whenNotPPOption getPPExplicit $ do
(fnStx, _, argStxs) ← withAppFnArgs
  (do
    fn ← getExpr;
    stx ← if fn.isConst then delabConst else delab;
    implicitParams ← liftM $ getImplicitParams fn;
    pure (stx, implicitParams.toList, #[]))
  (fun ⟨fnStx, implicitParams, argStxs⟩ => match implicitParams with
    | true :: implicitParams => pure (fnStx, implicitParams, argStxs)
    | _ => do
      argStx ← delab;
      pure (fnStx, implicitParams.tailD [], argStxs.push argStx));
-- avoid degenerate `app` node
if argStxs.isEmpty then pure fnStx else `($fnStx $argStxs*)

/--
Return `true` iff current binder should be merged with the nested
binder, if any, into a single binder group:
* both binders must have same binder info and domain
* they cannot be inst-implicit (`[a b : A]` is not valid syntax)
* `pp.binder_types` must be the same value for both terms
* prefer `fun a b` over `fun (a b)`
-/
private def shouldGroupWithNext : DelabM Bool := do
e ← getExpr;
ppEType ← getPPOption getPPBinderTypes;
let go (e' : Expr) := do {
  ppE'Type ← withBindingBody `_ $ getPPOption getPPBinderTypes;
  pure $ e.binderInfo == e'.binderInfo &&
    e.bindingDomain! == e'.bindingDomain! &&
    e'.binderInfo != BinderInfo.instImplicit &&
    ppEType == ppE'Type &&
    (e'.binderInfo != BinderInfo.default || ppE'Type)
};
match e with
| Expr.lam _ _     e'@(Expr.lam _ _ _ _) _     => go e'
| Expr.forallE _ _ e'@(Expr.forallE _ _ _ _) _ => go e'
| _ => pure false

private partial def delabLamAux : Array Syntax → Array Syntax → Delab
-- Accumulate finished binder groups `(a b : Nat) (c : Bool) ...` and names
-- (`Syntax.ident`s with position information) of the current, unfinished
-- binder group `(d e ...)`.
| binderGroups, curNames => do
  ppTypes ← getPPOption getPPBinderTypes;
  e@(Expr.lam n t body _) ← getExpr | unreachable!;
  lctx ← liftM $ getLCtx;
  let n := lctx.getUnusedName n;
  stxN ← annotateCurPos (mkIdent n);
  let curNames := curNames.push stxN;
  condM shouldGroupWithNext
    -- group with nested binder => recurse immediately
    (withBindingBody n $ delabLamAux binderGroups curNames) $
    -- don't group => finish current binder group
    do
      stxT ← withBindingDomain delab;
      group ← match e.binderInfo, ppTypes with
        | BinderInfo.default,     true   => do
          -- "default" binder group is the only one that expects binder names
          -- as a term, i.e. a single `Term.id` or an application thereof
          let curNames := curNames.map mkTermIdFromIdent;
          stxCurNames ← if curNames.size > 1 then `($(curNames.get! 0) $(curNames.eraseIdx 0)*)
            else pure $ curNames.get! 0;
          `(funBinder| ($stxCurNames : $stxT))
        | BinderInfo.default,     false  => pure $ mkTermIdFromIdent stxN  -- here `curNames == #[stxN]`
        | BinderInfo.implicit,    true   => `(funBinder| {$curNames* : $stxT})
        | BinderInfo.implicit,    false  => `(funBinder| {$curNames*})
        -- here `curNames == #[stxN]`
        | BinderInfo.instImplicit, _     => `(funBinder| [$stxN : $stxT])
        | _                      , _     => unreachable!;
      let binderGroups := binderGroups.push group;
      withBindingBody n $
        if body.isLambda then
          delabLamAux binderGroups #[]
        else do
          stxBody ← delab;
          `(@(fun $binderGroups* => $stxBody))

@[builtinDelab lam]
def delabExplicitLam : Delab :=
delabLamAux #[] #[]

-- TODO: implicit lambdas

@[builtinDelab lit]
def delabLit : Delab := do
Expr.lit l _ ← getExpr | unreachable!;
match l with
| Literal.natVal n => pure $ quote n
| Literal.strVal s => pure $ quote s

end Delaborator

/-- "Delaborate" the given term into surface-level syntax using the given general and subterm-specific options. -/
def delab (e : Expr) (defaultOptions : Options) (optionsPerPos : OptionsPerPos := {}) : MetaM Syntax := do
some stx ← Delaborator.delab { expr := e, pos := 1, defaultOptions := defaultOptions, optionsPerPos := optionsPerPos }
  | unreachable!;
pure stx

end Lean
