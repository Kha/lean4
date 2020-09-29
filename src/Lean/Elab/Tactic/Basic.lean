/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Util.CollectMVars
import Lean.Meta.Tactic.Assumption
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Revert
import Lean.Meta.Tactic.Subst
import Lean.Elab.Util
import Lean.Elab.Term
import Lean.Elab.Binders

namespace Lean
namespace Elab

open Meta

def goalsToMessageData (goals : List MVarId) : MessageData :=
MessageData.joinSep (goals.map $ MessageData.ofGoal) (Format.line ++ Format.line)

def Term.reportUnsolvedGoals (goals : List MVarId) : TermElabM Unit := do
throwError $ "unsolved goals" ++ Format.line ++ goalsToMessageData goals

namespace Tactic

structure Context :=
(main : MVarId)

structure State :=
(goals : List MVarId)

instance State.inhabited : Inhabited State := ⟨{ goals := [] }⟩

structure BacktrackableState :=
(env   : Environment)
(mctx  : MetavarContext)
(goals : List MVarId)

abbrev TacticM := ReaderT Context $ StateRefT State $ TermElabM
abbrev Tactic  := Syntax → TacticM Unit

def saveBacktrackableState : TacticM BacktrackableState := do
env ← getEnv;
mctx ← getMCtx;
s ← get;
pure { env := env, mctx := mctx, goals := s.goals }

def BacktrackableState.restore (b : BacktrackableState) : TacticM Unit := do
setEnv b.env;
setMCtx b.mctx;
modify fun s => { s with goals := b.goals }

@[inline] protected def catch {α} (x : TacticM α) (h : Exception → TacticM α) : TacticM α := do
b ← saveBacktrackableState;
catch x (fun ex => do b.restore; h ex)

@[inline] protected def orelse {α} (x y : TacticM α) : TacticM α := do
catch x (fun _ => y)

instance monadExcept : MonadExcept Exception TacticM :=
{ throw := fun _ => throw,
  catch := fun _ x h => Tactic.catch x h }

instance hasOrElse {α} : HasOrelse (TacticM α) := ⟨Tactic.orelse⟩

structure SavedState :=
(core   : Core.State)
(meta   : Meta.State)
(term   : Term.State)
(tactic : State)

instance SavedState.inhabited : Inhabited SavedState := ⟨⟨arbitrary _, arbitrary _, arbitrary _, arbitrary _⟩⟩

def saveAllState : TacticM SavedState := do
core   ← getThe Core.State;
meta   ← getThe Meta.State;
term   ← getThe Term.State;
tactic ← get;
pure { core := core, meta := meta, term := term, tactic := tactic }

def SavedState.restore (s : SavedState) : TacticM Unit := do
set s.core; set s.meta; set s.term; set s.tactic

@[inline] def liftTermElabM {α} (x : TermElabM α) : TacticM α :=
liftM x

@[inline] def liftMetaM {α} (x : MetaM α) : TacticM α :=
liftTermElabM $ Term.liftMetaM x

def ensureHasType (expectedType? : Option Expr) (e : Expr) : TacticM Expr := liftTermElabM $ Term.ensureHasType expectedType? e
def reportUnsolvedGoals (goals : List MVarId) : TacticM Unit := liftTermElabM $ Term.reportUnsolvedGoals goals

protected def getCurrMacroScope : TacticM MacroScope := do ctx ← readThe Term.Context; pure ctx.currMacroScope
protected def getMainModule     : TacticM Name       := do env ← getEnv; pure env.mainModule

unsafe def mkTacticAttribute : IO (KeyedDeclsAttribute Tactic) :=
mkElabAttribute Tactic `Lean.Elab.Tactic.tacticElabAttribute `builtinTactic `tactic `Lean.Parser.Tactic `Lean.Elab.Tactic.Tactic "tactic"
@[init mkTacticAttribute] constant tacticElabAttribute : KeyedDeclsAttribute Tactic := arbitrary _

private def evalTacticUsing (s : SavedState) (stx : Syntax) : List Tactic → TacticM Unit
| []                => do
  throwErrorAt stx ("unexpected syntax" ++ MessageData.nest 2 (Format.line ++ stx))
| (evalFn::evalFns) => catch (evalFn stx)
  (fun ex => match ex with
    | Exception.error _ _  =>
      match evalFns with
      | [] => throw ex
      | _  => do s.restore; evalTacticUsing evalFns
    | Exception.internal id =>
      if id == unsupportedSyntaxExceptionId then do
        s.restore; evalTacticUsing evalFns
      else
        throw ex)

/- Elaborate `x` with `stx` on the macro stack -/
@[inline] def withMacroExpansion {α} (beforeStx afterStx : Syntax) (x : TacticM α) : TacticM α :=
adaptTheReader Term.Context (fun ctx => { ctx with macroStack := { before := beforeStx, after := afterStx } :: ctx.macroStack }) x

@[specialize] private def expandTacticMacroFns (evalTactic : Syntax → TacticM Unit) (stx : Syntax) : List Macro → TacticM Unit
| []    => throwErrorAt stx ("tactic '" ++ toString stx.getKind ++ "' has not been implemented")
| m::ms => do
  scp  ← getCurrMacroScope;
  catch
    (do stx' ← adaptMacro m stx; evalTactic stx')
    (fun ex => match ms with
      | [] => throw ex
      | _  => expandTacticMacroFns ms)

@[inline] def expandTacticMacro (evalTactic : Syntax → TacticM Unit) (stx : Syntax) : TacticM Unit := do
env ← getEnv;
let k        := stx.getKind;
let table    := (macroAttribute.ext.getState env).table;
let macroFns := (table.find? k).getD [];
expandTacticMacroFns evalTactic stx macroFns

partial def evalTactic : Syntax → TacticM Unit
| stx => withRef stx $ withIncRecDepth $ withFreshMacroScope $ match stx with
  | Syntax.node k args =>
    if k == nullKind then
      -- Macro writers create a sequence of tactics `t₁ ... tₙ` using `mkNullNode #[t₁, ..., tₙ]`
      stx.getArgs.forM evalTactic
    else do
      trace `Elab.step fun _ => stx;
      env ← getEnv;
      s ← saveAllState;
      let table := (tacticElabAttribute.ext.getState env).table;
      let k := stx.getKind;
      match table.find? k with
      | some evalFns => evalTacticUsing s stx evalFns
      | none         => expandTacticMacro evalTactic stx
  | _ => throwError "unexpected command"

/-- Adapt a syntax transformation to a regular tactic evaluator. -/
def adaptExpander (exp : Syntax → TacticM Syntax) : Tactic :=
fun stx => do
  stx' ← exp stx;
  withMacroExpansion stx stx' $ evalTactic stx'

def getGoals : TacticM (List MVarId) := do s ← get; pure s.goals
def setGoals (gs : List MVarId) : TacticM Unit := modify $ fun s => { s with goals := gs }
def appendGoals (gs : List MVarId) : TacticM Unit := modify $ fun s => { s with goals := s.goals ++ gs }
def pruneSolvedGoals : TacticM Unit := do
gs ← getGoals;
gs ← gs.filterM $ fun g => not <$> isExprMVarAssigned g;
setGoals gs
def getUnsolvedGoals : TacticM (List MVarId) := do pruneSolvedGoals; getGoals
def getMainGoal : TacticM (MVarId × List MVarId) := do (g::gs) ← getUnsolvedGoals | throwError "no goals to be solved"; pure (g, gs)
def getMainTag : TacticM Name := do
(g, _) ← getMainGoal;
mvarDecl ← getMVarDecl g;
pure mvarDecl.userName

def ensureHasNoMVars (e : Expr) : TacticM Unit := do
e ← instantiateMVars e;
pendingMVars ← getMVars e;
liftM $ Term.logUnassignedUsingErrorContext pendingMVars;
when e.hasExprMVar $ throwError ("tactic failed, resulting expression contains metavariables" ++ indentExpr e)

def withMainMVarContext {α} (x : TacticM α) : TacticM α := do
(mvarId, _) ← getMainGoal;
withMVarContext mvarId x

@[inline] def liftMetaMAtMain {α} (x : MVarId → MetaM α) : TacticM α := do
(g, _) ← getMainGoal;
withMVarContext g $ liftMetaM $ x g

@[inline] def liftMetaTacticAux {α} (tactic : MVarId → MetaM (α × List MVarId)) : TacticM α := do
(g, gs) ← getMainGoal;
withMVarContext g $ do
  (a, gs') ← liftMetaM $ tactic g;
  setGoals (gs' ++ gs);
  pure a

@[inline] def liftMetaTactic (tactic : MVarId → MetaM (List MVarId)) : TacticM Unit :=
liftMetaTacticAux (fun mvarId => do gs ← tactic mvarId; pure ((), gs))

def done : TacticM Unit := do
gs ← getUnsolvedGoals;
unless gs.isEmpty $ reportUnsolvedGoals gs

@[builtinTactic Lean.Parser.Tactic.«done»] def evalDone : Tactic :=
fun _ => done

def focusAux {α} (tactic : TacticM α) : TacticM α := do
(g, gs) ← getMainGoal;
setGoals [g];
a ← tactic;
gs' ← getGoals;
setGoals (gs' ++ gs);
pure a

def focus {α} (tactic : TacticM α) : TacticM α :=
focusAux (do a ← tactic; done; pure a)

def try? {α} (tactic : TacticM α) : TacticM (Option α) :=
catch (do a ← tactic; pure (some a)) (fun _ => pure none)

def try {α} (tactic : TacticM α) : TacticM Bool :=
catch (do tactic; pure true) (fun _ => pure false)

/--
  Use `parentTag` to tag untagged goals at `newGoals`.
  If there are multiple new untagged goals, they are named using `<parentTag>.<newSuffix>_<idx>` where `idx > 0`.
  If there is only one new untagged goal, then we just use `parentTag` -/
def tagUntaggedGoals (parentTag : Name) (newSuffix : Name) (newGoals : List MVarId) : TacticM Unit := do
mctx ← getMCtx;
let numAnonymous := newGoals.foldl (fun n g => if mctx.isAnonymousMVar g then n + 1 else n) 0;
modifyMCtx fun mctx =>
  let (mctx, _) := newGoals.foldl
    (fun (acc : MetavarContext × Nat) (g : MVarId) =>
       let (mctx, idx) := acc;
       if mctx.isAnonymousMVar g then
         if numAnonymous == 1 then
           (mctx.renameMVar g parentTag, idx+1)
         else
           (mctx.renameMVar g (parentTag ++ newSuffix.appendIndexAfter idx), idx+1)
       else
         acc)
    (mctx, 1);
  mctx

def evalSeq : Tactic :=
fun stx => (stx.getArg 0).forSepArgsM evalTactic

@[builtinTactic seq1] def evalSeq1 : Tactic := evalSeq

@[builtinTactic tacticSeq1Indented] def evalTacticSeq1Indented : Tactic := evalSeq

@[builtinTactic tacticSeqBracketed] def evalTacticSeqBracketed : Tactic :=
fun stx => withRef (stx.getArg 2) $ focus $ (stx.getArg 1).forSepArgsM evalTactic

@[builtinTactic Parser.Tactic.focus] def evalFocus : Tactic :=
fun stx => focus $ evalTactic (stx.getArg 1)

@[builtinTactic paren] def evalParen : Tactic :=
fun stx => evalSeq1 (stx.getArg 1)

@[builtinTactic tacticSeq] def evalTacticSeq : Tactic :=
fun stx => evalTactic (stx.getArg 0)

partial def evalChoiceAux (tactics : Array Syntax) : Nat → TacticM Unit
| i =>
  if h : i < tactics.size then
    let tactic := tactics.get ⟨i, h⟩;
    catchInternalId unsupportedSyntaxExceptionId
      (evalTactic tactic)
      (fun _ => evalChoiceAux (i+1))
  else
    throwUnsupportedSyntax

@[builtinTactic choice] def evalChoice : Tactic :=
fun stx => evalChoiceAux stx.getArgs 0

@[builtinTactic skip] def evalSkip : Tactic :=
fun stx => pure ()

@[builtinTactic failIfSuccess] def evalFailIfSuccess : Tactic :=
fun stx =>
  let tactic := stx.getArg 1;
  whenM
    (catch
      (do evalTactic tactic; pure true)
      (fun _ => pure false))
    (throwError ("tactic succeeded"))

@[builtinTactic traceState] def evalTraceState : Tactic :=
fun stx => do
  gs ← getUnsolvedGoals;
  logInfo (goalsToMessageData gs)

@[builtinTactic Lean.Parser.Tactic.assumption] def evalAssumption : Tactic :=
fun stx => liftMetaTactic $ fun mvarId => do Meta.assumption mvarId; pure []

private def introStep (n : Name) : TacticM Unit :=
liftMetaTactic $ fun mvarId => do (_, mvarId) ← Meta.intro mvarId n; pure [mvarId]

@[builtinTactic Lean.Parser.Tactic.intro] def evalIntro : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| intro)           => liftMetaTactic $ fun mvarId => do (_, mvarId) ← Meta.intro1 mvarId; pure [mvarId]
  | `(tactic| intro $h:ident)  => introStep h.getId
  | `(tactic| intro _)         => introStep `_
  | `(tactic| intro $pat:term) => do
    stxNew ← `(tactic| intro h; match h with | $pat:term => _; clear h);
    withMacroExpansion stx stxNew $ evalTactic stxNew
  | `(tactic| intro $hs:term*) => do
    let h0 := hs.get! 0;
    let hs := hs.extract 1 hs.size;
    stxNew ← `(tactic| intro $h0:term; intro $hs:term*);
    withMacroExpansion stx stxNew $ evalTactic stxNew
  | _ => throwUnsupportedSyntax

@[builtinTactic Lean.Parser.Tactic.introMatch] def evalIntroMatch : Tactic :=
fun stx => do
  let matchAlts := stx.getArg 1;
  stxNew ← liftMacroM $ Term.expandMatchAltsIntoMatchTactic stx matchAlts;
  withMacroExpansion stx stxNew $ evalTactic stxNew

private def getIntrosSize : Expr → Nat
| Expr.forallE _ _ b _ => getIntrosSize b + 1
| Expr.letE _ _ _ b _  => getIntrosSize b + 1
| _                    => 0

@[builtinTactic «intros»] def evalIntros : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| intros)       => liftMetaTactic $ fun mvarId => do
    type ← Meta.getMVarType mvarId;
    type ← instantiateMVars type;
    let n := getIntrosSize type;
    (_, mvarId) ← Meta.introN mvarId n;
    pure [mvarId]
  | `(tactic| intros $ids*) => liftMetaTactic $ fun mvarId => do
    (_, mvarId) ← Meta.introN mvarId ids.size (ids.map Syntax.getId).toList;
    pure [mvarId]
  | _                       => throwUnsupportedSyntax

def getFVarId (id : Syntax) : TacticM FVarId :=
withRef id do
fvar? ← liftTermElabM $ Term.isLocalIdent? id;
match fvar? with
| some fvar => pure fvar.fvarId!
| none      => throwError ("unknown variable '" ++ toString id.getId ++ "'")

def getFVarIds (ids : Array Syntax) : TacticM (Array FVarId) := do
withMainMVarContext $ ids.mapM getFVarId

@[builtinTactic Lean.Parser.Tactic.revert] def evalRevert : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| revert $hs*) => do
     (g, gs) ← getMainGoal;
     fvarIds ← getFVarIds hs;
     (_, g) ← liftMetaM $ Meta.revert g fvarIds;
     setGoals (g :: gs)
  | _                     => throwUnsupportedSyntax

/- Sort free variables using an order `x < y` iff `x` was defined after `y` -/
private def sortFVarIds (fvarIds : Array FVarId) : TacticM (Array FVarId) :=
withMainMVarContext do
  lctx ← getLCtx;
  pure $ fvarIds.qsort fun fvarId₁ fvarId₂ =>
    match lctx.find? fvarId₁, lctx.find? fvarId₂ with
    | some d₁, some d₂ => d₁.index > d₂.index
    | some _,  none    => false
    | none,    some _  => true
    | none,    none    => Name.quickLt fvarId₁ fvarId₂

@[builtinTactic Lean.Parser.Tactic.clear] def evalClear : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| clear $hs*) => do
    fvarIds ← getFVarIds hs;
    fvarIds ← sortFVarIds fvarIds;
    fvarIds.forM fun fvarId => do
      (g, gs) ← getMainGoal;
      withMVarContext g do
        g ← liftMetaM $ clear g fvarId;
        setGoals (g :: gs)
  | _ => throwUnsupportedSyntax

def forEachVar (hs : Array Syntax) (tac : MVarId → FVarId → MetaM MVarId) : TacticM Unit :=
hs.forM $ fun h => do
  (g, gs) ← getMainGoal;
  withMVarContext g do
    fvarId ← getFVarId h;
    g ← liftMetaM $ tac g fvarId;
    setGoals (g :: gs)

@[builtinTactic Lean.Parser.Tactic.subst] def evalSubst : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| subst $hs*) => forEachVar hs Meta.subst
  | _                     => throwUnsupportedSyntax

/--
  First method searches for a metavariable `g` s.t. `tag` is a suffix of its name.
  If none is found, then it searches for a metavariable `g` s.t. `tag` is a prefix of its name. -/
private def findTag? (gs : List MVarId) (tag : Name) : TacticM (Option MVarId) := do
g? ← gs.findM? (fun g => do mvarDecl ← getMVarDecl g; pure $ tag.isSuffixOf mvarDecl.userName);
match g? with
| some g => pure g
| none   => gs.findM? (fun g => do mvarDecl ← getMVarDecl g; pure $ tag.isPrefixOf mvarDecl.userName)

@[builtinTactic «case»] def evalCase : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| case $tag => $tac:tacticSeq) => do
     let tag := tag.getId;
     gs ← getUnsolvedGoals;
     some g ← findTag? gs tag | throwError "tag not found";
     let gs := gs.erase g;
     setGoals [g];
     savedTag ← liftM $ getMVarTag g;
     liftM $ setMVarTag g Name.anonymous;
     finally (evalTactic tac) (liftM $ setMVarTag g savedTag);
     done;
     setGoals gs
  | _ => throwUnsupportedSyntax

@[builtinTactic «orelse»] def evalOrelse : Tactic :=
fun stx => match_syntax stx with
  | `(tactic| $tac1 <|> $tac2) => evalTactic tac1 <|> evalTactic tac2
  | _                          => throwUnsupportedSyntax

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.tactic;
pure ()

@[inline] def TacticM.run {α} (x : TacticM α) (ctx : Context) (s : State) : TermElabM (α × State) :=
(x.run ctx).run s

@[inline] def TacticM.run' {α} (x : TacticM α) (ctx : Context) (s : State) : TermElabM α :=
Prod.fst <$> x.run ctx s

end Tactic
end Elab
end Lean
