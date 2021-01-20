/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Util.ForEachExpr
import Lean.Elab.Term
import Lean.Elab.Tactic.Basic

namespace Lean.Elab.Term
open Tactic (TacticM evalTactic getUnsolvedGoals)
open Meta

def liftTacticElabM {α} (mvarId : MVarId) (x : TacticM α) : TermElabM α :=
  withMVarContext mvarId do
    let s ← get
    let savedSyntheticMVars := s.syntheticMVars
    modify fun s => { s with syntheticMVars := [] }
    try
      x.run' { main := mvarId } { goals := [mvarId] }
    finally
      modify fun s => { s with syntheticMVars := savedSyntheticMVars }

def runTactic (mvarId : MVarId) (tacticCode : Syntax) : TermElabM Unit := do
  /- Recall, `tacticCode` is the whole `by ...` expression.
     We store the `by` because in the future we want to save the initial state information at the `by` position. -/
  let code := tacticCode[1]
  modifyThe Meta.State fun s => { s with mctx := s.mctx.instantiateMVarDeclMVars mvarId }
  let remainingGoals ← withInfoHole mvarId do liftTacticElabM mvarId do evalTactic code; getUnsolvedGoals
  unless remainingGoals.isEmpty do reportUnsolvedGoals remainingGoals

/-- Auxiliary function used to implement `synthesizeSyntheticMVars`. -/
private def resumeElabTerm (stx : Syntax) (expectedType? : Option Expr) (errToSorry := true) : TermElabM Expr :=
  -- Remark: if `ctx.errToSorry` is already false, then we don't enable it. Recall tactics disable `errToSorry`
  withReader (fun ctx => { ctx with errToSorry := ctx.errToSorry && errToSorry }) do
    elabTerm stx expectedType? false

/--
  Try to elaborate `stx` that was postponed by an elaboration method using `Expection.postpone`.
  It returns `true` if it succeeded, and `false` otherwise.
  It is used to implement `synthesizeSyntheticMVars`. -/
private def resumePostponed (macroStack : MacroStack) (declName? : Option Name) (stx : Syntax) (mvarId : MVarId) (postponeOnError : Bool) : TermElabM Bool :=
  withRef stx $ withMVarContext mvarId do
    let s ← get
    try
      withReader (fun ctx => { ctx with macroStack := macroStack, declName? := declName? }) do
        let mvarDecl     ← getMVarDecl mvarId
        let expectedType ← instantiateMVars mvarDecl.type
        withInfoHole mvarId do
          let result ← resumeElabTerm stx expectedType (!postponeOnError)
          /- We must ensure `result` has the expected type because it is the one expected by the method that postponed stx.
            That is, the method does not have an opportunity to check whether `result` has the expected type or not. -/
          let result ← withRef stx $ ensureHasType expectedType result
          assignExprMVar mvarId result
          pure true
    catch
     | ex@(Exception.internal id _) =>
       if id == postponeExceptionId then
         set s
         pure false
       else
         throw ex
     | ex@(Exception.error _ _) =>
       if postponeOnError then
         set s; pure false
       else
         logException ex
         pure true

/--
  Similar to `synthesizeInstMVarCore`, but makes sure that `instMVar` local context and instances
  are used. It also logs any error message produced. -/
private def synthesizePendingInstMVar (instMVar : MVarId) : TermElabM Bool :=
  withMVarContext instMVar do
    try
      synthesizeInstMVarCore instMVar
    catch
      | ex@(Exception.error _ _) => logException ex; pure true
      | _                        => unreachable!

/--
  Similar to `synthesizePendingInstMVar`, but generates type mismatch error message. -/
private def synthesizePendingCoeInstMVar
    (instMVar : MVarId) (errorMsgHeader? : Option String) (expectedType : Expr) (eType : Expr) (e : Expr) (f? : Option Expr) : TermElabM Bool :=
  withMVarContext instMVar do
    try
      synthesizeCoeInstMVarCore instMVar
    catch
      | Exception.error _ msg => throwTypeMismatchError errorMsgHeader? expectedType eType e f? msg
      | _                     => unreachable!

/-- Try to synthesize the given pending synthetic metavariable. -/
private def synthesizeSyntheticMVar (mvarSyntheticDecl : SyntheticMVarDecl) (postponeOnError : Bool) (runTactics : Bool) : TermElabM Bool :=
  withRef mvarSyntheticDecl.stx do
  match mvarSyntheticDecl.kind with
  | SyntheticMVarKind.typeClass                           => synthesizePendingInstMVar mvarSyntheticDecl.mvarId
  | SyntheticMVarKind.coe header? expectedType eType e f? => synthesizePendingCoeInstMVar mvarSyntheticDecl.mvarId header? expectedType eType e f?
  -- NOTE: actual processing at `synthesizeSyntheticMVarsAux`
  | SyntheticMVarKind.postponed macroStack declName?      => resumePostponed macroStack declName? mvarSyntheticDecl.stx mvarSyntheticDecl.mvarId postponeOnError
  | SyntheticMVarKind.tactic declName? tacticCode         =>
    withReader (fun ctx => { ctx with declName? := declName? }) do
      if runTactics then
        runTactic mvarSyntheticDecl.mvarId tacticCode
        pure true
      else
        pure false

/--
  Try to synthesize the current list of pending synthetic metavariables.
  Return `true` if at least one of them was synthesized. -/
private def synthesizeSyntheticMVarsStep (postponeOnError : Bool) (runTactics : Bool) : TermElabM Bool := do
  let ctx ← read
  traceAtCmdPos `Elab.resuming fun _ =>
    m!"resuming synthetic metavariables, mayPostpone: {ctx.mayPostpone}, postponeOnError: {postponeOnError}"
  let s ← get
  let syntheticMVars    := s.syntheticMVars
  let numSyntheticMVars := syntheticMVars.length
  -- We reset `syntheticMVars` because new synthetic metavariables may be created by `synthesizeSyntheticMVar`.
  modify fun s => { s with syntheticMVars := [] }
  -- Recall that `syntheticMVars` is a list where head is the most recent pending synthetic metavariable.
  -- We use `filterRevM` instead of `filterM` to make sure we process the synthetic metavariables using the order they were created.
  -- It would not be incorrect to use `filterM`.
  let remainingSyntheticMVars ← syntheticMVars.filterRevM fun mvarDecl => do
     -- We use `traceM` because we want to make sure the metavar local context is used to trace the message
     traceM `Elab.postpone (withMVarContext mvarDecl.mvarId do addMessageContext m!"resuming {mkMVar mvarDecl.mvarId}")
     let succeeded ← synthesizeSyntheticMVar mvarDecl postponeOnError runTactics
     trace[Elab.postpone]! if succeeded then fmt "succeeded" else fmt "not ready yet"
     pure !succeeded
  -- Merge new synthetic metavariables with `remainingSyntheticMVars`, i.e., metavariables that still couldn't be synthesized
  modify fun s => { s with syntheticMVars := s.syntheticMVars ++ remainingSyntheticMVars }
  pure $ numSyntheticMVars != remainingSyntheticMVars.length

private def tryToSynthesizeUsingDefaultInstance (mvarId : MVarId) (defaultInstance : Name) : MetaM (Option (List SyntheticMVarDecl)) :=
  commitWhenSome? do
    let constInfo ← getConstInfo defaultInstance
    let candidate := Lean.mkConst defaultInstance (← mkFreshLevelMVars constInfo.lparams.length)
    let (mvars, bis, _) ← forallMetaTelescopeReducing (← inferType candidate)
    let candidate := mkAppN candidate mvars
    trace[Elab.resume]! "trying default instance for {mkMVar mvarId} := {candidate}"
    if (← isDefEqGuarded (mkMVar mvarId) candidate) then
      -- Succeeded. Collect new TC problems
      let mut result := []
      for i in [:bis.size] do
        if bis[i] == BinderInfo.instImplicit then
           result := { mvarId := mvars[i].mvarId!, stx := (← getRef), kind := SyntheticMVarKind.typeClass } :: result
      trace[Elab.resume]! "worked"
      return some result
    else
      return none

private def tryToSynthesizeUsingDefaultInstances (mvarId : MVarId) (prio : Nat) : MetaM (Option (List SyntheticMVarDecl)) :=
  withMVarContext mvarId do
    let mvarType := (← Meta.getMVarDecl mvarId).type
    match (← isClass? mvarType) with
    | none => return none
    | some className =>
      match (← getDefaultInstances className) with
      | [] => return none
      | defaultInstances =>
        for (defaultInstance, instPrio) in defaultInstances do
          if instPrio == prio then
            match (← tryToSynthesizeUsingDefaultInstance mvarId defaultInstance) with
            | some newMVarDecls => return some newMVarDecls
            | none => continue
        return none

/- Used to implement `synthesizeUsingDefault`. This method only consider default instances with the given priority. -/
private def synthesizeUsingDefaultPrio (prio : Nat) : TermElabM Bool := do
  let rec visit (syntheticMVars : List SyntheticMVarDecl) (syntheticMVarsNew : List SyntheticMVarDecl) : TermElabM Bool := do
    match syntheticMVars with
    | [] => return false
    | mvarDecl :: mvarDecls =>
      match mvarDecl.kind with
      | SyntheticMVarKind.typeClass =>
        match (← withRef mvarDecl.stx <| tryToSynthesizeUsingDefaultInstances mvarDecl.mvarId prio) with
        | none => visit mvarDecls (mvarDecl :: syntheticMVarsNew)
        | some newMVarDecls =>
          let syntheticMVarsNew := newMVarDecls ++ syntheticMVarsNew
          let syntheticMVarsNew := mvarDecls.reverse ++ syntheticMVarsNew
          modify fun s => { s with syntheticMVars := syntheticMVarsNew }
          return true
      | _ => visit mvarDecls (mvarDecl :: syntheticMVarsNew)
  /- Recall that s.syntheticMVars is essentially a stack. The first metavariable was the last one created.
     We want to apply the default instance in reverse creation order. Otherwise,
     `toString 0` will produce a `OfNat String _` cannot be synthesized error. -/
  visit (← get).syntheticMVars.reverse []

/--
  Apply default value to any pending synthetic metavariable of kind `SyntheticMVarKind.withDefault`
  Return true if something was synthesized. -/
private def synthesizeUsingDefault : TermElabM Bool := do
  let prioSet ← getDefaultInstancesPriorities
  /- Recall that `prioSet` is stored in descending order -/
  for prio in prioSet do
    if (← synthesizeUsingDefaultPrio prio) then
      return true
  return false

/-- Report an error for each synthetic metavariable that could not be resolved. -/
private def reportStuckSyntheticMVars : TermElabM Unit := do
  let s ← get
  for mvarSyntheticDecl in s.syntheticMVars do
    withRef mvarSyntheticDecl.stx do
    match mvarSyntheticDecl.kind with
    | SyntheticMVarKind.typeClass =>
      withMVarContext mvarSyntheticDecl.mvarId do
        let mvarDecl ← getMVarDecl mvarSyntheticDecl.mvarId
        unless (← get).messages.hasErrors do
          logError <| "typeclass instance problem contains metavariables" ++ indentExpr mvarDecl.type
    | SyntheticMVarKind.coe header expectedType eType e f? =>
      withMVarContext mvarSyntheticDecl.mvarId do
        let mvarDecl ← getMVarDecl mvarSyntheticDecl.mvarId
        throwTypeMismatchError header expectedType eType e f? (some ("failed to create type class instance for " ++ indentExpr mvarDecl.type))
    | _ => unreachable! -- TODO handle other cases.

private def getSomeSynthethicMVarsRef : TermElabM Syntax := do
  let s ← get
  match s.syntheticMVars.find? $ fun (mvarDecl : SyntheticMVarDecl) => !mvarDecl.stx.getPos?.isNone with
  | some mvarDecl => pure mvarDecl.stx
  | none          => pure Syntax.missing

/--
  Try to process pending synthetic metavariables. If `mayPostpone == false`,
  then `syntheticMVars` is `[]` after executing this method.

  It keeps executing `synthesizeSyntheticMVarsStep` while progress is being made.
  If `mayPostpone == false`, then it applies default instances to `SyntheticMVarKind.typeClass` (if available)
  metavariables that are still unresolved, and then tries to resolve metavariables
  with `mayPostpone == false`. That is, we force them to produce error messages and/or commit to
  a "best option". If, after that, we still haven't made progress, we report "stuck" errors. -/
partial def synthesizeSyntheticMVars (mayPostpone := true) : TermElabM Unit :=
  let rec loop (u : Unit) : TermElabM Unit := do
    let ref ← getSomeSynthethicMVarsRef
    withRef ref <| withIncRecDepth do
      let s ← get
      unless s.syntheticMVars.isEmpty do
        if ← synthesizeSyntheticMVarsStep false false then
          loop ()
        else if !mayPostpone then
          /- Resume pending metavariables with "elaboration postponement" disabled.
             We postpone elaboration errors in this step by setting `postponeOnError := true`.
             Example:
             ```
             #check let x := ⟨1, 2⟩; Prod.fst x
             ```
             The term `⟨1, 2⟩` can't be elaborated because the expected type is not know.
             The `x` at `Prod.fst x` is not elaborated because the type of `x` is not known.
             When we execute the following step with "elaboration postponement" disabled,
             the elaborator fails at `⟨1, 2⟩` and postpones it, and succeeds at `x` and learns
             that its type must be of the form `Prod ?α ?β`.

             Recall that we postponed `x` at `Prod.fst x` because its type it is not known.
             We the type of `x` may learn later its type and it may contain implicit and/or auto arguments.
             By disabling postponement, we are essentially giving up the opportunity of learning `x`s type
             and assume it does not have implict and/or auto arguments. -/
          if ← withoutPostponing (synthesizeSyntheticMVarsStep true  false) then
            loop ()
          else if ← synthesizeUsingDefault then
            loop ()
          else if ← withoutPostponing (synthesizeSyntheticMVarsStep false false) then
            loop ()
          else if ← synthesizeSyntheticMVarsStep false true then
            loop ()
          else
            reportStuckSyntheticMVars
  loop ()

def synthesizeSyntheticMVarsNoPostponing : TermElabM Unit :=
  synthesizeSyntheticMVars (mayPostpone := false)

/- Keep invoking `synthesizeUsingDefault` until it returns false. -/
private partial def synthesizeUsingDefaultLoop : TermElabM Unit := do
  if (← synthesizeUsingDefault) then
    synthesizeSyntheticMVars (mayPostpone := true)
    synthesizeUsingDefaultLoop

def synthesizeSyntheticMVarsUsingDefault : TermElabM Unit := do
  synthesizeSyntheticMVars (mayPostpone := true)
  synthesizeUsingDefaultLoop

/--
  Execute `k`, and synthesize pending synthetic metavariables created while executing `k` are solved.
  If `mayPostpone == false`, then all of them must be synthesized.
  Remark: even if `mayPostpone == true`, the method still uses `synthesizeUsingDefault` -/
partial def withSynthesize {α} (k : TermElabM α) (mayPostpone := false) : TermElabM α := do
  let s ← get
  let syntheticMVarsSaved := s.syntheticMVars
  modify fun s => { s with syntheticMVars := [] }
  try
    let a ← k
    synthesizeSyntheticMVars mayPostpone
    if mayPostpone then
      synthesizeUsingDefaultLoop
    pure a
  finally
    modify fun s => { s with syntheticMVars := s.syntheticMVars ++ syntheticMVarsSaved }

/-- Elaborate `stx`, and make sure all pending synthetic metavariables created while elaborating `stx` are solved. -/
def elabTermAndSynthesize (stx : Syntax) (expectedType? : Option Expr) : TermElabM Expr :=
  withRef stx do
    let v ← withSynthesize $ elabTerm stx expectedType?
    instantiateMVars v

end Lean.Elab.Term
