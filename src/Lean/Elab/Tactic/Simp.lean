/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Location
import Lean.Meta.Tactic.Replace
import Lean.Elab.BuiltinNotation

namespace Lean.Elab.Tactic
open Meta

unsafe def evalSimpConfigUnsafe (e : Expr) : TermElabM Meta.Simp.Config :=
  Term.evalExpr Meta.Simp.Config ``Meta.Simp.Config e
@[implementedBy evalSimpConfigUnsafe] constant evalSimpConfig (e : Expr) : TermElabM Meta.Simp.Config

unsafe def evalSimpConfigCtxUnsafe (e : Expr) : TermElabM Meta.Simp.ConfigCtx :=
  Term.evalExpr Meta.Simp.ConfigCtx ``Meta.Simp.ConfigCtx e
@[implementedBy evalSimpConfigCtxUnsafe] constant evalSimpConfigCtx (e : Expr) : TermElabM Meta.Simp.ConfigCtx

/-
  `optConfig` is of the form `("(" "config" ":=" term ")")?`
  If `ctx == false`, the argument is assumed to have type `Meta.Simp.Config`, and `Meta.Simp.ConfigCtx` otherwise. -/
def elabSimpConfig (optConfig : Syntax) (ctx : Bool) : TermElabM Meta.Simp.Config := do
  if optConfig.isNone then
    if ctx then
      return { : Meta.Simp.ConfigCtx }.toConfig
    else
      return {}
  else
    withoutModifyingState <| withLCtx {} {} <| Term.withSynthesize do
      let c ← Term.elabTermEnsuringType optConfig[3] (Lean.mkConst (if ctx then ``Meta.Simp.ConfigCtx else ``Meta.Simp.Config))
      if ctx then
        return (← evalSimpConfigCtx (← instantiateMVars c)).toConfig
      else
        evalSimpConfig (← instantiateMVars c)

private def addDeclToUnfoldOrLemma (lemmas : Meta.SimpLemmas) (e : Expr) (post : Bool) : MetaM Meta.SimpLemmas := do
  if e.isConst then
    let declName := e.constName!
    let info ← getConstInfo declName
    if (← isProp info.type) then
      lemmas.addConst declName post
    else
      lemmas.addDeclToUnfold declName
  else
    lemmas.add #[] e post

private def addSimpLemma (lemmas : Meta.SimpLemmas) (stx : Syntax) (post : Bool) : TermElabM Meta.SimpLemmas := do
  let (levelParams, proof) ← Term.withoutModifyingElabMetaStateWithInfo <| withRef stx <| Term.withoutErrToSorry do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    let e := e.eta
    if e.hasMVar then
      let r ← abstractMVars e
      return (r.paramNames, r.expr)
    else
      return (#[], e)
  lemmas.add levelParams proof

/--
  Elaborate extra simp lemmas provided to `simp`. `stx` is of the `simpLemma,*`
  If `eraseLocal == true`, then we consider local declarations when resolving names for erased lemmas (`- id`),
  this option only makes sense for `simp_all`.
-/
private def elabSimpLemmas (stx : Syntax) (ctx : Simp.Context) (eraseLocal : Bool) : TacticM Simp.Context := do
  if stx.isNone then
    return ctx
  else
    /-
    syntax simpPre := "↓"
    syntax simpPost := "↑"
    syntax simpLemma := (simpPre <|> simpPost)? term

    syntax simpErase := "-" ident
    -/
    withMainContext do
      let mut lemmas := ctx.simpLemmas
      for arg in stx[1].getSepArgs do
        if arg.getKind == ``Lean.Parser.Tactic.simpErase then
          if eraseLocal && (← Term.isLocalIdent? arg[1]).isSome then
            -- We use `eraseCore` because the simp lemma for the hypothesis was not added yet
            lemmas ← lemmas.eraseCore arg[1].getId
          else
            let declName ← resolveGlobalConstNoOverloadWithInfo arg[1]
            lemmas ← lemmas.erase declName
        else
          let post :=
            if arg[0].isNone then
              true
            else
              arg[0][0].getKind == ``Parser.Tactic.simpPost
          match (← resolveSimpIdLemma? arg[1]) with
          | some e => lemmas ← addDeclToUnfoldOrLemma lemmas e post
          | _      => lemmas ← addSimpLemma lemmas arg[1] post
      return { ctx with simpLemmas := lemmas }
where
  resolveSimpIdLemma? (simpArgTerm : Syntax) : TacticM (Option Expr) := do
    if simpArgTerm.isIdent then
      try
        Term.resolveId? simpArgTerm (withInfo := true)
      catch _ =>
        return none
    else
      Term.elabCDotFunctionAlias? simpArgTerm

--  If `ctx == false`, the argument is assumed to have type `Meta.Simp.Config`, and `Meta.Simp.ConfigCtx` otherwise. -/
private def mkSimpContext (stx : Syntax) (eraseLocal : Bool) (ctx := false) : TacticM Simp.Context := do
  let simpOnly := !stx[2].isNone
  elabSimpLemmas stx[3] (eraseLocal := eraseLocal) {
    config      := (← elabSimpConfig stx[1] (ctx := ctx))
    simpLemmas  := if simpOnly then {} else (← getSimpLemmas)
    congrLemmas := (← getCongrLemmas)
  }

/-
  "simp " ("(" "config" ":=" term ")")? ("only ")? ("[" simpLemma,* "]")? (location)?
-/
@[builtinTactic Lean.Parser.Tactic.simp] def evalSimp : Tactic := fun stx => do
  let ctx  ← mkSimpContext stx (eraseLocal := false)
  -- trace[Meta.debug] "Lemmas {← toMessageData ctx.simpLemmas.post}"
  let loc := expandOptLocation stx[4]
  match loc with
  | Location.targets hUserNames simpTarget =>
    withMainContext do
      let fvarIds ← hUserNames.mapM fun hUserName => return (← getLocalDeclFromUserName hUserName).fvarId
      go ctx fvarIds simpTarget
  | Location.wildcard =>
    withMainContext do
      go ctx (← getNondepPropHyps (← getMainGoal)) true
where
  go (ctx : Simp.Context) (fvarIdsToSimp : Array FVarId) (simpType : Bool) : TacticM Unit := do
    let mut mvarId ← getMainGoal
    let mut toAssert : Array Hypothesis := #[]
    for fvarId in fvarIdsToSimp do
      let localDecl ← getLocalDecl fvarId
      let type ← instantiateMVars localDecl.type
      match (← simpStep mvarId (mkFVar fvarId) type ctx) with
      | none => replaceMainGoal []; return ()
      | some (value, type) => toAssert := toAssert.push { userName := localDecl.userName, type := type, value := value }
    if simpType then
      match (← simpTarget mvarId ctx) with
      | none => replaceMainGoal []; return ()
      | some mvarIdNew => mvarId := mvarIdNew
    let (_, mvarIdNew) ← assertHypotheses mvarId toAssert
    let mvarIdNew ← tryClearMany mvarIdNew fvarIdsToSimp
    replaceMainGoal [mvarIdNew]

@[builtinTactic Lean.Parser.Tactic.simpAll] def evalSimpAll : Tactic := fun stx => do
  let ctx  ← mkSimpContext stx (eraseLocal := true) (ctx := true)
  match (← simpAll (← getMainGoal) ctx) with
  | none => replaceMainGoal []
  | some mvarId => replaceMainGoal [mvarId]

end Lean.Elab.Tactic
