/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.GlobalInstances
import Lean.Meta.Match.MatchPatternAttr

namespace Lean.Meta

def canUnfold (info : ConstantInfo) : MetaM Bool := do
  let ctx ← read
  match ctx.config.transparency with
  | .all => return true
  | .default => return !(← isIrreducible info.name)
  | m =>
    if (← isReducible info.name) then
      return true
    else if m == .instances && isGlobalInstance (← getEnv) info.name then
      return true
    else if !ctx.canUnfoldMatcher then
      return false
    else if hasMatchPatternAttribute (← getEnv) info.name then
      return true
    else
      return info.name == ``ite
       || info.name == ``dite
       || info.name == ``decEq
       || info.name == ``Nat.decEq
       || info.name == ``Char.ofNat   || info.name == ``Char.ofNatAux
       || info.name == ``String.decEq || info.name == ``List.hasDecEq
       || info.name == ``Fin.ofNat
       || info.name == ``UInt8.ofNat  || info.name == ``UInt8.decEq
       || info.name == ``UInt16.ofNat || info.name == ``UInt16.decEq
       || info.name == ``UInt32.ofNat || info.name == ``UInt32.decEq
       || info.name == ``UInt64.ofNat || info.name == ``UInt64.decEq
       /- Remark: we need to unfold the following two definitions because they are used for `Fin`, and
          lazy unfolding at `isDefEq` does not unfold projections.  -/
       || info.name == ``HMod.hMod || info.name == ``Mod.mod

/--
Look up a constant name, returning the `ConstantInfo`
if it should be unfolded at the current reducibility settings,
or `none` otherwise.

This is part of the implementation of `whnf`.
External users wanting to look up names should be using `Lean.getConstInfo`.
-/
def getUnfoldableConst? (constName : Name) : MetaM (Option ConstantInfo) := do
  match (← getEnv).find? constName with
  | some (info@(.thmInfo _))  => getTheoremInfo info
  | some (info@(.defnInfo _)) => if (← canUnfold info) then return info else return none
  | some info                 => return some info
  | none                      => throwUnknownConstant constName

/--
As with `getUnfoldableConst?` but return `none` instead of failing if the constant is not found.
-/
def getUnfoldableConstNoEx? (constName : Name) : MetaM (Option ConstantInfo) := do
  match (← getEnv).find? constName with
  | some (info@(.thmInfo _))  => getTheoremInfo info
  | some (info@(.defnInfo _)) => if (← canUnfold info) then return info else return none
  | some info                 => return some info
  | none                      => return none

end Meta
