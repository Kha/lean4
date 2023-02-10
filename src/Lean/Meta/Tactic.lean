/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
private import Lean.Meta.Tactic.Intro
private import Lean.Meta.Tactic.Assumption
private import Lean.Meta.Tactic.Contradiction
private import Lean.Meta.Tactic.Apply
private import Lean.Meta.Tactic.Revert
private import Lean.Meta.Tactic.Clear
private import Lean.Meta.Tactic.Assert
private import Lean.Meta.Tactic.Rewrite
private import Lean.Meta.Tactic.Generalize
private import Lean.Meta.Tactic.Replace
private import Lean.Meta.Tactic.Induction
private import Lean.Meta.Tactic.Cases
private import Lean.Meta.Tactic.ElimInfo
private import Lean.Meta.Tactic.Delta
private import Lean.Meta.Tactic.Constructor
private import Lean.Meta.Tactic.Simp
private import Lean.Meta.Tactic.AuxLemma
private import Lean.Meta.Tactic.SplitIf
private import Lean.Meta.Tactic.Split
private import Lean.Meta.Tactic.Cleanup
private import Lean.Meta.Tactic.Unfold
private import Lean.Meta.Tactic.Rename
private import Lean.Meta.Tactic.LinearArith
private import Lean.Meta.Tactic.AC
private import Lean.Meta.Tactic.Refl
private import Lean.Meta.Tactic.Congr