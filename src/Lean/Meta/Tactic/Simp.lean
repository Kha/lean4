/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
private import Lean.Meta.Tactic.Simp.SimpTheorems
private import Lean.Meta.Tactic.Simp.SimpCongrTheorems
private import Lean.Meta.Tactic.Simp.Types
private import Lean.Meta.Tactic.Simp.Main
private import Lean.Meta.Tactic.Simp.Rewrite
private import Lean.Meta.Tactic.Simp.SimpAll

namespace Lean

builtin_initialize registerTraceClass `Meta.Tactic.simp
builtin_initialize registerTraceClass `Meta.Tactic.simp.congr (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.simp.discharge (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.simp.rewrite (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.simp.unify (inherited := true)
builtin_initialize registerTraceClass `Meta.Tactic.simp.numSteps
builtin_initialize registerTraceClass `Meta.Tactic.simp.heads
builtin_initialize registerTraceClass `Debug.Meta.Tactic.simp
builtin_initialize registerTraceClass `Debug.Meta.Tactic.simp.congr (inherited := true)

end Lean
