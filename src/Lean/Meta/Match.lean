/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
private import Lean.Meta.Match.MatchPatternAttr
private import Lean.Meta.Match.Match
private import Lean.Meta.Match.CaseValues
private import Lean.Meta.Match.CaseArraySizes
private import Lean.Meta.Match.MatchEqs

namespace Lean

builtin_initialize registerTraceClass `Meta.Match

end Lean
