/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
private import Lean.Meta.Basic
private import Lean.Meta.LevelDefEq
private import Lean.Meta.WHNF
private import Lean.Meta.InferType
private import Lean.Meta.FunInfo
private import Lean.Meta.ExprDefEq
private import Lean.Meta.DecLevel
private import Lean.Meta.DiscrTree
private import Lean.Meta.Reduce
private import Lean.Meta.Instances
private import Lean.Meta.AbstractMVars
private import Lean.Meta.SynthInstance
private import Lean.Meta.AppBuilder
private import Lean.Meta.Tactic
private import Lean.Meta.KAbstract
private import Lean.Meta.RecursorInfo
private import Lean.Meta.GeneralizeTelescope
private import Lean.Meta.Match
private import Lean.Meta.ReduceEval
private import Lean.Meta.Closure
private import Lean.Meta.AbstractNestedProofs
private import Lean.Meta.ForEachExpr
private import Lean.Meta.Transform
private import Lean.Meta.PPGoal
private import Lean.Meta.UnificationHint
private import Lean.Meta.Inductive
private import Lean.Meta.SizeOf
private import Lean.Meta.IndPredBelow
private import Lean.Meta.Coe
private import Lean.Meta.CollectFVars
private import Lean.Meta.GeneralizeVars
private import Lean.Meta.Injective
private import Lean.Meta.Structure
private import Lean.Meta.Constructions
private import Lean.Meta.CongrTheorems
private import Lean.Meta.Eqns
private import Lean.Meta.CasesOn
private import Lean.Meta.ExprLens
private import Lean.Meta.ExprTraverse
private import Lean.Meta.Eval
