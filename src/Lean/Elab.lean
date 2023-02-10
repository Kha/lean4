/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
private import Lean.Elab.Import
private import Lean.Elab.Exception
private import Lean.Elab.Config
private import Lean.Elab.Command
private import Lean.Elab.Term
private import Lean.Elab.App
private import Lean.Elab.Binders
private import Lean.Elab.LetRec
private import Lean.Elab.Frontend
private import Lean.Elab.BuiltinNotation
private import Lean.Elab.Declaration
private import Lean.Elab.Tactic
private import Lean.Elab.Match
-- HACK: must come after `Match` because builtin elaborators (for `match` in this case) do not take priorities
private import Lean.Elab.Quotation
private import Lean.Elab.Syntax
private import Lean.Elab.Do
private import Lean.Elab.StructInst
private import Lean.Elab.Inductive
private import Lean.Elab.Structure
private import Lean.Elab.Print
private import Lean.Elab.MutualDef
private import Lean.Elab.AuxDef
private import Lean.Elab.PreDefinition
private import Lean.Elab.Deriving
private import Lean.Elab.DeclarationRange
private import Lean.Elab.Extra
private import Lean.Elab.GenInjective
private import Lean.Elab.BuiltinTerm
private import Lean.Elab.Arg
private import Lean.Elab.PatternVar
private import Lean.Elab.ElabRules
private import Lean.Elab.Macro
private import Lean.Elab.Notation
private import Lean.Elab.Mixfix
private import Lean.Elab.MacroRules
private import Lean.Elab.BuiltinCommand
private import Lean.Elab.RecAppSyntax
private import Lean.Elab.Eval
private import Lean.Elab.Calc
private import Lean.Elab.InheritDoc
private import Lean.Elab.ParseImportsFast
