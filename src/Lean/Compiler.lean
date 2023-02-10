/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
private import Lean.Compiler.InlineAttrs
private import Lean.Compiler.Specialize
private import Lean.Compiler.ConstFolding
private import Lean.Compiler.ClosedTermCache
private import Lean.Compiler.ExternAttr
private import Lean.Compiler.ImplementedByAttr
private import Lean.Compiler.NeverExtractAttr
private import Lean.Compiler.IR
private import Lean.Compiler.CSimpAttr
private import Lean.Compiler.FFI
private import Lean.Compiler.NoncomputableAttr
private import Lean.Compiler.Main
private import Lean.Compiler.AtMostOnce -- TODO: delete after we port code generator to Lean
private import Lean.Compiler.Old -- TODO: delete after we port code generator to Lean
