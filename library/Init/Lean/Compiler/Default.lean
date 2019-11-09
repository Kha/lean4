/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import private Init.Lean.Compiler.InlineAttrs
import private Init.Lean.Compiler.Specialize
import private Init.Lean.Compiler.ConstFolding
import private Init.Lean.Compiler.ClosedTermCache
import private Init.Lean.Compiler.ExternAttr
import private Init.Lean.Compiler.ImplementedByAttr
import private Init.Lean.Compiler.NeverExtractAttr
import private Init.Lean.Compiler.IR
