/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.Options

namespace Lean

def getMaxRecDepth (opts : Options) : Nat :=
opts.getNat `maxRecDepth defaultMaxRecDepth

@[init] def maxRecDepth : IO Unit :=
registerOption `maxRecDepth { defValue := defaultMaxRecDepth, group := "", descr := "maximum recursion depth for many Lean procedures" }

end Lean
