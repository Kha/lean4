/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam, Leonardo de Moura
-/
prelude
import private Init.Lean.Environment
import private Init.Lean.TypeClass.Synth

namespace Lean
namespace TypeClass

/- Entry point for the `#synth` command used for testing. -/
@[export lean_typeclass_synth_command]
def synthCommand (env : Environment) (goalType : Expr) : ExceptT String Id Expr :=
match (synth goalType).run { env := env } with
| EStateM.Result.ok val _    => pure val
| EStateM.Result.error msg _ => throw msg

end TypeClass
end Lean
