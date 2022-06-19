/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.InternalExceptionId
import Lean.KeyedDeclsAttribute

namespace Lean
namespace PrettyPrinter

/- Auxiliary internal exception for backtracking the pretty printer.
   See `orelse.parenthesizer` for example -/
builtin_initialize backtrackExceptionId : InternalExceptionId ← registerInternalExceptionId `backtrackFormatter

def runForNodeKind {α} (attr : KeyedDeclsAttribute α) (k : SyntaxNodeKind) : CoreM α := do
  match attr.getValues (← getEnv) k with
  | p::_ => pure p
  | _    => throwError "no declaration of attribute [{attr.defn.name}] found for '{k}'"

end PrettyPrinter
end Lean
