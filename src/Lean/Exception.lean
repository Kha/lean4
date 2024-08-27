/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Message
import Lean.InternalExceptionId
import Lean.Data.Options
import Lean.Util.MonadCache

namespace Lean

/-- Exception type used in most Lean monads -/
inductive Exception where
  /-- Error messages that are displayed to users. `ref` is used to provide position information. -/
  | error (ref : Syntax) (msg : MessageData)
  /--
  Internal exceptions that are not meant to be seen by users.
  Examples: "postpone elaboration", "stuck at universe constraint", etc.
  -/
  | internal (id : InternalExceptionId) (extra : KVMap := {})

/-- Convert exception into a structured message. -/
def Exception.toMessageData : Exception → MessageData
  | .error _ msg   => msg
  | .internal id _ => id.toString

def Exception.hasSyntheticSorry : Exception → Bool
  | Exception.error _ msg => msg.hasSyntheticSorry
  | _                     => false

/--
Return syntax object providing position information for the exception.
Recall that internal exceptions do not have position information.
-/
def Exception.getRef : Exception → Syntax
  | .error ref _  => ref
  | .internal _ _ => Syntax.missing

instance : Inhabited Exception := ⟨Exception.error default default⟩

/-- Similar to `AddMessageContext`, but for error messages.
   The default instance just uses `AddMessageContext`.
   In error messages, we may want to provide additional information (e.g., macro expansion stack),
   and refine the `(ref : Syntax)`. -/
class AddErrorMessageContext (m : Type → Type) where
  add : Syntax → MessageData → m (Syntax × MessageData)

instance (m : Type → Type) [AddMessageContext m] [Monad m] : AddErrorMessageContext m where
  add ref msg := do
    let msg ← addMessageContext msg
    pure (ref, msg)

class abbrev MonadError (m : Type → Type) :=
  MonadExceptOf Exception m
  MonadRef m
  AddErrorMessageContext m

section Methods

/--
Throw an error exception using the given message data.
The result of `getRef` is used as position information.
Recall that `getRef` returns the current "reference" syntax.
-/
protected def throwError [Monad m] [MonadError m] (msg : MessageData) : m α := do
  let ref ← getRef
  let (ref, msg) ← AddErrorMessageContext.add ref msg
  throw <| Exception.error ref msg

/-- Throw an unknown constant error message. -/
def throwUnknownConstant [Monad m] [MonadError m] (constName : Name) : m α :=
  Lean.throwError m!"unknown constant '{mkConst constName}'"

/-- Throw an error exception using the given message data and reference syntax. -/
protected def throwErrorAt [Monad m] [MonadError m] (ref : Syntax) (msg : MessageData) : m α := do
  withRef ref <| Lean.throwError msg

/--
Convert an `Except` into a `m` monadic action, where `m` is any monad that
implements `MonadError`.
-/
def ofExcept [Monad m] [MonadError m] [ToString ε] (x : Except ε α) : m α :=
  match x with
  | .ok a    => return a
  | .error e => Lean.throwError <| toString e

/--
Throw an error exception for the given kernel exception.
-/
def throwKernelException [Monad m] [MonadError m] [MonadEnv m] [MonadOptions m] (ex : Kernel.Exception) : m α := do
  Lean.throwError <| ex.toMessageData (← getEnv) (← getOptions)

/-- Lift from `Except Kernel.Exception` to `m` when `m` can throw kernel exceptions. -/
def ofExceptKernelException [Monad m] [MonadError m] [MonadEnv m] [MonadOptions m] (x : Except Kernel.Exception α) : m α :=
  match x with
  | .ok a    => return a
  | .error e => throwKernelException e

end Methods

class MonadRecDepth (m : Type → Type) where
  withRecDepth {α} : Nat → m α → m α
  getRecDepth      : m Nat
  getMaxRecDepth   : m Nat

instance [MonadRecDepth m] : MonadRecDepth (ReaderT ρ m) where
  withRecDepth d x := fun ctx => MonadRecDepth.withRecDepth d (x ctx)
  getRecDepth      := fun _ => MonadRecDepth.getRecDepth
  getMaxRecDepth   := fun _ => MonadRecDepth.getMaxRecDepth

instance [Monad m] [MonadRecDepth m] : MonadRecDepth (StateRefT' ω σ m) :=
  inferInstanceAs (MonadRecDepth (ReaderT _ _))

instance [BEq α] [Hashable α] [Monad m] [STWorld ω m] [MonadRecDepth m] : MonadRecDepth (MonadCacheT α β m) :=
  inferInstanceAs (MonadRecDepth (StateRefT' _ _ _))

/--
Throw a "maximum recursion depth has been reached" exception using the given reference syntax.
-/
def throwMaxRecDepthAt [MonadError m] (ref : Syntax) : m α :=
  throw <| .error ref (MessageData.ofFormat (Std.Format.text maxRecDepthErrorMessage))

/--
Return true if `ex` was generated by `throwMaxRecDepthAt`.
This function is a bit hackish. The max rec depth exception should probably be an internal exception,
but it is also produced by `MacroM` which implemented in the prelude, and internal exceptions have not
been defined yet.
-/
def Exception.isMaxRecDepth (ex : Exception) : Bool :=
  match ex with
  | error _ (MessageData.ofFormatWithInfos ⟨Std.Format.text msg, _⟩) => msg == maxRecDepthErrorMessage
  | _ => false

/--
Increment the current recursion depth and then execute `x`.
Throw an exception if maximum recursion depth has been reached.
We use this combinator to prevent stack overflows.
-/
@[inline] def withIncRecDepth [Monad m] [MonadError m] [MonadRecDepth m] (x : m α) : m α := do
  let curr ← MonadRecDepth.getRecDepth
  let max  ← MonadRecDepth.getMaxRecDepth
  if curr == max then
    throwMaxRecDepthAt (← getRef)
  else
    MonadRecDepth.withRecDepth (curr+1) x

/--
Macro for throwing error exceptions. The argument can be an interpolated string.
It is a convenient way of building `MessageData` objects.
The result of `getRef` is used as position information.
Recall that `getRef` returns the current "reference" syntax.
-/
syntax "throwError " (interpolatedStr(term) <|> term) : term
/--
Macro for throwing error exceptions. The argument can be an interpolated string.
It is a convenient way of building `MessageData` objects.
The first argument must be a `Syntax` that provides position information for
the error message.
`throwErrorAt ref msg` is equivalent to `withRef ref <| throwError msg`
-/
syntax "throwErrorAt " term:max ppSpace (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwError $msg:interpolatedStr) => `(Lean.throwError (m! $msg))
  | `(throwError $msg:term)            => `(Lean.throwError $msg)

macro_rules
  | `(throwErrorAt $ref $msg:interpolatedStr) => `(Lean.throwErrorAt $ref (m! $msg))
  | `(throwErrorAt $ref $msg:term)            => `(Lean.throwErrorAt $ref $msg)

end Lean
