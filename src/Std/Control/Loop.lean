/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/

/-! Macros for partial loops in `do` blocks. -/

structure Loop

namespace Std.Loop

@[inline]
partial def Loop.forIn {β : Type u} {m : Type u → Type v} [Monad m] (loop : Loop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (b : β) : m β := do
    match ← f () b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop b
  loop init

instance : ForIn m Loop Unit where
  forIn := Loop.forIn

scoped macro "repeat " seq:doSeq : doElem =>
  `(doElem| for _ in Loop.mk do $seq)

scoped macro "while " cond:termBeforeDo " do " seq:doSeq : doElem =>
  `(doElem| repeat if $cond then $seq else break)

scoped macro "while " "let " pat:term " := " d:termBeforeDo " do " seq:doSeq : doElem =>
  `(doElem| repeat match $d:term with | $pat:term => $seq | _ => break)

end Std.Loop
