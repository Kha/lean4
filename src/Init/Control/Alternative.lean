/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Core
import Init.Control.Applicative
universes u v

class Alternative (f : Type u → Type v) extends Applicative f : Type (max (u+1) v) :=
  (failure : {α : Type u} → f α)
  (orelse  : {α : Type u} → f α → f α → f α)

instance (f : Type u → Type v) (α : Type u) [Alternative f] : HasOrelse (f α) := ⟨Alternative.orelse⟩

variables {f : Type u → Type v} [Alternative f] {α : Type u}

export Alternative (failure)

@[inline] def guard {f : Type → Type v} [Alternative f] (p : Prop) [Decidable p] : f Unit :=
  if p then pure () else failure

@[inline] def assert {f : Type → Type v} [Alternative f] (p : Prop) [Decidable p] : f (Inhabited p) :=
  if h : p then pure ⟨h⟩ else failure

@[inline] def optional (x : f α) : f (Option α) :=
  some <$> x <|> pure none
