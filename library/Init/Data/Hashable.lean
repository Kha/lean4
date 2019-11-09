/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import private Init.Data.UInt
import private Init.Data.String
universes u

class Hashable (α : Type u) :=
(hash : α → USize)

export Hashable (hash)

@[extern "lean_usize_mix_hash"]
constant mixHash (u₁ u₂ : USize) : USize := arbitrary _

@[extern "lean_string_hash"]
protected constant String.hash (s : String) : USize := arbitrary _
instance : Hashable String := ⟨String.hash⟩

protected def Nat.hash (n : Nat) : USize :=
USize.ofNat n

instance : Hashable Nat := ⟨Nat.hash⟩

instance {α β} [Hashable α] [Hashable β] : Hashable (α × β) :=
⟨fun ⟨a, b⟩ => mixHash (hash a) (hash b)⟩
