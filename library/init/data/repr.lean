/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.string.basic init.data.bool.basic init.data.subtype.basic
import init.data.unsigned.basic init.data.prod init.data.sum.basic init.data.nat.div
open sum subtype nat

universes u v

class has_repr (α : Type u) :=
(repr : α → string)

def repr {α : Type u} [has_repr α] : α → string :=
has_repr.repr

instance : has_repr bool :=
⟨λ b, cond b "tt" "ff"⟩

instance {p : Prop} : has_repr (decidable p) :=
-- Remark: type class inference will not consider local instance `b` in the new elaborator
⟨λ b : decidable p, @ite p b _ "tt" "ff"⟩

protected def list.repr_aux {α : Type u} [has_repr α] : bool → list α → string
| b  []      := ""
| tt (x::xs) := repr x ++ list.repr_aux ff xs
| ff (x::xs) := ", " ++ repr x ++ list.repr_aux ff xs

protected def list.repr {α : Type u} [has_repr α] : list α → string
| []      := "[]"
| (x::xs) := "[" ++ list.repr_aux tt (x::xs) ++ "]"

instance {α : Type u} [has_repr α] : has_repr (list α) :=
⟨list.repr⟩

instance : has_repr unit :=
⟨λ u, "star"⟩

instance {α : Type u} [has_repr α] : has_repr (option α) :=
⟨λ o, match o with | none := "none" | (some a) := "(some " ++ repr a ++ ")" end⟩

instance {α : Type u} {β : Type v} [has_repr α] [has_repr β] : has_repr (α ⊕ β) :=
⟨λ s, match s with | (inl a) := "(inl " ++ repr a ++ ")" | (inr b) := "(inr " ++ repr b ++ ")" end⟩

instance {α : Type u} {β : Type v} [has_repr α] [has_repr β] : has_repr (α × β) :=
⟨λ ⟨a, b⟩, "(" ++ repr a ++ ", " ++ repr b ++ ")"⟩

instance {α : Type u} {β : α → Type v} [has_repr α] [s : ∀ x, has_repr (β x)] : has_repr (sigma β) :=
⟨λ ⟨a, b⟩, "⟨"  ++ repr a ++ ", " ++ repr b ++ "⟩"⟩

instance {α : Type u} {p : α → Prop} [has_repr α] : has_repr (subtype p) :=
⟨λ s, repr (val s)⟩

namespace nat

def digit_char (n : ℕ) : char :=
if n = 0 then '0' else
if n = 1 then '1' else
if n = 2 then '2' else
if n = 3 then '3' else
if n = 4 then '4' else
if n = 5 then '5' else
if n = 6 then '6' else
if n = 7 then '7' else
if n = 8 then '8' else
if n = 9 then '9' else
if n = 0xa then 'a' else
if n = 0xb then 'b' else
if n = 0xc then 'c' else
if n = 0xd then 'd' else
if n = 0xe then 'e' else
if n = 0xf then 'f' else
'*'

private def to_string_aux (base : ℕ) : ℕ → ℕ → string
| _         0 := ""
| 0         _ := ""
| (steps+1) n := (to_string_aux steps (n / base)).push $ digit_char (n % base)

protected def to_string : Π (n : ℕ) (base : opt_param ℕ 10), string
| 0 _ := "0"
| n base := to_string_aux base n n

protected def repr (n : ℕ) : string := n.to_string

end nat

instance : has_repr nat :=
⟨nat.repr⟩

def char_to_hex (c : char) : string :=
let hex := c.to_nat.to_string 16 in
(list.repeat '0' (4 - hex.length)).as_string ++ hex

def char.quote_core (c : char) : string :=
if       c = '\n' then "\\n"
else if  c = '\t' then "\\t"
else if  c = '\\' then "\\\\"
else if  c = '\"' then "\\\""
else if  32 <= c.to_nat ∧ c.to_nat <= 126 then string.singleton c
else "\\u" ++ char_to_hex c

instance : has_repr char :=
⟨λ c, "'" ++ char.quote_core c ++ "'"⟩

def string.quote_aux : list char → string
| []      := ""
| (x::xs) := char.quote_core x ++ string.quote_aux xs

def string.quote (s : string) : string :=
if s.is_empty = tt then "\"\""
else "\"" ++ string.quote_aux s.to_list ++ "\""

instance : has_repr string :=
⟨string.quote⟩

instance (n : nat) : has_repr (fin n) :=
⟨λ f, repr (fin.val f)⟩

instance : has_repr unsigned :=
⟨λ n, repr (fin.val n)⟩

def char.repr (c : char) : string :=
repr c
