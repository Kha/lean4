class Eq (α : Type) :=
(eq : α → α → Prop := λ a b, ¬ne a b)
(ne : α → α → Prop := λ a b, ¬eq a b)

set_option pp.all true
#check ({eq := (=)} : Eq ℕ)
#check ({ne := (≠)} : Eq ℕ)
