import Init.Lean

namespace Lean
open Lean.Elab

def run {α} [HasToString α] : Unhygienic α → String := toString ∘ Unhygienic.run

#eval run `(Nat.one)
#eval run `(1 + 1)
#eval run $ do a ← `(Nat.one); `(%%a)
#eval run $ do a ← `(Nat.one); `(f %%(id a))
#eval run `(`(hi))
#eval run `(`(%%a))
#eval run $ do a ← `(Nat.one); `(`(%%%%a))
#eval run $ do a ← `(1 + 2); match_syntax a with `(%%a + %%b) => `(%%b + %%a) | _ => pure Syntax.missing
#eval run $ do a ← `(aa); match_syntax a with `(%%id:id) => pure 0 | `(%%e) => pure 1 | _ => pure 2
#eval run $ do a ← `(1 + 2); match_syntax a with `(%%id:id) => pure 0 | `(%%e) => pure 1 | _ => pure 2
-- TODO
#eval run $ do a ← `(fun a b => c); match_syntax a with `(fun %%aa* => aa) => pure aa | _ => pure #[]

end Lean
