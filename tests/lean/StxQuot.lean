import Lean

open Lean
open Lean.Elab

def run {α} [ToString α] : Unhygienic α → String := toString ∘ Unhygienic.run

#eval run `(Nat.one)
#eval run `($Syntax.missing)
namespace Lean.Syntax
#eval run `($missing)
#eval run `($(missing))
#eval run `($(id Syntax.missing) + 1)
#eval run $ let id := Syntax.missing; `($id + 1)
end Lean.Syntax
#eval run `(1 + 1)
#eval run $ `(fun a => a) >>= pure
#eval run $ `(def foo := 1)
#eval run $ `(def foo := 1 def bar := 2)
#eval run $ do let a ← `(Nat.one); `($a)
#eval run $ do `($(← `(Nat.one)))
#eval run $ do let a ← `(Nat.one); `(f $a $a)
#eval run $ do let a ← `(Nat.one); `(f $ f $a 1)
#eval run $ do let a ← `(Nat.one); `(f $(id a))
#eval run $ do let a ← `(Nat.one); `($(a).b)
#eval run $ do let a ← `(1 + 2); match a with | `($a + $b) => `($b + $a) | _ => pure Syntax.missing
#eval run $ do let a ← `(1 + 2); match a with | stx@`($a + $b) => `($stx + $a) | _ => pure Syntax.missing
#eval run $ do let a ← `(def foo := 1); match a with | `($f:command) => pure f | _ => pure Syntax.missing
#eval run $ do let a ← `(def foo := 1 def bar := 2); match a with | `($f:command $g:command) => `($g:command $f:command) | _ => pure Syntax.missing

#eval run $ do let a ← `(aa); match a with | `($id:ident) => pure 0 | `($e) => pure 1 | _ => pure 2
#eval run $ do let a ← `(1 + 2); match a with | `($id:ident) => pure 0 | `($e) => pure 1 | _ => pure 2
#eval run $ do let params ← #[`(a), `((b : Nat))].mapM id; `(fun $params* => 1)
#eval run $ do let a ← `(fun (a : Nat) b => c); match a with | `(fun $aa* => $e) => pure aa | _ => pure #[]
#eval run $ do let a ← `(∀ a, c); match a with | `(∀ $id:ident, $e) => pure id | _ => pure a
#eval run $ do let a ← `(∀ _, c); match a with | `(∀ $id:ident, $e) => pure id | _ => pure a
-- this one should NOT check the kind of the matched node
#eval run $ do let a ← `(∀ _, c); match a with | `(∀ $a, $e) => pure a | _ => pure a
#eval run $ do let a ← `(a); match a with | `($id:ident) => pure id | _ => pure a
#eval run $ do let a ← `(a.{0}); match a with | `($id:ident) => pure id | _ => pure a
#eval run $ do let a ← `(match a with | a => 1 | _ => 2); match a with | `(match $e with $eqns:matchAlt*) => pure eqns | _ => pure #[]

def f (stx : Syntax) : Unhygienic Syntax := match stx with
  | `({ a := a $[: $a]?}) => `({ a := a $[: $(id a)]?})
  | _ => unreachable!
#eval run do f (← `({ a := a : a }))
#eval run do f (← `({ a := a }))

def f' (stx : Syntax) : Unhygienic Syntax := match stx with
  | `(section $(id?)?) => `(section $(id?)?)
  | _ => unreachable!
#eval run do f' (← `(section))
#eval run do f' (← `(section foo))

#eval run do
  match ← `(match a with | a => b | a + 1 => b + 1) with
  | `(match a with $[| $pats =>%$arr $rhss]*) => `(match a with $[| $pats =>%$arr $rhss]*)
  | _ => unreachable!

#eval run do
  match ← `(match a with | a => b | a + 1 => b + 1) with
  | `(match a with $alts:matchAlt*) => `(match a with $alts:matchAlt*)
  | _ => unreachable!

open Parser.Term
#eval run do
  match ← `(structInstField|a := b) with
  | `(Parser.Term.structInstField| $lhs:ident := $rhs) => #[lhs, rhs]
  | _ => unreachable!

#eval run do
  match ← `({ a := a : a }) with
  | `({ a := a : 0 })      => "0"
  | `({ a := a $[: $a?]?}) => "1"
  | stx                    => "2"

#eval run `(sufficesDecl|x from x)

#eval run do
  match ← `([1, 2, 3, 4]) with
    | `([$x, $ys,*, $z]) => #[x, mkNullNode ys, z]
    | _ => unreachable!

#eval run do
  match ← `([1, 2]) with
    | `([$x, $y, $zs,*]) => zs.getElems
    | `([$x, $ys,*])     => ys.getElems
    | _ => unreachable!

#check (match · with | `([1, $ys,*, 2, $zs,*, 3]) => _)

#eval run do
  match Syntax.setHeadInfo (← `(fun x =>%$(Syntax.atom (SourceInfo.synthetic 2 2) "") x)) (SourceInfo.synthetic 1 1) with
  | `(fun%$i1 $x =>%$i2 $y) => pure #[i1.getPos?, i2.getPos?]
  | _ => unreachable!
