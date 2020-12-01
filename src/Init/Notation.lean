/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Notation for operators defined at Prelude.lean
-/
prelude
import Init.Prelude

infixr:90 " ∘ "  => Function.comp
infixr:35 " × "  => Prod

infixl:65 " + "  => Add.add
infixl:65 " - "  => Sub.sub
infixl:70 " * "  => Mul.mul
infixl:70 " / "  => Div.div
infixl:70 " % "  => Mod.mod
infixl:70 " %ₙ " => ModN.modn
infixr:80 " ^ "  => Pow.pow
prefix:100 "-"   => Neg.neg

-- declare ASCII alternatives first so that the latter Unicode unexpander wins
infix:50 " <= " => HasLessEq.LessEq
infix:50 " ≤ "  => HasLessEq.LessEq
infix:50 " < "  => HasLess.Less
infix:50 " >= " => GreaterEq
infix:50 " ≥ "  => GreaterEq
infix:50 " > "  => Greater
infix:50 " = "  => Eq
infix:50 " == " => BEq.beq
infix:50 " ~= " => HEq
infix:50 " ≅ "  => HEq

infixr:35 " /\\ " => And
infixr:35 " ∧ "   => And
infixr:30 " \\/ " => Or
infixr:30 " ∨   " => Or
notation:max "¬" p:40 => Not p

infixl:35 " && " => and
infixl:30 " || " => or
notation:max "!" b:40 => not b

infixl:65 " ++ " => Append.append
infixr:67 " :: " => List.cons

infixr:2   " <|> " => OrElse.orElse
infixr:60  " >> "  => AndThen.andThen
infixl:55  " >>= " => Bind.bind
infixl:60  " <*> " => Seq.seq
infixl:60  " <* "  => SeqLeft.seqLeft
infixr:60  " *> "  => SeqRight.seqRight
infixr:100 " <$> " => Functor.map

macro "if" h:ident " : " c:term " then " t:term " else " e:term : term =>
  `(dite $c (fun $h => $t) (fun $h => $e))

macro "if" c:term " then " t:term " else " e:term : term =>
  `(ite $c $t $e)

syntax "[" sepBy(term, ", ") "]"  : term

open Lean in
macro_rules
  | `([ $elems* ]) => do
    let rec expandListLit (i : Nat) (skip : Bool) (result : Syntax) : MacroM Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => expandListLit i true  (← `(List.cons $(elems[i]) $result))
    expandListLit elems.size false (← `(List.nil))

syntax:0 term "<|" term:0 : term

macro_rules
  | `($f $args* <| $a) => let args := args.push a; `($f $args*)
  | `($f <| $a) => `($f $a)

syntax:0 term "|>" term:1 : term

macro_rules
  | `($a |> $f $args*) => let args := args.push a; `($f $args*)
  | `($a |> $f)        => `($f $a)

-- Haskell-like pipe <|
-- Note that we have a whitespace after `$` to avoid an ambiguity with the antiquotations.
syntax:0 term "$" ws term:0 : term

macro_rules
  | `($f $args* $ $a) => let args := args.push a; `($f $args*)
  | `($f $ $a) => `($f $a)

-- Basic notation for defining parsers
syntax   stx "+" : stx
syntax   stx "*" : stx
syntax   stx "?" : stx
syntax:2 stx " <|> " stx:1 : stx

macro_rules
  | `(stx| $p +) => `(stx| many1($p))
  | `(stx| $p *) => `(stx| many($p))
  | `(stx| $p ?) => `(stx| optional($p))
  | `(stx| $p₁ <|> $p₂) => `(stx| orelse($p₁, $p₂))

macro "!" x:stx : stx => `(stx| notFollowedBy($x))

syntax "{ " ident (" : " term)? " // " term " }" : term

macro_rules
  | `({ $x : $type // $p }) => `(Subtype (fun ($x:ident : $type) => $p))
  | `({ $x // $p })         => `(Subtype (fun ($x:ident : _) => $p))

/-
  `withoutExpected! t` instructs Lean to elaborate `t` without an expected type.
  Recall that terms such as `match ... with ...` and `⟨...⟩` will postpone elaboration until
  expected type is known. So, `withoutExpected!` is not effective in this case. -/
macro "withoutExpectedType! " x:term : term => `(let aux := $x; aux)

namespace Lean.Parser.Tactic

syntax[intro] "intro " notFollowedBy("|") (colGt term:max)* : tactic
syntax[intros] "intros " (colGt (ident <|> "_"))* : tactic
syntax[revert] "revert " (colGt ident)+ : tactic
syntax[clear] "clear " (colGt ident)+ : tactic
syntax[subst] "subst " (colGt ident)+ : tactic
syntax[assumption] "assumption" : tactic
syntax[apply] "apply " term : tactic
syntax[exact] "exact " term : tactic
syntax[refine] "refine " term : tactic
syntax[refine!] "refine! " term : tactic
syntax[case] "case " ident " => " tacticSeq : tactic
syntax[allGoals] "allGoals " tacticSeq : tactic
syntax[focus] "focus " tacticSeq : tactic
syntax[skip] "skip" : tactic
syntax[done] "done" : tactic
syntax[traceState] "traceState" : tactic
syntax[failIfSuccess] "failIfSuccess " tacticSeq : tactic
syntax[generalize] "generalize " atomic(ident " : ")? term:51 " = " ident : tactic
syntax[paren] "(" tacticSeq ")" : tactic
syntax[withReducible] "withReducible " tacticSeq : tactic
syntax[withReducibleAndInstances] "withReducibleAndInstances " tacticSeq : tactic
syntax:2[orelse] tactic "<|>" tactic:1 : tactic
macro "try " t:tacticSeq : tactic => `(($t) <|> skip)


macro "rfl" : tactic => `(exact rfl)
macro "decide!" : tactic => `(exact decide!)
macro "admit" : tactic => `(exact sorry)

syntax locationWildcard := "*"
syntax locationTarget   := "⊢" <|> "|-"
syntax locationHyp      := (colGt ident)+
syntax location         := withPosition("at " locationWildcard <|> locationTarget <|> locationHyp)

syntax[change] "change " term (location)? : tactic
syntax[changeWith] "change " term " with " term (location)? : tactic

syntax rwRule    := ("←" <|> "<-")? term
syntax rwRuleSeq := "[" sepBy1T(rwRule, ", ") "]"

syntax[rewrite] "rewrite " rwRule (location)? : tactic
syntax[rewriteSeq, 1] "rewrite " rwRuleSeq (location)? : tactic
syntax[erewrite] "erewrite " rwRule (location)? : tactic
syntax[erewriteSeq, 1] "erewrite " rwRuleSeq (location)? : tactic

syntax[rw] "rw " rwRule (location)? : tactic
syntax[rwSeq, 1] "rw " rwRuleSeq (location)? : tactic
syntax[erw] "erw " rwRule (location)? : tactic
syntax[erwSeq, 1] "erw " rwRuleSeq (location)? : tactic

private def withCheapRefl (tac : Syntax) : MacroM Syntax :=
  `(tactic| $tac; try (withReducible rfl))

@[macro rw]
def expandRw : Macro :=
  fun stx => withCheapRefl (stx.setKind `Lean.Parser.Tactic.rewrite |>.setArg 0 (mkAtomFrom stx "rewrite"))

@[macro rwSeq]
def expandRwSeq : Macro :=
  fun stx => withCheapRefl (stx.setKind `Lean.Parser.Tactic.rewriteSeq |>.setArg 0 (mkAtomFrom stx "rewrite"))

@[macro erw]
def expandERw : Macro :=
  fun stx => withCheapRefl (stx.setKind `Lean.Parser.Tactic.erewrite |>.setArg 0 (mkAtomFrom stx "erewrite"))

@[macro erwSeq]
def expandERwSeq : Macro :=
  fun stx => withCheapRefl (stx.setKind `Lean.Parser.Tactic.erewriteSeq |>.setArg 0 (mkAtomFrom stx "erewrite"))

syntax[injection] "injection " term (" with " (colGt (ident <|> "_"))+)? : tactic

syntax[«have»] "have " haveDecl : tactic
syntax[«suffices»] "suffices " sufficesDecl : tactic
syntax[«show»] "show " term : tactic
syntax[«let»] "let " letDecl : tactic
syntax[«let!»] "let! " letDecl : tactic
syntax[letrec] withPosition(atomic(group("let " &"rec ")) letRecDecls) : tactic

syntax inductionAlt  := (ident <|> "_") (ident <|> "_")* " => " (hole <|> syntheticHole <|> tacticSeq)
syntax inductionAlts := "with " withPosition("| " sepBy1(inductionAlt, colGe "| "))
syntax[induction] "induction " sepBy1(term, ", ") (" using " ident)?  ("generalizing " ident+)? (inductionAlts)? : tactic
syntax casesTarget := atomic(ident " : ")? term
syntax[cases] "cases " sepBy1(casesTarget, ", ") (" using " ident)? (inductionAlts)? : tactic

syntax matchAlt  := sepBy1(term, ", ") " => " (hole <|> syntheticHole <|> tacticSeq)
syntax matchAlts := withPosition("| " sepBy1(matchAlt, colGe "| "))
syntax[«match»] "match " sepBy1(matchDiscr, ", ") (" : " term)? " with " matchAlts : tactic

syntax[introMatch] "intro " matchAlts : tactic

syntax[existsIntro] "exists " term : tactic

/- We use a priority > 0, to avoid ambiguity with the builtin `have` notation -/
macro[1] "have" x:ident " := " p:term : tactic => `(have $x:ident : _ := $p)

syntax "repeat " tacticSeq : tactic
macro_rules
  | `(tactic| repeat $seq) => `(tactic| (($seq); repeat $seq) <|> skip)

end Lean.Parser.Tactic
