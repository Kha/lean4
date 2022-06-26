/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Notation for operators defined at Prelude.lean
-/
prelude
import Init.Prelude

namespace Lean.PrettyPrinter

def Formatter : Type := Nat → Nat → Nat → Nat → Nat → Nat
--@[extern "lean_formatter_empty"]
--axiom Formatter.empty : Formatter
--abbrev TrailingFormatter := Formatter
instance Formatter.inhabited : Inhabited Formatter := ⟨sorry⟩

def Parenthesizer : Type := Nat → Nat → Nat → Nat → Nat → Nat
instance Parenthesizer.inhabited : Inhabited Parenthesizer := ⟨sorry⟩

end Lean.PrettyPrinter

namespace Lean.Parser
open Lean.PrettyPrinter

opaque Parser : Type
@[extern "lean_parser_empty"]
axiom Parser.empty : Parser
instance Parser.inhabited : Inhabited Parser := ⟨Parser.empty⟩
abbrev TrailingParser := Parser

@[extern "l_Lean_Parser_andthen"]
opaque andthen (p q : Parser) : Parser
@[combinatorFormatter Lean.Parser.andthen, extern "l_Lean_Parser_andthen_formatter"]
opaque andthen.formatter (p q : Formatter) : Formatter
@[combinatorParenthesizer Lean.Parser.andthen, extern "l_Lean_Parser_andthen_parenthesizer"]
opaque andthen.parenthesizer (p q : Parenthesizer) : Parenthesizer

@[extern "l_Lean_Parser_leadingNode"]
opaque leadingNode (n : SyntaxNodeKind) (prec : Nat) (p : Parser) : TrailingParser
@[combinatorFormatter Lean.Parser.leadingNode, extern "l_Lean_Parser_leadingNode_formatter"]
opaque leadingNode.formatter (n : SyntaxNodeKind) (prec : Nat) (p : Formatter) : Formatter
@[combinatorParenthesizer Lean.Parser.leadingNode, extern "l_Lean_Parser_leadingNode_parenthesizer"]
opaque leadingNode.parenthesizer (n : SyntaxNodeKind) (prec : Nat) (p : Parenthesizer) : Parenthesizer

@[extern "l_Lean_Parser_symbol"]
opaque symbol (sym : String) : Parser
@[combinatorFormatter Lean.Parser.symbol, extern "l_Lean_Parser_symbol_formatter"]
opaque symbol.formatter (sym : String) : Formatter
@[combinatorParenthesizer Lean.Parser.symbol, extern "l_Lean_Parser_symbol_parenthesizer"]
opaque symbol.parenthesizer (sym : String) : Parenthesizer

@[extern "l_Lean_Parser_categoryParser"]
opaque categoryParser (cat : Name) (rbp : Nat) : Parser
@[combinatorFormatter Lean.Parser.categoryParser, extern "l_Lean_Parser_categoryParser_formatter"]
opaque categoryParser.formatter (cat : Name) (rbp : Nat) : Formatter
@[combinatorParenthesizer Lean.Parser.categoryParser, extern "l_Lean_Parser_categoryParser_parenthesizer"]
opaque categoryParser.parenthesizer (cat : Name) (rbp : Nat) : Parenthesizer

def prec (rbp := 0) := categoryParser `prec rbp
def prio (rbp := 0) := categoryParser `prio rbp
def stx (rbp := 0) := categoryParser `stx rbp
def term (rbp := 0) := categoryParser `term rbp

@[extern "l_Lean_Parser_ident"]
opaque ident : Parser
@[combinatorFormatter Lean.Parser.ident, extern "l_Lean_Parser_ident_formatter"]
opaque ident.formatter : Formatter
@[combinatorParenthesizer Lean.Parser.ident, extern "l_Lean_Parser_ident_parenthesizer"]
opaque ident.parenthesizer : Parenthesizer

end Lean.Parser

open Lean
open Lean.Parser
open Lean.PrettyPrinter

@[extern "l_Lean_Name_mangle"]
opaque Lean.Name.mangle (n : Name) (pre : String := "l_") : String := ""

@[extern "l_Lean_Syntax_mkStrLit"]
opaque Lean.Syntax.mkStrLit (s : String) (info : SourceInfo := SourceInfo.none) : Syntax

local macro "bootstrap_parser" id:ident ty:term : command =>
  set_option hygiene false in
  `(@[extern $(.mkStrLit id.getId.mangle):str]
    opaque $id:ident : $ty Parser
    namespace $id
      --@[combinatorParenthesizer $id, extern $(.mkStrLit (id.getId.append `parenthesizer).mangle):str]
      --opaque parenthesizer : $ty Parenthesizer
      --@[combinatorFormatter $id, extern $(.mkStrLit (id.getId.append `formatter).mangle):str]
      --opaque formatter : $ty Formatter
      @[combinatorParenthesizer $id]
      opaque parenthesizer : $ty Parenthesizer
      @[combinatorFormatter $id]
      opaque formatter : $ty Formatter
    end $id)

bootstrap_parser Lean.Parser.group fun Parser => Parser → Parser
bootstrap_parser Lean.Parser.ppRealGroup fun Parser => Parser → Parser
bootstrap_parser Lean.Parser.ppRealFill fun Parser => Parser → Parser
bootstrap_parser Lean.Parser.ppIndent fun Parser => Parser → Parser
bootstrap_parser Lean.Parser.ppDedent fun Parser => Parser → Parser
bootstrap_parser Lean.Parser.ppSpace fun Parser => Parser
bootstrap_parser Lean.Parser.ppLine fun Parser => Parser

bootstrap_parser Lean.Parser.checkColGt fun Parser => (errorMsg : String := "checkColGt") → Parser
bootstrap_parser Lean.Parser.checkColGe fun Parser => (errorMsg : String := "checkColGe") → Parser
bootstrap_parser Lean.Parser.checkWsBefore fun Parser => (errorMsg : String := "space before") → Parser
abbrev Lean.Parser.ws := checkWsBefore
bootstrap_parser Lean.Parser.checkNoWsBefore fun Parser => (errorMsg : String := "no space before") → Parser
@[runParserAttributeHooks] abbrev Lean.Parser.noWs := checkNoWsBefore
bootstrap_parser Lean.Parser.withPosition fun Parser => Parser → Parser

bootstrap_parser Lean.Parser.numLit fun Parser => Parser
abbrev Lean.Parser.num := numLit
bootstrap_parser Lean.Parser.strLit fun Parser => Parser
abbrev Lean.Parser.str := strLit
bootstrap_parser Lean.Parser.Tactic.tacticSeq fun Parser => Parser

--bootstrap_parser Lean.Parser.nonReservedSymbol fun Parser => String → (includeIdent : Bool := false) → Parser
bootstrap_parser Lean.Parser.optional fun Parser => Parser → Parser
bootstrap_parser Lean.Parser.many fun Parser => Parser → Parser
bootstrap_parser Lean.Parser.many1 fun Parser => Parser → Parser
bootstrap_parser Lean.Parser.atomic fun Parser => Parser → Parser
bootstrap_parser Lean.Parser.orelse fun Parser => Parser → Parser → Parser
bootstrap_parser Lean.Parser.trailingNode fun Parser => SyntaxNodeKind → (prec lhsPrec : Nat) → Parser → Parser
bootstrap_parser Lean.Parser.notFollowedBy fun Parser => Parser → Parser
bootstrap_parser Lean.Parser.sepBy fun Parser => (p : Parser) → (sep : String) → (psep : Parser) → (allowTrailingSep : Bool := false) → Parser
bootstrap_parser Lean.Parser.sepBy1 fun Parser => (p : Parser) → (sep : String) → (psep : Parser) → (allowTrailingSep : Bool := false) → Parser

@[extern "l_Lean_Parser_nonReservedSymbol"]
opaque Lean.Parser.nonReservedSymbol (sym : String) (b : Bool := false) : Parser
@[combinatorFormatter Lean.Parser.nonReservedSymbol, extern "l_Lean_Parser_nonReservedSymbol_formatter"]
opaque Lean.Parser.nonReservedSymbol.formatter (sym : String) (b : Bool := false) : Formatter
@[combinatorParenthesizer Lean.Parser.nonReservedSymbol, extern "l_Lean_Parser_nonReservedSymbol_parenthesizer"]
opaque Lean.Parser.nonReservedSymbol.parenthesizer (sym : String) (b : Bool := false) : Parenthesizer

@[extern "l_Lean_Parser_nodeWithAntiquot"]
opaque Lean.Parser.nodeWithAntiquot (name : String) (kind : SyntaxNodeKind) (p : Parser) (anonymous := false) : Parser
@[combinatorFormatter Lean.Parser.nodeWithAntiquot, extern "l_Lean_Parser_nodeWithAntiquot_formatter"]
opaque Lean.Parser.nodeWithAntiquot.formatter (name : String) (kind : SyntaxNodeKind) (p : Formatter) (anonymous := false) : Formatter
@[combinatorParenthesizer Lean.Parser.nodeWithAntiquot, extern "l_Lean_Parser_nodeWithAntiquot_parenthesizer"]
opaque Lean.Parser.nodeWithAntiquot.parenthesizer (name : String) (kind : SyntaxNodeKind) (p : Parenthesizer) (anonymous := false) : Parenthesizer

bootstrap_parser Lean.Parser.Term.letDecl fun Parser => Parser
bootstrap_parser Lean.Parser.Term.haveDecl fun Parser => Parser
bootstrap_parser Lean.Parser.Term.sufficesDecl fun Parser => Parser
bootstrap_parser Lean.Parser.Term.letRecDecls fun Parser => Parser
bootstrap_parser Lean.Parser.Term.hole fun Parser => Parser
bootstrap_parser Lean.Parser.Term.syntheticHole fun Parser => Parser
bootstrap_parser Lean.Parser.Term.matchDiscr fun Parser => Parser
bootstrap_parser Lean.Parser.Term.bracketedBinder fun Parser => Parser
bootstrap_parser Lean.Parser.Term.attrKind fun Parser => Parser

bootstrap_parser Lean.Parser.interpolatedStr fun Parser => Parser → Parser

-- DSL for specifying parser precedences and priorities

namespace Lean.Parser.Syntax

syntax:65 (name := addPrec) prec " + " prec:66 : prec
syntax:65 (name := subPrec) prec " - " prec:66 : prec

syntax:65 (name := addPrio) prio " + " prio:66 : prio
syntax:65 (name := subPrio) prio " - " prio:66 : prio

end Lean.Parser.Syntax

macro "max"  : prec => `(1024) -- maximum precedence used in term parsers, in particular for terms in function position (`ident`, `paren`, ...)
macro "arg"  : prec => `(1023) -- precedence used for application arguments (`do`, `by`, ...)
macro "lead" : prec => `(1022) -- precedence used for terms not supposed to be used as arguments (`let`, `have`, ...)
macro "(" p:prec ")" : prec => return p
macro "min"  : prec => `(10)   -- minimum precedence used in term parsers
macro "min1" : prec => `(11)   -- `(min+1) we can only `min+1` after `Meta.lean`
/-
  `max:prec` as a term. It is equivalent to `eval_prec max` for `eval_prec` defined at `Meta.lean`.
  We use `max_prec` to workaround bootstrapping issues. -/
macro "max_prec" : term => `(1024)

macro "default" : prio => `(1000)
macro "low"     : prio => `(100)
macro "mid"     : prio => `(1000)
macro "high"    : prio => `(10000)
macro "(" p:prio ")" : prio => return p

-- Basic notation for defining parsers
-- NOTE: precedence must be at least `arg` to be used in `macro` without parentheses
syntax:arg stx:max "+" : stx
syntax:arg stx:max "*" : stx
syntax:arg stx:max "?" : stx
syntax:2 stx:2 " <|> " stx:1 : stx

macro_rules
  | `(stx| $p +) => `(stx| many1($p))
  | `(stx| $p *) => `(stx| many($p))
  | `(stx| $p ?) => `(stx| optional($p))
  | `(stx| $p₁ <|> $p₂) => `(stx| orelse($p₁, $p₂))

/- Comma-separated sequence. -/
macro:arg x:stx:max ",*"   : stx => `(stx| sepBy($x, ",", ", "))
macro:arg x:stx:max ",+"   : stx => `(stx| sepBy1($x, ",", ", "))
/- Comma-separated sequence with optional trailing comma. -/
macro:arg x:stx:max ",*,?" : stx => `(stx| sepBy($x, ",", ", ", allowTrailingSep))
macro:arg x:stx:max ",+,?" : stx => `(stx| sepBy1($x, ",", ", ", allowTrailingSep))

macro:arg "!" x:stx:max : stx => `(stx| notFollowedBy($x))

syntax (name := rawNatLit) "nat_lit " num : term

infixr:90 " ∘ "  => Function.comp
infixr:35 " × "  => Prod

infixl:55 " ||| " => HOr.hOr
infixl:58 " ^^^ " => HXor.hXor
infixl:60 " &&& " => HAnd.hAnd
infixl:65 " + "   => HAdd.hAdd
infixl:65 " - "   => HSub.hSub
infixl:70 " * "   => HMul.hMul
infixl:70 " / "   => HDiv.hDiv
infixl:70 " % "   => HMod.hMod
infixl:75 " <<< " => HShiftLeft.hShiftLeft
infixl:75 " >>> " => HShiftRight.hShiftRight
infixr:80 " ^ "   => HPow.hPow
infixl:65 " ++ "  => HAppend.hAppend
prefix:100 "-"    => Neg.neg
prefix:100 "~~~"  => Complement.complement
/-
  Remark: the infix commands above ensure a delaborator is generated for each relations.
  We redefine the macros below to be able to use the auxiliary `binop%` elaboration helper for binary operators.
  It addresses issue #382. -/
macro_rules | `($x ||| $y) => `(binop% HOr.hOr $x $y)
macro_rules | `($x ^^^ $y) => `(binop% HXor.hXor $x $y)
macro_rules | `($x &&& $y) => `(binop% HAnd.hAnd $x $y)
macro_rules | `($x + $y)   => `(binop% HAdd.hAdd $x $y)
macro_rules | `($x - $y)   => `(binop% HSub.hSub $x $y)
macro_rules | `($x * $y)   => `(binop% HMul.hMul $x $y)
macro_rules | `($x / $y)   => `(binop% HDiv.hDiv $x $y)
macro_rules | `($x ++ $y)  => `(binop% HAppend.hAppend $x $y)

-- declare ASCII alternatives first so that the latter Unicode unexpander wins
infix:50 " <= " => LE.le
infix:50 " ≤ "  => LE.le
infix:50 " < "  => LT.lt
infix:50 " >= " => GE.ge
infix:50 " ≥ "  => GE.ge
infix:50 " > "  => GT.gt
infix:50 " = "  => Eq
infix:50 " == " => BEq.beq
/-
  Remark: the infix commands above ensure a delaborator is generated for each relations.
  We redefine the macros below to be able to use the auxiliary `binrel%` elaboration helper for binary relations.
  It has better support for applying coercions. For example, suppose we have `binrel% Eq n i` where `n : Nat` and
  `i : Int`. The default elaborator fails because we don't have a coercion from `Int` to `Nat`, but
  `binrel%` succeeds because it also tries a coercion from `Nat` to `Int` even when the nat occurs before the int. -/
macro_rules | `($x <= $y) => `(binrel% LE.le $x $y)
macro_rules | `($x ≤ $y)  => `(binrel% LE.le $x $y)
macro_rules | `($x < $y)  => `(binrel% LT.lt $x $y)
macro_rules | `($x > $y)  => `(binrel% GT.gt $x $y)
macro_rules | `($x >= $y) => `(binrel% GE.ge $x $y)
macro_rules | `($x ≥ $y)  => `(binrel% GE.ge $x $y)
macro_rules | `($x = $y)  => `(binrel% Eq $x $y)
macro_rules | `($x == $y) => `(binrel_no_prop% BEq.beq $x $y)

infixr:35 " /\\ " => And
infixr:35 " ∧ "   => And
infixr:30 " \\/ " => Or
infixr:30 " ∨  "  => Or
notation:max "¬" p:40 => Not p

infixl:35 " && " => and
infixl:30 " || " => or
notation:max "!" b:40 => not b

infix:50 " ∈ " => Membership.mem
notation:50 a:50 " ∉ " b:50 => ¬ (a ∈ b)

infixr:67 " :: " => List.cons
syntax:20 term:21 " <|> " term:20 : term
syntax:60 term:61 " >> " term:60 : term
infixl:55  " >>= " => Bind.bind
notation:60 a:60 " <*> " b:61 => Seq.seq a fun _ : Unit => b
notation:60 a:60 " <* " b:61 => SeqLeft.seqLeft a fun _ : Unit => b
notation:60 a:60 " *> " b:61 => SeqRight.seqRight a fun _ : Unit => b
infixr:100 " <$> " => Functor.map

macro_rules | `($x <|> $y) => `(binop_lazy% HOrElse.hOrElse $x $y)
macro_rules | `($x >> $y)  => `(binop_lazy% HAndThen.hAndThen $x $y)

syntax (name := termDepIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("if " ident " : " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

macro_rules
  | `(if $h:ident : $c then $t:term else $e:term) => `(let_mvar% ?m := $c; wait_if_type_mvar% ?m; dite ?m (fun $h:ident => $t) (fun $h:ident => $e))

syntax (name := termIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("if " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

macro_rules
  | `(if $c then $t:term else $e:term) => `(let_mvar% ?m := $c; wait_if_type_mvar% ?m; ite ?m $t $e)

macro "if " "let " pat:term " := " d:term " then " t:term " else " e:term : term =>
  `(match $d:term with | $pat:term => $t | _ => $e)

syntax (name := boolIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("bif " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

macro_rules
  | `(bif $c then $t:term else $e:term) => `(cond $c $t $e)

syntax:min term " <| " term:min : term

macro_rules
  | `($f $args* <| $a) => let args := args.push a; `($f $args*)
  | `($f <| $a) => `($f $a)

syntax:min term " |> " term:min1 : term

macro_rules
  | `($a |> $f $args*) => let args := args.push a; `($f $args*)
  | `($a |> $f)        => `($f $a)

-- Haskell-like pipe <|
-- Note that we have a whitespace after `$` to avoid an ambiguity with the antiquotations.
syntax:min term atomic(" $" ws) term:min : term

macro_rules
  | `($f $args* $ $a) => let args := args.push a; `($f $args*)
  | `($f $ $a) => `($f $a)

syntax "{ " ident (" : " term)? " // " term " }" : term

macro_rules
  | `({ $x : $type // $p }) => ``(Subtype (fun ($x:ident : $type) => $p))
  | `({ $x // $p })         => ``(Subtype (fun ($x:ident : _) => $p))

/-
  `without_expected_type t` instructs Lean to elaborate `t` without an expected type.
  Recall that terms such as `match ... with ...` and `⟨...⟩` will postpone elaboration until
  expected type is known. So, `without_expected_type` is not effective in this case. -/
macro "without_expected_type " x:term : term => `(let aux := $x; aux)

syntax "[" term,* "]"  : term
syntax "%[" term,* "|" term "]" : term -- auxiliary notation for creating big list literals

namespace Lean

macro_rules
  | `([ $elems,* ]) => do
    let rec expandListLit (i : Nat) (skip : Bool) (result : Syntax) : MacroM Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => expandListLit i true  (← ``(List.cons $(elems.elemsAndSeps[i]) $result))
    if elems.elemsAndSeps.size < 64 then
      expandListLit elems.elemsAndSeps.size false (← ``(List.nil))
    else
      `(%[ $elems,* | List.nil ])

-- Declare `this` as a keyword that unhygienically binds to a scope-less `this` assumption (or other binding).
-- The keyword prevents declaring a `this` binding except through metapgrogramming, as is done by `have`/`show`.
/-- Special identifier introduced by "anonymous" `have : ...`, `suffices p ...` etc. -/
macro tk:"this" : term => return Syntax.ident tk.getHeadInfo "this".toSubstring `this []
