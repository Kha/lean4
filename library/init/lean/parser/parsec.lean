/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

Implementation for the parsec parser combinators described in the
paper:
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/parsec-paper-letter.pdf
-/
prelude
import init.data.to_string init.data.string.basic init.data.list.basic init.control.except
import init.data.repr init.lean.name init.data.dlist init.control.monad_fail init.control.combinators
import init.util

namespace lean
namespace parser
open string (iterator)

namespace parsec
@[reducible] def position : Type := nat

structure pre_message (μ : Type := unit) :=
(unexpected : string       := "")          -- unexpected input
(expected   : dlist string := dlist.empty) -- expected productions
(custom     : option μ     := none)

structure message (μ : Type := unit) extends pre_message μ :=
(it : iterator)

def expected.to_string : list string → string
| []       := ""
| [e]      := e
| [e1, e2] := e1 ++ " or " ++ e2
| (e::es)  := e ++ ", " ++ expected.to_string es

protected def message.to_string {μ : Type} (msg : message μ) : string :=
let (line, col) := msg.it.to_string.line_column msg.it.offset in
-- always print ":"; we assume at least one of `unexpected` and `expected` to be non-empty
let loc := ["error at line " ++ to_string line ++ ", column " ++ to_string col ++ ":"] in
let unexpected := (if msg.unexpected = "" then [] else ["unexpected " ++ msg.unexpected]) in
let ex_list := msg.expected.to_list in
let expected := if ex_list = [] then [] else ["expected " ++ expected.to_string ex_list] in
"\n".intercalate $ loc ++ unexpected ++ expected

instance {μ : Type} : has_to_string (message μ) :=
⟨message.to_string⟩

--- use for e.g. upcasting parsec errors with `monad_except.lift_except`
instance {μ : Type} : has_lift (message μ) string :=
⟨to_string⟩

/-
Remark: we store expected "error" messages in `ok_eps` results.
They contain the error that would have occurred if a
successful "epsilon" alternative was not taken.
-/
inductive result (μ α : Type)
| ok {} (a : α) (it : iterator) (expected : option $ dlist string) : result
| error {} (it : iterator) (msg : pre_message μ) (consumed : bool) : result

@[inline] def result.mk_eps {μ α : Type} (a : α) (it : iterator) : result μ α :=
result.ok a it (some dlist.empty)
end parsec

open parsec

def parsec_t (μ : Type) (m : Type → Type) (α : Type) :=
iterator → bool → m (result μ α)

abbreviation parsec (μ : Type) := parsec_t μ id
/-- `parsec` without custom error message type -/
abbreviation parsec' := parsec unit

namespace parsec_t
open parsec.result
variables {m : Type → Type} [monad m] {μ α β : Type}

def run (p : parsec_t μ m α) (s : string) (msgs_enabled : bool := tt) (fname := "") : m (except (message μ) α) :=
do r ← p s.mk_iterator msgs_enabled,
   pure $ match r with
   | ok a _ _        := except.ok a
   | error it msg _  := except.error {it := it, ..msg}

@[inline] protected def pure (a : α) : parsec_t μ m α :=
λ it e, pure (mk_eps a it)

def eps : parsec_t μ m unit :=
parsec_t.pure ()

@[macro_inline] def mk_if {μ} (e : bool) (m : pre_message μ) : pre_message μ :=
if e then m else {}

protected def failure : parsec_t μ m α :=
λ it e, pure (error it (mk_if e { unexpected := "failure" }) ff)

def merge (msg₁ msg₂ : pre_message μ) : pre_message μ :=
{ expected := msg₁.expected ++ msg₂.expected, ..msg₁ }

@[inline_if_reduce] def bind_mk_res (msgs_enabled : bool) (ex₁ : option (dlist string)) (r : result μ β) : result μ β :=
match ex₁, r with
| none,     ok b it _          := ok b it none
| none,     error it msg _     := error it msg tt
| some ex₁, ok b it (some ex₂) := ok b it (some $ ex₁ ++ ex₂)
| some ex₁, error it msg₂ ff   := error it (mk_if msgs_enabled { expected := ex₁ ++ msg₂.expected, .. msg₂ }) ff
| some ex₁, other              := other

/--
  The `bind p q` combinator behaves as follows:
  1- If `p` fails, then it fails.
  2- If `p` succeeds and consumes input, then execute `q`
  3- If `q` succeeds but does not consume input, then execute `q`
     and merge error messages if both do not consume any input.
-/
@[inline] protected def bind (p : parsec_t μ m α) (q : α → parsec_t μ m β) : parsec_t μ m β :=
λ it e, do
 r ← p it e,
 match r with
 | ok a it ex₁     := bind_mk_res e ex₁ <$> q a it e
 | error it msg c  := pure (error it msg c)

instance : monad (parsec_t μ m) :=
{ bind := λ _ _, parsec_t.bind, pure := λ _, parsec_t.pure }

instance : monad_fail parsec' :=
{ fail := λ _ s it e, error it (mk_if e { unexpected := s, custom := () }) ff }

instance : monad_except (message μ) (parsec_t μ m) :=
{ throw := λ _ msg it _, pure (error msg.it msg.to_pre_message ff),
  catch := λ _ p c it e, do
    r ← p it e,
    match r with
    | error it' msg cns := do {
      r ← c {it := it', ..msg} it' e,
      pure $ match r with
      | error it' msg' cns' := error it' msg' (cns || cns')
      | other               := other }
    | other       := pure other }

instance : has_monad_lift m (parsec_t μ m) :=
{ monad_lift := λ α x it _, do a ← x, pure (mk_eps a it) }

@[inline_if_reduce] def labels_mk_res (r : result μ α) (lbls : dlist string) : result μ α :=
match r with
  | ok a it (some _) := ok a it (some lbls)
  | error it msg ff  := error it {expected := lbls, ..msg} ff
  | other            := other

@[inline] def labels (p : parsec_t μ m α) (lbls : dlist string) : parsec_t μ m α :=
λ it e, do
   r ← p it e,
   pure $ labels_mk_res r lbls

@[inline_if_reduce] def try_mk_res (r : result μ α) : result μ α :=
match r with
| error it msg _  := error it msg ff
| other           := other

/--
`try p` behaves like `p`, but it pretends `p` hasn't
consumed any input when `p` fails.

It is useful for implementing infinite lookahead.
The parser `try p <|> q` will try `q` even when
`p` has consumed input.

It is also useful for specifying both the lexer and parser
together.
```
    (do try (ch 'l' >> ch 'e' >> ch 't'), whitespace, ...)
    <|>
    ...
```
Without the `try` combinator we will not be able to backtrack on the `let` keyword.
-/
@[inline] def try (p : parsec_t μ m α) : parsec_t μ m α :=
λ it e, do
  r ← p it e,
  pure $ try_mk_res r

@[inline_if_reduce] def orelse_mk_res (msgs_enabled : bool) (it₁ : iterator) (msg₁ : pre_message μ) (r : result μ α) : result μ α :=
match r with
| ok a it' (some ex₂) := ok a it' (some (msg₁.expected ++ ex₂))
| error _ msg₂ ff     := error it₁ (mk_if msgs_enabled (merge msg₁ msg₂)) ff
| other               := other

/--
  The `orelse p q` combinator behaves as follows:
  1- If `p` succeeds *or* consumes input, return
     its result. Otherwise, execute `q` and return its
     result.
     Recall that the `try p` combinator can be used to
     pretend that `p` did not consume any input, and
     simulate infinite lookahead.
  2- If both `p` and `q` did not consume any input, then
     combine their error messages (even if one of
     them succeeded).
-/
@[inline] protected def orelse (p q : parsec_t μ m α) : parsec_t μ m α :=
λ it e, do
  r ← p it e,
  match r with
  | error it₁ msg₁ ff := do { r ← q it e, pure $ orelse_mk_res e it₁ msg₁ r }
  | other             := pure other

instance : alternative (parsec_t μ m) :=
{ orelse         := λ _, parsec_t.orelse,
  failure        := λ _, parsec_t.failure,
  ..parsec_t.monad }

/-- Parse `p` without consuming any input. -/
@[specialize] def lookahead (p : parsec_t μ m α) : parsec_t μ m α :=
λ it e, do
  r ← p it e,
  pure $ match r with
  | ok a s' _ := mk_eps a it
  | other     := other

/-- `not_followed_by p` succeeds when parser `p` fails -/
@[specialize] def not_followed_by (p : parsec' α) (msg : string := "input") : parsec' unit :=
λ it e, do
  r ← p it ff,
  pure $ match r with
  | ok _ _ _     := error it (mk_if e { unexpected := msg, custom := () }) ff
  | error _ _ _  := mk_eps () it

def dbg (label : string) (p : parsec_t μ m α) : parsec_t μ m α :=
λ it e, do
  r ← p it e,
  pure $ trace ("DBG " ++ label ++ ": \"" ++ (it.extract (it.nextn 40)).get_or_else "" ++ "\"") $ match r : _ → result μ α with
  | ok a it' none      := trace ("consumed ok : '" ++ (it.extract it').get_or_else "" ++ "'") $ @ok μ α a it' none
  | ok a it' (some ex) := trace ("empty ok : '" ++ (it.extract it').get_or_else "" ++ "'") $ @ok μ α a it' (some ex)
  | error it' msg tt   := trace ("consumed error : '" ++ (it.extract it').get_or_else "" ++ "'\n" ++ to_string {message . it := it', ..msg}) $ @error μ α it' msg tt
  | error it' msg ff   := trace ("empty error : '" ++ (it.extract it').get_or_else "" ++ "'\n" ++ to_string {message . it := it', ..msg}) $ @error μ α it' msg ff

end parsec_t

/- Type class for abstracting from concrete monad stacks containing a `parsec` somewhere. -/
class monad_parsec (μ : out_param Type) (m : Type → Type) :=
-- analogous to e.g. `monad_reader.lift` before simplification (see there)
(lift {} {α : Type} : parsec μ α → m α)
-- Analogous to e.g. `monad_reader_adapter.map` before simplification (see there).
-- Its usage seems to be way too common to justify moving it into a separate type class.
(map {} {α : Type} : (∀ {m'} [monad m'] {α}, parsec_t μ m' α → parsec_t μ m' α) → m α → m α)

/-- `parsec` without custom error message type -/
abbreviation monad_parsec' := monad_parsec unit

variables {μ : Type}

instance {m : Type → Type} [monad m] : monad_parsec μ (parsec_t μ m) :=
{ lift := λ α p it e, pure (p it e),
  map  := λ α f x, f x }

instance monad_parsec_trans {m n : Type → Type} [has_monad_lift m n] [monad_functor m m n n] [monad_parsec μ m] : monad_parsec μ n :=
{ lift := λ α p, monad_lift (monad_parsec.lift p : m α),
  map  := λ α f x, monad_map (λ β x, (monad_parsec.map @f x : m β)) x }

namespace monad_parsec
open parsec_t
variables {m : Type → Type} [monad m] [monad_parsec μ m] {α β : Type}

@[macro_inline]
def error {α : Type} (unexpected : string) (expected : dlist string := dlist.empty)
          (it : option iterator := none) (custom : option μ := none) : m α :=
lift $ λ it' e, result.error (it.get_or_else it') (mk_if e { unexpected := unexpected, expected := expected, custom := custom }) ff

@[inline] def left_over : m iterator :=
lift $ λ it e, result.mk_eps it it

def msgs_enabled : m bool :=
lift $ λ it e, result.mk_eps e it

/-- Return the number of characters left to be parsed. -/
@[inline] def remaining : m nat :=
string.iterator.remaining <$> left_over

@[inline] def labels (p : m α) (lbls : dlist string) : m α :=
map (λ m' inst β p, @parsec_t.labels m' inst μ β p lbls) p

@[inline] def label (p : m α) (lbl : string) : m α :=
labels p (dlist.singleton lbl)

infixr ` <?> `:2 := label

@[inline] def hidden (p : m α) : m α :=
labels p dlist.empty

/--
`try p` behaves like `p`, but it pretends `p` hasn't
consumed any input when `p` fails.

It is useful for implementing infinite lookahead.
The parser `try p <|> q` will try `q` even when
`p` has consumed input.

It is also useful for specifying both the lexer and parser
together.
```
    (do try (ch 'l' >> ch 'e' >> ch 't'), whitespace, ...)
    <|>
    ...
```
Without the `try` combinator we will not be able to backtrack on the `let` keyword.
-/

@[inline] def try (p : m α) : m α :=
map (λ m' inst β p, @parsec_t.try m' inst μ β p) p

/-- Parse `p` without consuming any input. -/
@[inline] def lookahead (p : m α) : m α :=
map (λ m' inst β p, @parsec_t.lookahead m' inst μ β p) p

/-- Faster version of `not_followed_by (satisfy p)` -/
@[inline] def not_followed_by_sat (p : char → bool) : m unit :=
do it ← left_over,
   if !it.has_next then pure ()
   else let c := it.curr in
       if p c then error (repr c)
       else pure ()

def eoi_error (it : iterator) (e : bool)  : result μ α :=
result.error it (mk_if e { unexpected := "end of input", custom := default _ }) ff

def curr : m char :=
string.iterator.curr <$> left_over

@[inline] def cond (p : char → bool) (t : m α) (e : m α) : m α :=
mcond (p <$> curr) t e

/--
If the next character `c` satisfies `p`, then
update position and return `c`. Otherwise,
generate error message with current position and character. -/
@[inline] def satisfy (p : char → bool) : m char :=
do it ← left_over,
   if !it.has_next then error "end of input"
   else let c := it.curr in
       if p c then lift $ λ _ _, result.ok c it.next none
       else error (repr c)

def ch (c : char) : m char :=
satisfy (= c)

def alpha : m char :=
satisfy char.is_alpha

def digit : m char :=
satisfy char.is_digit

def upper : m char :=
satisfy char.is_upper

def lower : m char :=
satisfy char.is_lower

def any : m char :=
satisfy (λ _, true)

private def str_aux : nat → iterator → iterator → option iterator
| 0     _    it := some it
| (n+1) s_it it :=
  if it.has_next ∧ s_it.curr = it.curr then str_aux n s_it.next it.next
  else none

/--
`str s` parses a sequence of elements that match `s`. Returns the parsed string (i.e. `s`).
This parser consumes no input if it fails (even if a partial match).
Note: The behaviour of this parser is different to that the `string` parser in the Parsec_t Μ M Haskell library,
as this one is all-or-nothing.
-/
def str (s : string) : m string :=
if s.is_empty then pure ""
else lift $ λ it e, match str_aux s.length s.mk_iterator it with
  | some it' := result.ok s it' none
  | none     := result.error it (mk_if e { expected := dlist.singleton (repr s), custom := none }) ff

private def take_aux : nat → string → iterator → bool → result μ string
| 0     r it _ := result.ok r it none
| (n+1) r it e :=
  if !it.has_next then eoi_error it e
  else take_aux n (r.push (it.curr)) it.next e

/-- Consume `n` characters. -/
def take (n : nat) : m string :=
if n = 0 then pure ""
else lift $ take_aux n ""

private def mk_string_result (r : string) (it : iterator) : result μ string :=
if r.is_empty then result.mk_eps r it
else result.ok r it none

@[specialize]
private def take_while_aux (p : char → bool) : nat → string → iterator → result μ string
| 0     r it := mk_string_result r it
| (n+1) r it :=
  if !it.has_next then mk_string_result r it
  else let c := it.curr in
       if p c then take_while_aux n (r.push c) it.next
       else mk_string_result r it

/--
Consume input as long as the predicate returns `tt`, and return the consumed input.
This parser does not fail. It will return an empty string if the predicate
returns `ff` on the current character. -/
@[specialize] def take_while (p : char → bool) : m string :=
lift $ λ it e, take_while_aux p it.remaining "" it

@[specialize] def take_while_cont (p : char → bool) (ini : string) : m string :=
lift $ λ it e, take_while_aux p it.remaining ini it

/--
Consume input as long as the predicate returns `tt`, and return the consumed input.
This parser requires the predicate to succeed on at least once. -/
@[specialize] def take_while1 (p : char → bool) : m string :=
do c ← satisfy p,
   take_while_cont p (to_string c)

/--
Consume input as long as the predicate returns `ff` (i.e. until it returns `tt`), and return the consumed input.
This parser does not fail. -/
@[inline] def take_until (p : char → bool) : m string :=
take_while (λ c, !p c)

@[inline] def take_until1 (p : char → bool) : m string :=
take_while1 (λ c, !p c)

private def mk_consumed_result (consumed : bool) (it : iterator) : result μ unit :=
if consumed then result.ok () it none
else result.mk_eps () it

@[specialize] private def take_while_aux' (p : char → bool) : nat → bool → iterator → result μ unit
| 0     consumed it := mk_consumed_result consumed it
| (n+1) consumed it :=
  if !it.has_next then mk_consumed_result consumed it
  else let c := it.curr in
       if p c then take_while_aux' n tt it.next
       else mk_consumed_result consumed it

/-- Similar to `take_while` but it does not return the consumed input. -/
@[specialize] def take_while' (p : char → bool) : m unit :=
lift $ λ it _, take_while_aux' p it.remaining ff it

/-- Similar to `take_while1` but it does not return the consumed input. -/
@[specialize] def take_while1' (p : char → bool) : m unit :=
satisfy p *> take_while' p

/-- Consume zero or more whitespaces. -/
@[noinline] def whitespace : m unit :=
take_while' char.is_whitespace

/-- Shorthand for `p <* whitespace` -/
@[inline] def lexeme (p : m α) : m α :=
p <* whitespace

/-- Parse a numeral in decimal. -/
@[noinline] def num : m nat :=
string.to_nat <$> (take_while1 char.is_digit)

/-- Succeed only if there are at least `n` characters left. -/
def ensure (n : nat) : m unit :=
do it ← left_over,
   if n ≤ it.remaining then pure ()
   else error "end of input" (dlist.singleton ("at least " ++ to_string n ++ " characters"))

/-- Return the current position. -/
def pos : m position :=
string.iterator.offset <$> left_over

@[inline] def not_followed_by [monad_except (message μ) m] (p : m α) (msg : string := "input") : m unit :=
do it ← left_over,
   b ← lookahead $ catch (p *> pure ff) (λ _, pure tt),
   if b then pure () else error msg dlist.empty it

def eoi : m unit :=
do it ← left_over,
   if it.remaining = 0 then pure ()
   else error (repr it.curr) (dlist.singleton ("end of input"))

@[specialize] def many1_aux [alternative m] (p : m α) : nat → m (list α)
| 0     := do a ← p, pure [a]
| (n+1) := do a ← p,
              as ← (many1_aux n <|> pure []),
              pure (a::as)

@[specialize] def many1 [alternative m] (p : m α) : m (list α) :=
do r ← remaining, many1_aux p r

@[specialize] def many [alternative m] (p : m α) : m (list α) :=
many1 p <|> pure []

@[specialize] def many1_aux' [alternative m] (p : m α) : nat → m unit
| 0     := p *> pure ()
| (n+1) := p *> (many1_aux' n <|> pure ())

@[inline] def many1' [alternative m] (p : m α) : m unit :=
do r ← remaining, many1_aux' p r

@[specialize] def many' [alternative m] (p : m α) : m unit :=
many1' p <|> pure ()

@[specialize] def sep_by1 [alternative m] (p : m α) (sep : m β) : m (list α) :=
(::) <$> p <*> many (sep *> p)

@[specialize] def sep_by [alternative m] (p : m α) (sep : m β) : m (list α) :=
sep_by1 p sep <|> pure []

@[specialize] def fix_aux [alternative m] (f : m α → m α) : nat → m α
| 0     := error "fix_aux: no progress"
| (n+1) := f (fix_aux n)

@[specialize] def fix [alternative m] (f : m α → m α) : m α :=
do n ← remaining, fix_aux f (n+1)

@[specialize] def foldr_aux [alternative m] (f : α → β → β) (p : m α) (b : β) : nat → m β
| 0     := pure b
| (n+1) := (f <$> p <*> foldr_aux n) <|> pure b

/-- Matches zero or more occurrences of `p`, and folds the result. -/
@[specialize] def foldr [alternative m] (f : α → β → β) (p : m α) (b : β) : m β :=
do it ← left_over,
   foldr_aux f p b it.remaining

@[specialize] def foldl_aux [alternative m] (f : α → β → α) (p : m β) : α → nat → m α
| a 0     := pure a
| a (n+1) := (do x ← p, foldl_aux (f a x) n) <|> pure a

/-- Matches zero or more occurrences of `p`, and folds the result. -/
@[specialize] def foldl [alternative m] (f : α → β → α) (a : α) (p : m β) : m α :=
do it ← left_over,
   foldl_aux f p a it.remaining

def unexpected (msg : string) : m α :=
error msg

def unexpected_at (msg : string) (it : iterator) : m α :=
error msg dlist.empty it

/- Execute all parsers in `ps` and return the result of the longest parse(s) if any,
   or else the result of the furthest error. If there are two parses of
   equal length, the first parse wins. -/
@[specialize]
def longest_match [monad_except (message μ) m] (ps : list (m α)) : m (list α) :=
do it ← left_over,
   e  ← msgs_enabled,
   r  ← ps.mfoldr (λ p (r : result μ (list α)),
     lookahead $ catch
       (do
         a ← p,
         it ← left_over,
         pure $ match r with
         | result.ok as it' none := if it'.offset > it.offset then r
             else if it.offset > it'.offset then result.ok [a] it none
             else result.ok (a::as) it none
         | _                     := result.ok [a] it none)
       (λ msg, pure $ match r with
           | result.error it' msg' _ := if it'.offset > msg.it.offset then r
             else if msg.it.offset > it'.offset then result.error msg.it msg.to_pre_message tt
             else result.error msg.it (mk_if e (merge msg.to_pre_message msg')) (msg.it.offset > it.offset)
           | _ := r))
    ((error "longest_match: empty list" : parsec _ _) it e),
    lift $ λ _ _, r

/-- Add trace information about `p`'s input and output. -/
def dbg (label : string) (p : m α) : m α :=
map (λ m' inst β, @parsec_t.dbg m' inst μ β label) p

@[specialize]
def observing [monad_except (message μ) m] (p : m α) : m (except (message μ) α) :=
catch (except.ok <$> p) $ λ msg, pure (except.error msg)

end monad_parsec

namespace monad_parsec
open parsec_t
variables {m : Type → Type} [monad m] [monad_parsec unit m] {α β : Type}

end monad_parsec

namespace parsec_t
open monad_parsec
variables {m : Type → Type} [monad m] {α β : Type}

def parse (p : parsec_t μ m α) (s : string) (msgs_enabled : bool := tt) (fname := "") : m (except (message μ) α) :=
run p s msgs_enabled fname

def parse_with_eoi (p : parsec_t μ m α) (s : string) (msgs_enabled : bool := tt) (fname := "") : m (except (message μ) α) :=
run (p <* eoi) s msgs_enabled fname

def parse_with_left_over (p : parsec_t μ m α) (s : string) (msgs_enabled : bool := tt) (fname := "") : m (except (message μ) (α × iterator)) :=
run (prod.mk <$> p <*> left_over) s msgs_enabled fname

end parsec_t

def parsec.parse {α : Type} (p : parsec μ α) (s : string) (msgs_enabled : bool := tt) (fname := "") : except (message μ) α :=
parsec_t.parse p s msgs_enabled fname

end parser
end lean
