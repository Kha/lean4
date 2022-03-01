/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Lars König

The string fuzzy matching algorithm in this file is based on the algorithm
used in LLVM with some modifications. The LLVM algorithm itself is based on VS
code's client side filtering algorithm.
-/

namespace Lean
namespace FuzzyMatching

/- Represents the type of a single character. -/
inductive CharType where
  | lower | upper | separator

def charType (c : Char) : CharType :=
  if c.isAlphanum then
    if c.isUpper
      then CharType.upper
      else CharType.lower
  else
    CharType.separator


/- Represents the role of a character inside a word. -/
inductive CharRole where
  | head | tail | separator

def charRole (prev? : Option CharType) (curr : CharType) (next?: Option CharType) : CharRole :=
  if curr matches CharType.separator then
    CharRole.separator
  else if prev?.isNone || prev? matches some CharType.separator then
    CharRole.head
  else if curr matches CharType.lower then
    CharRole.tail
  else if prev? matches some CharType.upper && !(next? matches some CharType.lower) then
    CharRole.tail
  else
    CharRole.head


private def iterateLookaround (f : α → (Option Char × Char × Option Char) → α) (init : α) (string : String) : α :=
  if string.isEmpty then
    init
  else if string.length == 1 then
    f init (none, string.get 0, none)
  else Id.run <| do
    let mut prev? := none
    let mut curr := string.get 0

    let mut res := init
    for i in [1:string.bsize] do
      let next := string.get i
      res := f res (prev?, curr, some next)

      prev? := some curr
      curr := next
    f res (prev?, curr, none)


/- Combines different information about a character. -/
private structure CharInfo where
  char : Char
  role : CharRole

/- Add additional information to each character in a string and return the
resulting list in reverse order. -/
private def reverseStringInfo (s : String) : List CharInfo :=
  iterateLookaround (string := s) (init := []) fun res (prev?, curr, next?) =>
    ⟨curr, charRole (prev?.map charType) (charType curr) (next?.map charType)⟩ :: res


private def containsInOrderLower (a b : String) : Bool := Id.run <| do
  if a.isEmpty then
    return true
  let mut aIt := a.mkIterator
  for i in [:b.bsize] do
    if aIt.curr.toLower == (b.get i).toLower then
      aIt := aIt.next
      if !aIt.hasNext then
        return true
  return false


/- Contains the best possible scores when skipping or matching the last
seen character.

`none`       - no possible match was found
`some score` - possible match, quality is indicated by score -/
private structure MatchResult where
  MissScore? : Option Int
  MatchScore? : Option Int
  deriving Inhabited

private def selectBest : MatchResult → Option Int
  | ⟨missScore, none⟩  => missScore
  | ⟨none, matchScore⟩ => matchScore
  | ⟨some missScore, some matchScore⟩ =>
    some <| max missScore matchScore

/- Match the given pattern with the given word. The algorithm uses dynamic
programming to find the best scores and requires the pattern and the word in
reverse order.

In addition to the current characters in the pattern and the word, the
algorithm can use different scores for the last operation using the two scores
in match result. This is necessary to give consecutive character matches a
bonus.

`patternComplete` is necessary to know when we are behind the match in the
word. -/
private partial def fuzzyMatchRec (pattern word : List CharInfo) (patternComplete := true) : MatchResult :=
  match (pattern, word) with
  | ([], [])       => ⟨some 0, none⟩
  | ((_ :: _), []) => ⟨none, none⟩
  | ([], (_ :: _)) =>
    if patternComplete then ⟨some 0, none⟩ else
      -- this is a more efficient implementation of a fold over `word` using `skipPenalty`
      -- the `+2` is a correction for the first character of the word
      -- (`wordStart` instead of `CharRole.head`)
      ⟨some <| Int.neg <| Int.ofNat <| (·.length + 2) <| word.filter (·.role matches CharRole.head), none⟩
  | ((ph :: pt), (wh :: wt)) =>
    let missScore? := fuzzyMatchRec pattern wt patternComplete |> selectBest |>.map (· - skipPenalty wh patternComplete wt.isEmpty)

    let matchScore? := if ph.char.toLower != wh.char.toLower then none else
      let matchScores := fuzzyMatchRec pt wt false
      selectBest ⟨
        matchScores.MissScore?.map (· + matchResult ph wh false wt.isEmpty),
        matchScores.MatchScore?.map (· + matchResult ph wh true wt.isEmpty)
      ⟩

    ⟨missScore?, matchScore?⟩

  where
    /- Heuristic to penalize skipping characters in the word. -/
    skipPenalty (wh : CharInfo) (patternComplete : Bool) (wordStart : Bool) : Int := Id.run <| do
      /- Skipping characters if the match is already completed is free. -/
      if patternComplete then
        return 0
      /- Skipping the beginning of the word. -/
      if wordStart then
        return 3
      /- Skipping the beginning of a segment. -/
      if wh.role matches CharRole.head then
        return 1

      return 0

    /- Heuristic to rate a match or `none` if the characters do not match. -/
    matchResult (ph wh : CharInfo) (consecutive : Bool) (wordStart : Bool) : Int := Id.run <| do
      let mut score := 1
      /- Case-sensitive equality or beginning of a segment in pattern and word. -/
      if ph.char == wh.char || (ph.role matches CharRole.head && wh.role matches CharRole.head) then
        score := score + 1
      /- Beginning of the word or consecutive character match. -/
      if wordStart || consecutive then
        score := score + 2
      /- Match starts in the middle of a segment. -/
      if wh.role matches CharRole.tail && !consecutive then
        score := score - 3
      /- Beginning of a segment in the pattern is not aligned with the
      beginning of a segment in the word. -/
      if ph.role matches CharRole.head && wh.role matches CharRole.tail then
        score := score - 1

      return score

/- Match the given pattern with the given word using a fuzzy matching
algorithm. The resulting scores are in the interval `[0, 1]` or `none` if no
match was found. -/
def fuzzyMatchScore? (pattern word : String) : Option Float := Id.run <| do
  /- Some fast and simple checks. -/
  if pattern.length > word.length then
    return none
  if !(containsInOrderLower pattern word) then
    return none

  let some score := selectBest <| fuzzyMatchRec (reverseStringInfo pattern) (reverseStringInfo word)
    | none
  let mut score := score

  /- Bonus if every character is matched. -/
  if pattern.length == word.length then
    score := score * 2

  /- Perfect score per character given the heuristic in `matchResult`. -/
  let perfect := 4
  let normScore := Float.ofInt score / Float.ofInt (perfect * pattern.length)

  return some <| min 1 (max 0 normScore)

/- Match the given pattern with the given word using a fuzzy matching
algorithm. Return `false` if no match was found or the found match received a
score below the given threshold. -/
def fuzzyMatch (pattern word : String) (threshold := 0.2) : Bool :=
  match fuzzyMatchScore? pattern word with
  | none       => false
  | some score => score > threshold

end FuzzyMatching
end Lean
