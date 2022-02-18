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

def charRole (prev? : Option CharType) (curr : CharType) : CharRole :=
  if curr matches CharType.separator then
    CharRole.separator
  else if prev? matches none || prev? matches some CharType.separator then
    CharRole.head
  else if curr matches CharType.lower then
    CharRole.tail
  else if prev? matches some CharType.upper then
    CharRole.tail
  else
    CharRole.head


/- Combines different information about a character. -/
private structure CharInfo where
  char : Char
  charLower : Char
  type : CharType
  role : CharRole

/- Add additional information to each character in a string and return the
resulting list in reverse order. -/
private def reverseStringInfo (s : String) : List CharInfo :=
  s.toList.foldl (init := (none, [])) (fun (prev, res) curr => (
    some curr,
    ⟨curr, curr.toLower, charType curr, charRole (prev.map charType) (charType curr)⟩ :: res
  )) |>.2


private def Option.map₂ (f : α → β → γ) : Option α × Option β → Option γ
  | (a?, b?) => a?.bind fun a => b?.map fun b => f a b

private def containsInOrder (a b : String) : Bool := Id.run do
  let mut aIt := a.mkIterator
  let mut bIt := b.mkIterator
  for _ in [:b.bsize] do
    if aIt.curr == bIt.curr then
      aIt := aIt.next
      if !aIt.hasNext then
        return true
    bIt := bIt.next
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
  | ([], (wh :: wt)) =>
    ⟨fuzzyMatchRec [] wt patternComplete |>.MissScore? |>.map (· - skipPenalty wh patternComplete wt.isEmpty), none⟩
  | ((ph :: pt), (wh :: wt)) =>
    let missScore := fuzzyMatchRec pattern wt patternComplete |> selectBest |>.map (· - skipPenalty wh patternComplete wt.isEmpty)

    let matchScores := fuzzyMatchRec pt wt false
    let matchScore := selectBest ⟨
      (matchScores.MissScore?, matchResult ph wh false wt.isEmpty) |> Option.map₂ (· + ·),
      (matchScores.MatchScore?, matchResult ph wh true wt.isEmpty) |> Option.map₂ (· + ·)
    ⟩

    ⟨missScore, matchScore⟩

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
    matchResult (ph wh : CharInfo) (consecutive : Bool) (wordStart : Bool) : Option Int := Id.run <| do
      /- Different characters. -/
      if ph.charLower != wh.charLower then
        return none

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

      return some score

/- Match the given pattern with the given word using a fuzzy matching
algorithm. The resulting scores are in the interval `[0, 1]` or `none` if no
match was found. -/
def fuzzyMatchScore? (pattern word : String) : Option Float := Id.run <| do
  /- Some fast and simple checks. -/
  if pattern.length == 0 then
    return some 0
  if pattern.length > word.length then
    return none
  if !(containsInOrder pattern.toLower word.toLower) then
    return none

  let mut score := selectBest <| fuzzyMatchRec (reverseStringInfo pattern) (reverseStringInfo word)
  /- Bonus if every character is matched. -/
  if pattern.length == word.length then
    score := score.map (· * 2)

  /- Perfect score per character given the heuristic in `matchResult`. -/
  let perfect := 4
  let normScore := score.map (Float.ofInt · / Float.ofInt (perfect * pattern.length))

  return normScore.map fun s => min 1 (max 0 s)

/- Match the given pattern with the given word using a fuzzy matching
algorithm. Return `false` if no match was found or the found match received a
score below the given threshold. -/
def fuzzyMatch (pattern word : String) (threshold := 0.2) : Bool :=
  match fuzzyMatchScore? pattern word with
  | none       => false
  | some score => score > threshold

end FuzzyMatching
end Lean
