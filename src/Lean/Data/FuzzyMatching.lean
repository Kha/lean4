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
  deriving Inhabited

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


private def iterateLookaround (f : (Option Char × Char × Option Char) → α) (string : String) : Array α :=
  if string.isEmpty then
    #[]
  else if string.length == 1 then
    #[f (none, string.get 0, none)]
  else Id.run <| do
    let mut result := Array.mkEmpty string.length

    let mut prev? := none
    let mut curr := string.get 0

    for i in [1:string.length] do
      let next := string.get i
      result := result.push <| f (prev?, curr, some next)

      prev? := some curr
      curr := next
    result.push <| f (prev?, curr, none)


/- Add additional information to each character in a string and return the
resulting list in reverse order. -/
private def stringInfo (s : String) : Array CharRole :=
  iterateLookaround (string := s) fun (prev?, curr, next?) =>
    charRole (prev?.map charType) (charType curr) (next?.map charType)


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
private def fuzzyMatchCore (pattern word : String) (patternRoles wordRoles : Array CharRole) (patternComplete := true) : MatchResult := Id.run <| do
  let mut result : Array MatchResult := Array.mkEmpty ((pattern.length + 1) * (word.length + 1))

  result := result.push ⟨some 0, none⟩

  let mut penalty := 0
  for wordIdx in [:word.length] do
    penalty := penalty - skipPenalty (wordRoles.get! wordIdx) false (wordIdx == 0)
    result := result.push ⟨some penalty, none⟩

  for patternIdx in [:pattern.length] do
    result := result.push ⟨none, none⟩

    let patternComplete := patternIdx == pattern.length - 1

    for wordIdx in [:word.length] do
      if wordIdx < patternIdx then
        result := result.push ⟨none, none⟩
      else
        let missScore? :=
          getPrevMiss result patternIdx wordIdx
          |> selectBest
          |>.map (· - skipPenalty (wordRoles.get! wordIdx) patternComplete (wordIdx == 0))

        let matchScore? :=
          if allowMatch (pattern.get patternIdx) (word.get wordIdx) (patternRoles.get! patternIdx) (wordRoles.get! wordIdx) then
            let matchScores := getPrevMatch result patternIdx wordIdx
            selectBest ⟨
              matchScores.MissScore?.map (· + matchResult
                (pattern.get patternIdx) (word.get wordIdx)
                (patternRoles.get! patternIdx) (wordRoles.get! wordIdx)
                false
                (wordIdx == 0)
              ),
              matchScores.MatchScore?.map (· + matchResult
                (pattern.get patternIdx) (word.get wordIdx)
                (patternRoles.get! patternIdx) (wordRoles.get! wordIdx)
                true
                (wordIdx == 0)
              )
            ⟩
          else none

        result := result.push ⟨missScore?, matchScore?⟩

  return result.get! (result.size - 1)

  where
    getPrevMiss (result : Array MatchResult) (patternIdx wordIdx : Nat) : MatchResult :=
      let patternIdx := patternIdx + 1
      let idx := patternIdx * (word.length + 1) + wordIdx
      result.get! idx

    getPrevMatch (result : Array MatchResult) (patternIdx wordIdx : Nat) : MatchResult :=
      let idx := patternIdx * (word.length + 1) + wordIdx
      result.get! idx

    /- Heuristic to penalize skipping characters in the word. -/
    skipPenalty (wordRole : CharRole) (patternComplete : Bool) (wordStart : Bool) : Int := Id.run <| do
      /- Skipping characters if the match is already completed is free. -/
      if patternComplete then
        return 0
      /- Skipping the beginning of the word. -/
      if wordStart then
        return 3
      /- Skipping the beginning of a segment. -/
      if wordRole matches CharRole.head then
        return 1

      return 0

    /- Whether characters from the pattern and the word match. -/
    allowMatch (patternChar wordChar : Char) (patternRole wordRole : CharRole) : Bool := Id.run <| do
      /- Different characters do not match. -/
      if patternChar.toLower != wordChar.toLower then
        return false
      /- The beginning of a segment in the pattern must align with the beginning of a segment in the word. -/
      if patternRole matches CharRole.head && !(wordRole matches CharRole.head) then
        return false

      return true

    /- Heuristic to rate a match. -/
    matchResult (patternChar wordChar : Char) (patternRole wordRole : CharRole) (consecutive : Bool) (wordStart : Bool) : Int := Id.run <| do
      let mut score := 1
      /- Case-sensitive equality or beginning of a segment in pattern and word. -/
      if patternChar == wordChar || (patternRole matches CharRole.head && wordRole matches CharRole.head) then
        score := score + 1
      /- Beginning of the word or consecutive character match. -/
      if wordStart || consecutive then
        score := score + 2
      /- Match starts in the middle of a segment. -/
      if wordRole matches CharRole.tail && !consecutive then
        score := score - 3
      /- Beginning of a segment in the pattern is not aligned with the
      beginning of a segment in the word. -/
      if patternRole matches CharRole.head && wordRole matches CharRole.tail then
        score := score - 1

      return score

/- Match the given pattern with the given word using a fuzzy matching
algorithm. The resulting scores are in the interval `[0, 1]` or `none` if no
match was found. -/
def fuzzyMatchScore? (pattern word : String) : Option Float := Id.run <| do
  /- Some fast and simple checks. -/
  if pattern.isEmpty then
    return some 1
  if pattern.length > word.length then
    return none
  if !(containsInOrderLower pattern word) then
    return none

  let result := fuzzyMatchCore pattern word (stringInfo pattern) (stringInfo word)
  let some score := selectBest <| result
    | none
  let mut score := score

  /- Bonus if every character is matched. -/
  if pattern.length == word.length then
    score := score * 2

  /- Perfect score per character given the heuristic in `matchResult`. -/
  let perfect := 4
  let normScore := Float.ofInt score / Float.ofInt (perfect * pattern.length)

  return some <| min 1 (max 0 normScore)

def fuzzyMatchScoreWithThreshold? (pattern word : String) (threshold := 0.2) : Option Float :=
  let score? := fuzzyMatchScore? pattern word
  score?.bind fun score => if score > threshold then some score else none

/- Match the given pattern with the given word using a fuzzy matching
algorithm. Return `false` if no match was found or the found match received a
score below the given threshold. -/
def fuzzyMatch (pattern word : String) (threshold := 0.2) : Bool :=
  fuzzyMatchScoreWithThreshold? pattern word threshold |>.isSome

end FuzzyMatching
end Lean
