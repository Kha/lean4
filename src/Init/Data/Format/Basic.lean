/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Control.State
import Init.Data.Int.Basic
import Init.Data.String.Basic

namespace Std.Format

/-- Default indentation. -/
def defIndent  := 2
def defUnicode := true
/-- Default width of the targeted output pane. -/
def defWidth   := 120

/-- Determines how groups should have linebreaks inserted when the
text would overfill its remaining space.

- `uniform` will make a linebreak on every `Format.softSep` in the group or none of them.
  ```
  [1,
   2,
   3]
  ```
- `fill` will only make linebreaks on as few `Format.softSep`s as possible:
  ```
  [1, 2,
   3]
  ```
-/
inductive GroupBehavior where
  | uniform
  | fill
  deriving Inhabited, BEq

/-- A string with pretty-printing information for rendering in a column-width-aware way.

The pretty-printing algorithm is based on Wadler's paper
[_A Prettier Printer_](https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf). -/
inductive _root_.Std.Format where
  /-- The empty format. -/
  | nil
  /-- A position where a newline may be inserted instead of `otherwise`
  if the current group does not fit within the allotted column width. -/
  | softBreak (otherwise : String := " ")
  /-- A node containing a plain string. -/
  | text (s : String)
  /-- `nest n f` tells the formatter that `f` is nested inside something with length `n`
  so that it is pretty-printed with the correct indentation on a line break.
  For example, we can define a formatter for list `l : List Format` as:

  ```
  let f := join <| l.intersperse <| ", " ++ Format.line
  group (nest 1 <| "[" ++ f ++ "]")
  ```

  This will be written all on one line, but if the text is too large,
  the formatter will put in linebreaks after the commas and indent later lines by 1.
  -/
  | indent (f : Format) (num : Int := defIndent)
  /-- Concatenation of two Formats. -/
  | append (f g : Format)
  /-- Creates a new flattening group for the given inner format.  -/
  | group (f : Format) (behavior : Format.GroupBehavior := .uniform)
  /-- Used for associating auxiliary information (e.g. `Expr`s) with `Format` objects. -/
  | tag (t : Nat) (f : Format)
  deriving Inhabited

/-- Check whether the given format contains no characters. -/
def isEmpty : Format → Bool
  | nil          => true
  | softBreak _  => false
  | text msg     => msg == ""
  | indent f _   => f.isEmpty
  | append f₁ f₂ => f₁.isEmpty && f₂.isEmpty
  | group f _    => f.isEmpty
  | tag _ f      => f.isEmpty

/-- Alias for a group with `GroupBehavior` set to `fill`. -/
def fill (f : Format) : Format :=
  group f (behavior := .fill)

@[deprecated] def line : Format := softBreak
@[deprecated] def nest (n : Int) (f : Format) := indent f n

instance : Append Format     := ⟨Format.append⟩
instance : Coe String Format := ⟨text⟩

def join (xs : List Format) : Format :=
  xs.foldl (·++·) ""

def isNil : Format → Bool
  | nil => true
  | _   => false

/-- Create a format `l ++ f ++ r` with a flatten group.
GroupBehavior is `uniform`; for `fill` use `bracketFill`. -/
@[inline] def bracket (l : String) (f : Format) (r : String) : Format :=
  group <| indent (num := l.length) <| l ++ f ++ r

/-- Creates the format `"(" ++ f ++ ")"` with a flattening group.-/
@[inline] def paren (f : Format) : Format :=
  bracket "(" f ")"

/-- Creates the format `"[" ++ f ++ "]"` with a flattening group.-/
@[inline] def sbracket (f : Format) : Format :=
  bracket "[" f "]"

/-- Same as `bracket` except uses the `fill` flattening behavior. -/
@[inline] def bracketFill (l : String) (f : Format) (r : String) : Format :=
  fill <| indent (num := l.length) <| l ++ f ++ r

/-- Nest with the default indentation amount.-/
@[deprecated] def nestD (f : Format) : Format := indent f

/-- Inserts a newline and then `f` indented by the default amount. -/
def indentD (f : Format) : Format :=
  indent (softBreak ++ f)

end Format

/-- Class for converting a given type α to a `Format` object for pretty-printing.
See also `Repr`, which also outputs a `Format` object. -/
class ToFormat (α : Type u) where
  format : α → Format

export ToFormat (format)

-- note: must take precedence over the above instance to avoid premature formatting
instance : ToFormat Format where
  format f := f

instance : ToFormat String where
  format s := Format.text s

/-- Intersperse the given list (each item printed with `format`) with the given `sep` format. -/
def Format.joinSep {α : Type u} [ToFormat α] : List α → Format → Format
  | [],    _   => nil
  | [a],   _   => format a
  | a::as, sep => format a ++ sep ++ joinSep as sep

/-- Format each item in `items` and prepend prefix `pre`. -/
def Format.prefixJoin {α : Type u} [ToFormat α] (pre : Format) : List α → Format
  | []    => nil
  | a::as => pre ++ format a ++ prefixJoin pre as

/-- Format each item in `items` and append `suffix`. -/
def Format.joinSuffix {α : Type u} [ToFormat α] : List α → Format → Format
  | [],    _      => nil
  | a::as, suffix => format a ++ suffix ++ joinSuffix as suffix

end Std
