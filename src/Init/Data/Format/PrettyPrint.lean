/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich, Lars König
-/
prelude
import Init.Data.Format.Basic
import Init.Data.Array.Basic
import Init.Data.Range
import Init.NotationExtra

namespace Std

/- `Format` with explicit indentation, hard line breaks, and flattened `append`s. -/
private inductive ResolvedFormat
  /- Hard line break with indent `indent`. -/
  | hardBreak (indent : Nat)
  /- may not contain `\n`. -/
  | text (s : String)
  | softBreak (s : String) (indent : Nat)
  | group (behavior : Option Format.GroupBehavior) (fmts : Array ResolvedFormat)
  | tag (t : Nat) (f : ResolvedFormat)
  deriving Inhabited

partial def Format.resolve (f : Format) (indent := 0) : ResolvedFormat :=
  .group none (go indent f)
where
  go (indent : Int) : Format → Array ResolvedFormat
  | .nil              => #[]
  | .text s =>
    s.split (· == '\n') |>.map .text |>.intersperse (.hardBreak indent.toNat) |>.toArray
  | .append a b       => go indent a |>.appendCore (go indent b)
  | .softBreak s      => #[.softBreak s indent.toNat]
  | .indent f n       => go (indent + n) f
  | .group f behavior => #[.group behavior (go indent f)]
  | .tag t f          => #[.tag t (.group (some .uniform) (go indent f))]

/-- A monad in which we can pretty-print `Format` objects. -/
class MonadPrettyFormat (m : Type → Type) where
  pushText (s : String)      : m Unit
  pushNewline (indent : Nat) : m Unit
  currColumn                 : m Nat
  withTag (t : Nat)          : m α → m α
open MonadPrettyFormat

/- Measures the length of the given format, but stops when the current line is exceeded.
Requires `currentColumn` to be less than `width`. -/
variable (width : Nat) in
private partial def measureFlatUpToWidth : ResolvedFormat → StateM Nat Unit
  | .hardBreak _ =>
    set width  -- never fits in line
  | .text s =>
    modify (· + s.length)
  | .softBreak s _ =>
    measureFlatUpToWidth <| .text s
  | .group _ fmts => do
    for fmt in fmts do
      measureFlatUpToWidth fmt
      if (← get) ≥ width then
        break
  | .tag _ f => measureFlatUpToWidth f

/- Fits as many formats on the current line as possible and returns them together with the remaining formats. -/
private def fillLine (currColumn : Nat) (width : Nat) (fmts : Array ResolvedFormat) :
    Array ResolvedFormat × Array ResolvedFormat := Id.run <| StateT.run' (s := currColumn) do
  for i in [0:fmts.size] do
    let f := fmts[i]!
    measureFlatUpToWidth width f
    if (← get) >= width then
      return fmts.splitAt i
  return (fmts, #[])

variable (width : Nat) in
private partial def ResolvedFormat.prettyM [Monad m] [MonadPrettyFormat m] (flatten : Bool) : ResolvedFormat → m Unit
  | .hardBreak indent => pushNewline indent
  | .text s => pushText s
  | .tag t f => withTag t (prettyM flatten f)
  | .softBreak s indent => do
    -- whether separators are flattened is decided on the group level
    if flatten then
      pushText s
    else
      pushNewline indent
  | .group behavior fmts => do
    if behavior.isNone then
      fmts.forM (prettyM false)
    else if flatten then
      -- we already know that the entire flattened group will fit in the current line
      fmts.forM (prettyM true)
    else
      -- make sure the group is non-empty
      if fmts.isEmpty then
        return ()

      -- try to fit as many parts of the flattened group in the current line
      let (line, rest) := fillLine (← currColumn) width fmts
      if rest.isEmpty then
        -- entire group fits
        fmts.forM (prettyM true)
      else
        -- only some parts of the group fit
        match behavior with
        | none => unreachable!
        | some .uniform =>
          -- do not flatten any separators
          fmts.forM (prettyM false)
        | some .fill =>
          -- flatten the parts of the group that fit in the current line
          line.forM (prettyM true)
          prettyM false rest[0]!
          -- continue with the rest of the group
          prettyM false <| .group behavior (rest.extract 1 rest.size)

def Format.prettyM [Monad m] [MonadPrettyFormat m] (fmt : Format) (width : Nat := defWidth) (indent := 0) : m Unit :=
  fmt.resolve indent |>.prettyM width false

-- default instances for `PrettyMonad`
structure StringPrettyState where
  out : String := ""
  currColumn : Nat := 0

instance : MonadPrettyFormat (StateM StringPrettyState) where
  pushNewline indent := modify fun st =>
    { st with
      out := st.out ++ "\n" ++ "".pushn ' ' indent
      currColumn := indent }
  pushText s := modify fun st =>
    { st with
      out := st.out ++ s
      currColumn := st.currColumn + s.length }
  currColumn := do return (← get).currColumn
  withTag _ := id

@[export lean_format_pretty]
def Format.pretty (fmt : Format) (width : Nat := defWidth) : String :=
  (fmt.prettyM width : StateM StringPrettyState Unit) |>.run {} |>.2.out

instance : ToString Format where
  toString f := f.pretty
