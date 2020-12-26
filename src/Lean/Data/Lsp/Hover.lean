/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Data.Json
import Lean.Data.Lsp.Basic

/-! Handling of mouse hover requests. -/

namespace Lean
namespace Lsp

open Json

structure Hover where
  /- NOTE we should also accept MarkedString/MarkedString[] here
  but they are deprecated, so maybe can get away without. -/
  contents : MarkupContent
  range? : Option Range := none
  deriving ToJson, FromJson

structure HoverParams extends TextDocumentPositionParams

instance : FromJson HoverParams := ⟨fun j => do
  let tdpp ← @fromJson? TextDocumentPositionParams _ j
  pure ⟨tdpp⟩⟩

instance : ToJson HoverParams :=
  ⟨fun o => toJson o.toTextDocumentPositionParams⟩

end Lsp
end Lean
