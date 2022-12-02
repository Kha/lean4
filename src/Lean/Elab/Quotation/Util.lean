/-
Copyright (c) 2020 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Lean.Elab.Term

namespace Lean.Elab.Term.Quotation
open Lean.Syntax

register_builtin_option hygiene : Bool := {
  defValue := true
  descr    := "Annotate identifiers in quotations such that they are resolved relative to the scope at their declaration, not that at their eventual use/expansion, to avoid accidental capturing. Note that quotations/notations already defined are unaffected."
}

def getAntiquotationIds (stx : Syntax) : TermElabM (Array Ident) := do
  let mut ids := #[]
  for stx in stx.topDown (firstChoiceOnly := true) do
    if (isAntiquot stx || isTokenAntiquot stx) && !isEscapedAntiquot stx then
      let anti := getAntiquotTerm stx
      if anti.isIdent then ids := ids.push ⟨anti⟩
      else if anti.isOfKind ``Parser.Term.hole then pure ()
      else throwErrorAt stx "complex antiquotation not allowed here"
  return ids

/-- Get all pattern vars (as `Syntax.ident`s) in `stx` -/
partial def getPatternVars (stx : Syntax) : TermElabM (Array Syntax) :=
  if stx.isQuot then
    getAntiquotationIds stx
  else match stx with
    | `(_)            => return #[]
    | `($id:ident)    => return #[id]
    | `($id:ident@$e) => return (← getPatternVars e).push id
    | _               => throwErrorAt stx "unsupported pattern in syntax match{indentD stx}"

def getPatternsVars (pats : Array Syntax) : TermElabM (Array Syntax) :=
  pats.foldlM (fun vars pat => do return vars ++ (← getPatternVars pat)) #[]

/--
Given an antiquotation like `$e:term` (i.e. `Syntax.antiquotKind?` returns `some`),
returns the `"term"` atom if present.
-/
def getAntiquotKindSpec? (antiquot : Syntax) : Option Syntax :=
  let name := antiquot[3][1]
  if name.isMissing then none else some name

def resolveSectionVariable (sectionVars : NameMap Name) (id : Name) : List (Name × List String) :=
  -- decode macro scopes from name before recursion
  let extractionResult := extractMacroScopes id
  let rec loop : Name → List String → List (Name × List String)
    | id@(.str p s), projs =>
      -- NOTE: we assume that macro scopes always belong to the projected constant, not the projections
      let id := { extractionResult with name := id }.review
      match sectionVars.find? id with
      | some newId => [(newId, projs)]
      | none       => loop p (s::projs)
    | _, _ => []
  loop extractionResult.name []

/--
Extends the identifier's list of preresolved names with resolutions from the current scope,
unless the `hygiene` option is off.
-/
def preresolveIdent [Monad m] [MonadOptions m] [MonadResolveName m] [MonadEnv m] [MonadError m] (sectionVars : NameMap Name) :
    Ident → m (List Preresolved)
  | ⟨Syntax.ident _ _ val preresolved⟩ => do
    if !hygiene.get (← getOptions) then
      return preresolved
    let consts ← resolveGlobalName val
    -- extension of the paper algorithm: also store unique section variable names as top-level scopes
    -- so they can be captured and used inside the section, but not outside
    let sectionVars := resolveSectionVariable sectionVars val
    -- extension of the paper algorithm: resolve namespaces as well
    let namespaces ← resolveNamespaceCore (allowEmpty := true) val
    let preresolved := (consts ++ sectionVars).map (fun (n, projs) => Preresolved.decl n projs) ++
      namespaces.map .namespace ++
      preresolved
    return preresolved
  | _ => unreachable!

end Lean.Elab.Term.Quotation
