/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Command
import Lean.Parser.Syntax
import Lean.Elab.Util

namespace Lean.Elab.Term
/-
Expand `optional «precedence»` where
 «precedence» := leading_parser " : " >> precedenceParser -/
def expandOptPrecedence (stx : Syntax) : MacroM (Option Nat) :=
  if stx.isNone then
    return none
  else
    return some (← evalPrec stx[0][1])

private def mkParserSeq (ds : Array Syntax) : TermElabM Syntax := do
  if ds.size == 0 then
    throwUnsupportedSyntax
  else if ds.size == 1 then
    pure ds[0]
  else
    let mut r := ds[0]
    for d in ds[1:ds.size] do
      r ← ``(Parser.andthen $r $d)
    return r

structure ToParserDescrContext where
  catName  : Name
  first    : Bool
  leftRec  : Bool -- true iff left recursion is allowed
  /- See comment at `Parser.ParserCategory`. -/
  behavior : Parser.LeadingIdentBehavior

abbrev ToParserDescrM := ReaderT ToParserDescrContext (StateRefT (Option Nat) TermElabM)
private def markAsTrailingParser (lhsPrec : Nat) : ToParserDescrM Unit := set (some lhsPrec)

@[inline] private def withNotFirst {α} (x : ToParserDescrM α) : ToParserDescrM α :=
  withReader (fun ctx => { ctx with first := false }) x

@[inline] private def withNestedParser {α} (x : ToParserDescrM α) : ToParserDescrM α :=
  withReader (fun ctx => { ctx with leftRec := false, first := false }) x

def checkLeftRec (stx : Syntax) : ToParserDescrM Bool := do
  let ctx ← read
  unless ctx.first && stx.getKind == ``Lean.Parser.Syntax.cat do
    return false
  let cat := stx[0].getId.eraseMacroScopes
  unless cat == ctx.catName do
    return false
  let prec? ← liftMacroM <| expandOptPrecedence stx[1]
  unless ctx.leftRec do
    throwErrorAt stx[3] "invalid occurrence of '{cat}', parser algorithm does not allow this form of left recursion"
  markAsTrailingParser (prec?.getD 0)
  return true

/--
  Given a `stx` of category `syntax`, return a pair `(newStx, lhsPrec?)`,
  where `newStx` is of category `term`. After elaboration, `newStx` should have type
  `TrailingParserDescr` if `lhsPrec?.isSome`, and `ParserDescr` otherwise. -/
partial def toParserDescr (stx : Syntax) (catName : Name) : TermElabM (Syntax × Option Nat) := do
  let env ← getEnv
  let behavior := Parser.leadingIdentBehavior env catName
  (process stx { catName := catName, first := true, leftRec := true, behavior := behavior }).run none
where
  process (stx : Syntax) : ToParserDescrM Syntax := withRef stx do
    let kind := stx.getKind
    if kind == nullKind then
      processSeq stx
    else if kind == choiceKind then
      process stx[0]
    else if kind == ``Lean.Parser.Syntax.paren then
      process stx[1]
    else if kind == ``Lean.Parser.Syntax.cat then
      processNullaryOrCat stx
    else if kind == ``Lean.Parser.Syntax.unary then
      processUnary stx
    else if kind == ``Lean.Parser.Syntax.binary then
      processBinary stx
    else if kind == ``Lean.Parser.Syntax.atom then
      processAtom stx
    else
      let stxNew? ← liftM (liftMacroM (expandMacro? stx) : TermElabM _)
      match stxNew? with
      | some stxNew => process stxNew
      | none => throwErrorAt stx "unexpected syntax kind of category `syntax`: {kind}"

  /- Sequence (aka NullNode) -/
  processSeq (stx : Syntax) := do
    let args := stx.getArgs
    if (← checkLeftRec stx[0]) then
      if args.size == 1 then throwErrorAt stx "invalid atomic left recursive syntax"
      let args := args.eraseIdx 0
      let args ← args.mapM fun arg => withNestedParser do process arg
      mkParserSeq args
    else
      let args ← args.mapIdxM fun i arg => withReader (fun ctx => { ctx with first := ctx.first && i.val == 0 }) do process arg
      mkParserSeq args

  processNullaryOrCat (stx : Syntax) := do
    match stx[1].getOptional? with
    | none => return stx[0]
    | some prec =>
      let prec? ← liftMacroM <| expandOptPrecedence stx[1]
      let prec := prec?.getD 0
      `($(stx[0]) $(quote prec))

  processUnary (stx : Syntax) := do
    let p ← withNestedParser do process stx[2]
    `($(stx[0]) $p)

  processBinary (stx : Syntax) := do
    let p₁ ← withNestedParser do process stx[2]
    let p₂ ← withNestedParser do process stx[4]
    `($(stx[0]) $p₁ $p₂)

  isValidAtom (s : String) : Bool :=
    !s.isEmpty &&
    s[0] != '\'' &&
    s[0] != '\"' &&
    !(s[0] == '`' && (s.endPos == ⟨1⟩ || isIdFirst s[⟨1⟩] || isIdBeginEscape s[⟨1⟩])) &&
    !s[0].isDigit

  processAtom (stx : Syntax) := do
    match stx[0].isStrLit? with
    | some atom =>
      unless isValidAtom atom do
        throwErrorAt stx "invalid atom"
      /- For syntax categories where initialized with `LeadingIdentBehavior` different from default (e.g., `tactic`), we automatically mark
         the first symbol as nonReserved. -/
      if (← read).behavior != Parser.LeadingIdentBehavior.default && (← read).first then
        ``(Parser.nonReservedSymbol $(quote atom))
      else
        ``(Parser.symbol $(quote atom))
    | none => throwUnsupportedSyntax

end Term

namespace Command
open Lean.Syntax
open Lean.Parser.Term hiding macroArg
open Lean.Parser.Command

private def declareSyntaxCatQuotParser (catName : Name) : CommandElabM Unit := do
  if let Name.str _ suffix _ := catName then
    let quotSymbol := "`(" ++ suffix ++ "|"
    let name := catName ++ `quot
    -- TODO(Sebastian): this might confuse the pretty printer, but it lets us reuse the elaborator
    let kind := ``Lean.Parser.Term.quot
    let cmd ← `(
      @[termParser] def $(mkIdent name) : Parser.Parser :=
        Parser.leadingNode $(quote kind) $(quote Parser.maxPrec)
          (Parser.andthen (Parser.symbol $(quote quotSymbol))
            (Parser.andthen
              (Parser.categoryParser $(quote catName) 0)
              (Parser.symbol ")"))))
    elabCommand cmd

@[builtinCommandElab syntaxCat] def elabDeclareSyntaxCat : CommandElab := fun stx => do
  let catName  := stx[1].getId
  let catBehavior :=
    if stx[2].isNone then
      Parser.LeadingIdentBehavior.default
    else if stx[2][3].getKind == ``Parser.Command.catBehaviorBoth then
      Parser.LeadingIdentBehavior.both
    else
      Parser.LeadingIdentBehavior.symbol
  let attrName := catName.appendAfter "Parser"
  let env ← getEnv
  let env ← Parser.registerParserCategory env attrName catName catBehavior
  setEnv env
  elabCommand (← `(def $(mkIdent catName):ident (rbp := 0) : Parser.Parser := Parser.categoryParser $(quote catName) rbp))
  declareSyntaxCatQuotParser catName

/--
  Auxiliary function for creating declaration names from parser descriptions.
  Example:
  Given
  ```
  syntax term "+" term : term
  syntax "[" sepBy(term, ", ") "]"  : term
  ```
  It generates the names `term_+_` and `term[_,]`
-/
partial def mkNameFromParserSyntax (catName : Name) (stx : Syntax) : MacroM Name := do
  mkUnusedBaseName <| Name.mkSimple <| appendCatName <| visit stx ""
where
  visit (stx : Syntax) (acc : String) : String :=
    match stx.isStrLit? with
    | some val => acc ++ (val.trim.map fun c => if c.isWhitespace then '_' else c).capitalize
    | none =>
      match stx with
      | Syntax.node _ k args =>
        if k == ``Lean.Parser.Syntax.cat then
          acc ++ "_"
        else
          args.foldl (init := acc) fun acc arg => visit arg acc
      | Syntax.ident ..    => acc
      | Syntax.atom ..     => acc
      | Syntax.missing     => acc

  appendCatName (str : String) :=
    match catName with
    | Name.str _ s _ => s ++ str
    | _ => str

/- We assume a new syntax can be treated as an atom when it starts and ends with a token.
   Here are examples of atom-like syntax.
   ```
   syntax "(" term ")" : term
   syntax "[" (sepBy term ",") "]" : term
   syntax "foo" : term
   ```
 -/
private partial def isAtomLikeSyntax (stx : Syntax) : Bool :=
  let kind := stx.getKind
  if kind == nullKind then
    isAtomLikeSyntax stx[0] && isAtomLikeSyntax stx[stx.getNumArgs - 1]
  else if kind == choiceKind then
    isAtomLikeSyntax stx[0] -- see toParserDescr
  else if kind == ``Lean.Parser.Syntax.paren then
    isAtomLikeSyntax stx[1]
  else
    kind == ``Lean.Parser.Syntax.atom

def resolveSyntaxKind (k : Name) : CommandElabM Name := do
  checkSyntaxNodeKindAtNamespaces k (← getCurrNamespace)
  <|>
  throwError "invalid syntax node kind '{k}'"

@[builtinCommandElab «syntax»] def elabSyntax : CommandElab := fun stx => do
  let `($[$doc?:docComment]? $attrKind:attrKind syntax $[: $prec? ]? $[(name := $name?)]? $[(priority := $prio?)]? $[$ps:stx]* : $catStx) ← pure stx
    | throwUnsupportedSyntax
  let cat := catStx.getId.eraseMacroScopes
  unless (Parser.isParserCategory (← getEnv) cat) do
    throwErrorAt catStx "unknown category '{cat}'"
  let syntaxParser := mkNullNode ps
  -- If the user did not provide an explicit precedence, we assign `maxPrec` to atom-like syntax and `leadPrec` otherwise.
  let precDefault  := if isAtomLikeSyntax syntaxParser then Parser.maxPrec else Parser.leadPrec
  let prec ← match prec? with
    | some prec => liftMacroM <| evalPrec prec
    | none      => pure precDefault
  let name ← match name? with
    | some name => pure name.getId
    | none => liftMacroM <| mkNameFromParserSyntax cat syntaxParser
  let prio ← liftMacroM <| evalOptPrio prio?
  let stxNodeKind := (← getCurrNamespace) ++ name
  let catParserId := mkIdentFrom stx (cat.appendAfter "Parser")
  let (val, lhsPrec?) ← runTermElabM none fun _ => Term.toParserDescr syntaxParser cat
  let declName := mkIdentFrom stx name
  let d ← if let some lhsPrec := lhsPrec? then
    `($[$doc?:docComment]? @[$attrKind:attrKind $catParserId:ident $(quote prio):num] def $declName:ident : Parser.TrailingParser :=
        Parser.trailingNode $(quote stxNodeKind) $(quote prec) $(quote lhsPrec) $val)
  else
    `($[$doc?:docComment]? @[$attrKind:attrKind $catParserId:ident $(quote prio):num] def $declName:ident : Parser.Parser :=
        Parser.leadingNode $(quote stxNodeKind) $(quote prec) $val)
  trace `Elab fun _ => d
  withMacroExpansion stx d <| elabCommand d

@[builtinCommandElab «syntaxAbbrev»] def elabSyntaxAbbrev : CommandElab := fun stx => do
  let `($[$doc?:docComment]? syntax $declName:ident := $[$ps:stx]*) ← pure stx | throwUnsupportedSyntax
  -- TODO: nonatomic names
  let (val, _) ← runTermElabM none fun _ => Term.toParserDescr (mkNullNode ps) Name.anonymous
  let stxNodeKind := (← getCurrNamespace) ++ declName.getId
  let stx' ← `($[$doc?:docComment]? def $declName:ident : Parser.Parser := Parser.nodeWithAntiquot $(quote (toString declName.getId)) $(quote stxNodeKind) $val)
  withMacroExpansion stx stx' <| elabCommand stx'

def checkRuleKind (given expected : SyntaxNodeKind) : Bool :=
  given == expected || given == expected ++ `antiquot

def inferMacroRulesAltKind : Syntax → CommandElabM SyntaxNodeKind
  | `(matchAltExpr| | $pat:term => $_) => do
    if !pat.isQuot then
      throwUnsupportedSyntax
    let quoted := getQuotContent pat
    pure quoted.getKind
  | _ => throwUnsupportedSyntax

/--
Infer syntax kind `k` from first pattern, put alternatives of same kind into new `macro/elab_rules (kind := k)` via `mkCmd (some k)`,
leave remaining alternatives (via `mkCmd none`) to be recursively expanded. -/
def expandNoKindMacroRulesAux (alts : Array Syntax) (cmdName : String) (mkCmd : Option Name → Array Syntax → CommandElabM Syntax) : CommandElabM Syntax := do
  let mut k ← inferMacroRulesAltKind alts[0]
  if k.isStr && k.getString! == "antiquot" then
    k := k.getPrefix
  if k == choiceKind then
    throwErrorAt alts[0]
      "invalid {cmdName} alternative, multiple interpretations for pattern (solution: specify node kind using `{cmdName} (kind := ...) ...`)"
  else
    let altsK    ← alts.filterM fun alt => return checkRuleKind (← inferMacroRulesAltKind alt) k
    let altsNotK ← alts.filterM fun alt => return !checkRuleKind (← inferMacroRulesAltKind alt) k
    if altsNotK.isEmpty then
      mkCmd k altsK
    else
      return mkNullNode #[← mkCmd k altsK, ← mkCmd none altsNotK]

def strLitToPattern (stx: Syntax) : MacroM Syntax :=
  match stx.isStrLit? with
  | some str => return mkAtomFrom stx str
  | none     => Macro.throwUnsupported

builtin_initialize
  registerTraceClass `Elab.syntax

end Lean.Elab.Command
