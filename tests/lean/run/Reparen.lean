/-! Reprint file after removing all parentheses and then passing it through the parenthesizer -/
import Lean.Parser

open Lean
open Lean.Format

def unparenAux (parens body : Syntax) : Syntax :=
match parens.getHeadInfo, body.getHeadInfo, body.getTailInfo, parens.getTailInfo with
| some bi', some bi, some ti, some ti' => (body.setHeadInfo { bi with leading := bi'.leading }).setTailInfo { ti with trailing := ti'.trailing }
| _, _, _, _ => body

partial def unparen : Syntax → Syntax
-- don't remove parentheses in syntax quotations, they might be semantically significant
| stx => if stx.isOfKind `Lean.Parser.Term.stxQuot then stx
  else match_syntax stx with
  | `(($stx')) => unparenAux stx $ unparen stx'
  | `(level|($stx')) => unparenAux stx $ unparen stx'
  | _ => stx.modifyArgs $ Array.map unparen

unsafe def main (args : List String) : IO Unit := do
let (debug, f) : Bool × String := match args with
  | [f, "-d"] => (true, f)
  | [f]       => (false, f)
  | _         => panic! "usage: file [-d]";
env ← mkEmptyEnvironment;
stx ← Lean.Parser.parseFile env args.head!;
let header := stx.getArg 0;
some s ← pure header.reprint | throw $ IO.userError "header reprint failed";
IO.print s;
let cmds := stx.getArgs.extract 1 stx.getArgs.size;
cmds.forM $ fun cmd => do
  let cmd := unparen cmd;
  (cmd, _) ← (PrettyPrinter.parenthesizeCommand cmd).toIO { options := Options.empty.setBool `trace.PrettyPrinter.parenthesize debug } { env := env };
  some s ← pure cmd.reprint | throw $ IO.userError "cmd reprint failed";
  IO.print s

#eval main ["../../../src/Init/Core.lean"]

def check (stx : Syntax) : CoreM Unit := do
let stx' := unparen stx;
stx' ← PrettyPrinter.parenthesizeTerm stx';
f ← PrettyPrinter.formatTerm stx';
IO.println f;
when (stx != stx') $
  throwError "reparenthesization failed"

new_frontend

open Lean

syntax:80 term " ^~ " term:80 : term
syntax:70 term " *~ " term:71 : term
#eval check $ Unhygienic.run `(((1 + 2) *~ 3) ^~ 4)
