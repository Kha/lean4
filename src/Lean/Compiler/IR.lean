/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
private import Lean.Compiler.IR.Basic
private import Lean.Compiler.IR.Format
private import Lean.Compiler.IR.CompilerM
private import Lean.Compiler.IR.PushProj
private import Lean.Compiler.IR.ElimDeadVars
private import Lean.Compiler.IR.SimpCase
private import Lean.Compiler.IR.ResetReuse
private import Lean.Compiler.IR.NormIds
private import Lean.Compiler.IR.Checker
private import Lean.Compiler.IR.Borrow
private import Lean.Compiler.IR.Boxing
private import Lean.Compiler.IR.RC
private import Lean.Compiler.IR.ExpandResetReuse
private import Lean.Compiler.IR.UnboxResult
private import Lean.Compiler.IR.ElimDeadBranches
private import Lean.Compiler.IR.EmitC
private import Lean.Compiler.IR.CtorLayout
private import Lean.Compiler.IR.Sorry

namespace Lean.IR

register_builtin_option compiler.reuse : Bool := {
  defValue := true
  descr    := "heuristically insert reset/reuse instruction pairs"
}

private def compileAux (decls : Array Decl) : CompilerM Unit := do
  logDecls `init decls
  checkDecls decls
  let mut decls ← elimDeadBranches decls
  logDecls `elim_dead_branches decls
  decls := decls.map Decl.pushProj
  logDecls `push_proj decls
  if compiler.reuse.get (← read) then
    decls := decls.map Decl.insertResetReuse
    logDecls `reset_reuse decls
  decls := decls.map Decl.elimDead
  logDecls `elim_dead decls
  decls := decls.map Decl.simpCase
  logDecls `simp_case decls
  decls := decls.map Decl.normalizeIds
  decls ← inferBorrow decls
  logDecls `borrow decls
  decls ← explicitBoxing decls
  logDecls `boxing decls
  decls ← explicitRC decls
  logDecls `rc decls
  if compiler.reuse.get (← read) then
    decls := decls.map Decl.expandResetReuse
    logDecls `expand_reset_reuse decls
  decls := decls.map Decl.pushProj
  logDecls `push_proj decls
  decls ← updateSorryDep decls
  logDecls `result decls
  checkDecls decls
  addDecls decls

@[export lean_ir_compile]
def compile (env : Environment) (opts : Options) (decls : Array Decl) : Log × (Except String Environment) :=
  match (compileAux decls opts).run { env := env } with
  | EStateM.Result.ok     _  s => (s.log, Except.ok s.env)
  | EStateM.Result.error msg s => (s.log, Except.error msg)

def addBoxedVersionAux (decl : Decl) : CompilerM Unit := do
  let env ← getEnv
  if !ExplicitBoxing.requiresBoxedVersion env decl then
    pure ()
  else
    let decl := ExplicitBoxing.mkBoxedVersion decl
    let decls : Array Decl := #[decl]
    let decls ← explicitRC decls
    decls.forM fun decl => modifyEnv fun env => addDeclAux env decl
    pure ()

-- Remark: we are ignoring the `Log` here. This should be fine.
@[export lean_ir_add_boxed_version]
def addBoxedVersion (env : Environment) (decl : Decl) : Except String Environment :=
  match (addBoxedVersionAux decl Options.empty).run { env := env } with
  | EStateM.Result.ok     _  s => Except.ok s.env
  | EStateM.Result.error msg _ => Except.error msg

end Lean.IR
