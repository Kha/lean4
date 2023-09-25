import Lean

/-! First the mentioned `Fix` helper; just a prototype as well. -/

private unsafe inductive FixImp (F : Type u → Type u) : Type u where
  | mk : F (FixImp F) → FixImp F

private unsafe example (F : Type u → Type u) [∀ α, Inhabited (F α)] : NonemptyType.{u} := ⟨FixImp F, .intro <| .mk default⟩
private opaque FixPointed (F : Type u → Type u) : NonemptyType.{u}

/--
  `Fix F` for `F : Type → Type` represents the fixpoint `F (F (F ...))`.
  It can be used to construct nested types not accepted by `inductive`.
  In exchange, there is no accessible recursor or `Sizeof` instance,
  and so recursion over a value of type `Fix F` has to be done using
  `partial` or another argument of the function. -/
def Fix F := FixPointed F |>.type
instance : Nonempty (Fix F) := FixPointed F |>.property

@[extern "fix_imp_mk"]
opaque Fix.mk : F (Fix F) → Fix F
@[extern "fix_imp_unmk"]
opaque Fix.unmk [∀ α, Nonempty (F α)] : Fix F → F (Fix F)

---

/-! New snapshot API -/

open Lean Server Elab Command

/-
/-- Result of processing a snapshot -/
inductive SnapshotF.Result (Snapshot : Type)
  /-- Forces the current file worker to restart; used when the set of imports has changed. -/
  | restartWorker
  | eof
  | next (snap : Snapshot)
deriving Inhabited

structure SnapshotF (Snapshot : Type) where
  messages : MessageLog
  next : Task (SnapshotF.Result Snapshot)
  reprocess (doc : DocumentMeta) : BaseIO (Task (SnapshotF.Result Snapshot))

def Snapshot := Fix SnapshotF
--inductive Snapshot where
--  | mk : SnapshotF Snapshot → Snapshot
abbrev Snapshot.Result := SnapshotF.Result Snapshot
abbrev Snapshot.ProcessCont := DocumentMeta → BaseIO Snapshot.Result

def Snapshot.ofProcess
  (process : (doc : DocumentMeta) → BaseIO (SnapshotF.Result Snapshot))
  (doc : DocumentMeta) :
    BaseIO Snapshot := do
  let next ← BaseIO.asTask (process doc)
  return .mk {
    next
    reprocess := fun doc =>


  }
-/

structure Snapshot where
  msgLog : MessageLog
  stx : Syntax

abbrev SnapshotTask α := Task α

structure TacticSnapshotF (TacticSnapshot : Type) extends Snapshot where
  next? : Option (SnapshotTask TacticSnapshot)
abbrev TacticSnapshot := Fix TacticSnapshotF

structure CommandSnapshotF (CommandParseSnapshot : Type) extends Snapshot where
  nextTac? : Option (SnapshotTask TacticSnapshot)
  next? : Option (SnapshotTask CommandParseSnapshot)

structure CommandParseSnapshotF (CommandParseSnapshot : Type) extends Snapshot where
  next? : Option (SnapshotTask (CommandSnapshotF CommandParseSnapshot))

abbrev CommandParseSnapshot := Fix CommandParseSnapshotF
abbrev CommandSnapshot := CommandSnapshotF CommandParseSnapshot

structure HeaderSnapshot extends Snapshot where
  cmdState : Command.State
  next? : Option (SnapshotTask CommandSnapshot)

structure HeaderParseSnapshot extends Snapshot where
  next? : Option (SnapshotTask HeaderSnapshot)

abbrev InitialSnapshot := HeaderParseSnapshot

def withFatalExceptions (ex : Snapshot → α) (act : IO α) : BaseIO α := do
  match (← act.toBaseIO) with
  | .error e => return ex {
    stx := .missing
    msgLog := MessageLog.empty.add { fileName := "TODO", pos := ⟨0, 0⟩, data := e.toString }
  }
  | .ok a => return a

def getOrCancel (t? : Option (SnapshotTask α)) : BaseIO (Option α) := do
  let some t := t? | return none
  if (← IO.hasFinished t) then
    return t.get
  IO.cancel t
  return none

open Lean.Server.FileWorker in
partial def processLean (hOut : IO.FS.Stream) (opts : Options) (doc : DocumentMeta) (old? : Option InitialSnapshot) :
    BaseIO InitialSnapshot :=
  parseHeader old?
where
  parseHeader (old? : Option HeaderParseSnapshot) := withFatalExceptions ({ · with stx := .missing, next? := none }) do
    let (stx, parserState, msgLog) ← do
      Parser.parseHeader doc.mkInputContext
    let oldNext? ← old?.bind (·.next?) |> getOrCancel
    return { stx, msgLog, next? := some (← BaseIO.asTask <| processHeader oldNext? stx parserState) }
  processHeader (old? : Option HeaderSnapshot) (stx : Syntax) (parserState : Parser.ModuleParserState) := withFatalExceptions ({ · with next? := none }) do
    if let some old := old? then
      if old.stx == stx then
        let oldNext? ← old?.bind (·.next?) |> getOrCancel
        return { old with next? := some (← BaseIO.asTask <| parseCmd oldNext? parserState old.cmdState) }
    -- COPIED
    let mut srcSearchPath ← initSrcSearchPath (← getBuildDir)
    let lakePath ← match (← IO.getEnv "LAKE") with
      | some path => pure <| System.FilePath.mk path
      | none =>
        let lakePath ← match (← IO.getEnv "LEAN_SYSROOT") with
          | some path => pure <| System.FilePath.mk path / "bin" / "lake"
          | _         => pure <| (← IO.appDir) / "lake"
        pure <| lakePath.withExtension System.FilePath.exeExtension
    let (headerEnv, msgLog) ← try
      if let some path := System.Uri.fileUriToPath? doc.uri then
        -- NOTE: we assume for now that `lakefile.lean` does not have any non-stdlib deps
        -- NOTE: lake does not exist in stage 0 (yet?)
        if path.fileName != "lakefile.lean" && (← System.FilePath.pathExists lakePath) then
          let pkgSearchPath ← lakeSetupSearchPath lakePath doc (Lean.Elab.headerToImports stx) hOut
          srcSearchPath ← initSrcSearchPath (← getBuildDir) pkgSearchPath
      Elab.processHeader stx opts .empty doc.mkInputContext
    catch e =>  -- should be from `lake print-paths`
      let msgs := MessageLog.empty.add { fileName := "<ignored>", pos := ⟨0, 0⟩, data := e.toString }
      pure (← mkEmptyEnvironment, msgs)
    let mut headerEnv := headerEnv
    try
      if let some path := System.Uri.fileUriToPath? doc.uri then
        headerEnv := headerEnv.setMainModule (← moduleNameOfFileName path none)
    catch _ => pure ()
    let cmdState := Elab.Command.mkState headerEnv msgLog opts
    let cmdState := { cmdState with infoState := {
      enabled := true
      trees := #[Elab.InfoTree.context ({
        env     := headerEnv
        fileMap := doc.text
        ngen    := { namePrefix := `_worker }
      }) (Elab.InfoTree.node
          (Elab.Info.ofCommandInfo { elaborator := `header, stx })
          (stx[1].getArgs.toList.map (fun importStx =>
            Elab.InfoTree.node (Elab.Info.ofCommandInfo {
              elaborator := `import
              stx := importStx
            }) #[].toPArray'
          )).toPArray'
      )].toPArray'
    }}
    -- END COPIED
    return {
      stx
      cmdState
      msgLog := cmdState.messages
      next? := some (← BaseIO.asTask <| parseCmd (old?.map _) parserState cmdState)
    }
  parseCmd (old? : Option CommandSnapshot) (mpState : Parser.ModuleParserState) (cmdState : Command.State) := do
    let beginPos := mpState.pos
    let scope := cmdState.scopes.head!
    let inputCtx := doc.mkInputContext
    let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (cmdStx, cmdParserState, msgLog) :=
      Parser.parseCommand inputCtx pmctx mpState cmdState.messages
    if let some old := old? then
      if let some next := old.next? then
        if let some oldProc ← next.getOrCancel then
          if old.stx == stx then
            return { old with next? := some (← BaseIO.asTask <| processHeader oldProc stx parserState) }
    return .next <| .mk {
      beginPos
      messages := msgLog
      process := fun _ => do
        -- COPIED
        let cmdStateRef ← IO.mkRef { cmdState with messages := .empty }
        let cmdCtx : Elab.Command.Context := {
          cmdPos       := mpState.pos
          fileName     := inputCtx.fileName
          fileMap      := inputCtx.fileMap
          tacticCache? := none
        }
        let (output, _) ← IO.FS.withIsolatedStreams (isolateStderr := Snapshots.server.stderrAsMessages.get scope.opts) <| liftM (m := BaseIO) do
          Elab.Command.catchExceptions
            (getResetInfoTrees *> Elab.Command.elabCommandTopLevel cmdStx)
            cmdCtx cmdStateRef
        let mut postCmdState ← cmdStateRef.get
        if !output.isEmpty then
          postCmdState := {
            postCmdState with
            messages := postCmdState.messages.add {
              fileName := inputCtx.fileName
              severity := MessageSeverity.information
              pos      := inputCtx.fileMap.toPosition beginPos
              data     := output
            }
          }
        -- END COPIED
        return .next <| .mk {
          beginPos
          messages := postCmdState.messages
          process := processCmd cmdStx cmdParserState postCmdState
        }
    }
