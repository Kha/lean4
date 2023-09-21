import Lean

private unsafe inductive FixImp (F : Type u → Type u) : Type u where
  | mk : F (FixImp F) → FixImp F

private unsafe example (F : Type u → Type u) [∀ α, Inhabited (F α)] : NonemptyType.{u} := ⟨FixImp F, .intro <| .mk default⟩
private opaque FixPointed (F : Type u → Type u) : NonemptyType.{u}

def Fix F := FixPointed F |>.type

instance : Nonempty (Fix F) := FixPointed F |>.property

@[extern "fix_imp_mk"]
opaque Fix.mk : F (Fix F) → Fix F
@[extern "fix_imp_unmk"]
opaque Fix.unmk [∀ α, Inhabited (F α)] : Fix F → F (Fix F)

---

open Lean Server Elab Command

inductive SnapshotF.Result (Snapshot : Type)
  | restartWorker
  | unchanged
  | eof
  | next (snap : Snapshot)
deriving Inhabited

structure SnapshotF (Snapshot : Type) where
  beginPos : Nat
  messages : MessageLog
  process (doc : DocumentMeta) : BaseIO (SnapshotF.Result Snapshot)
deriving Inhabited

abbrev Snapshot := Fix SnapshotF
abbrev Snapshot.Result := SnapshotF.Result Snapshot
abbrev Snapshot.ProcessCont := DocumentMeta → BaseIO Snapshot.Result

def withFatalExceptions (beginPos : Nat) (rec : Snapshot.ProcessCont) (act : IO Snapshot.Result) : BaseIO Snapshot.Result := do
  match (← act.toBaseIO) with
  | .error e => return .next <| .mk {
    beginPos
    messages := MessageLog.empty.add { fileName := "TODO", pos := ⟨0, 0⟩, data := e.toString }
    process := rec
  }
  | .ok a => return a

open Lean.Server.FileWorker in
partial def processLean (hOut : IO.FS.Stream) (opts : Options) : Snapshot :=
  initial
where
  initial : Snapshot := .mk {
    beginPos := 0
    messages := .empty
    process := parseHeader none
  }
  parseHeader (oldStx : Option Syntax) := fun m => withFatalExceptions (rec := parseHeader oldStx) (beginPos := 0) do
    let (headerStx, headerParserState, msgLog) ← do
      Parser.parseHeader m.mkInputContext
    if oldStx == some headerStx then
      return .unchanged
    return .next <| .mk {
      beginPos := 0
      messages := msgLog
      process := elabHeader headerStx headerParserState
    }
  elabHeader headerStx headerParserState := fun m => withFatalExceptions (rec := elabHeader headerStx headerParserState) (beginPos := 0) do
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
      if let some path := System.Uri.fileUriToPath? m.uri then
        -- NOTE: we assume for now that `lakefile.lean` does not have any non-stdlib deps
        -- NOTE: lake does not exist in stage 0 (yet?)
        if path.fileName != "lakefile.lean" && (← System.FilePath.pathExists lakePath) then
          let pkgSearchPath ← lakeSetupSearchPath lakePath m (Lean.Elab.headerToImports headerStx) hOut
          srcSearchPath ← initSrcSearchPath (← getBuildDir) pkgSearchPath
      Elab.processHeader headerStx opts .empty m.mkInputContext
    catch e =>  -- should be from `lake print-paths`
      let msgs := MessageLog.empty.add { fileName := "<ignored>", pos := ⟨0, 0⟩, data := e.toString }
      pure (← mkEmptyEnvironment, msgs)
    let mut headerEnv := headerEnv
    try
      if let some path := System.Uri.fileUriToPath? m.uri then
        headerEnv := headerEnv.setMainModule (← moduleNameOfFileName path none)
    catch _ => pure ()
    let cmdState := Elab.Command.mkState headerEnv msgLog opts
    let cmdState := { cmdState with infoState := {
      enabled := true
      trees := #[Elab.InfoTree.context ({
        env     := headerEnv
        fileMap := m.text
        ngen    := { namePrefix := `_worker }
      }) (Elab.InfoTree.node
          (Elab.Info.ofCommandInfo { elaborator := `header, stx := headerStx })
          (headerStx[1].getArgs.toList.map (fun importStx =>
            Elab.InfoTree.node (Elab.Info.ofCommandInfo {
              elaborator := `import
              stx := importStx
            }) #[].toPArray'
          )).toPArray'
      )].toPArray'
    }}
    -- END COPIED
    return .next <| .mk {
      beginPos := 0
      messages := cmdState.messages
      process := processCmd none headerParserState cmdState
    }
  processCmd (oldStx : Option Syntax) (mpState : Parser.ModuleParserState) (cmdState : Command.State) := fun doc => do
    let scope := cmdState.scopes.head!
    let inputCtx := doc.mkInputContext
    let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (cmdStx, cmdParserState, msgLog) :=
      Parser.parseCommand inputCtx pmctx mpState cmdState.messages
    if oldStx == some cmdStx then
      return .unchanged
    return .next <| .mk {
      beginPos := mpState.pos.byteIdx
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
              pos      := inputCtx.fileMap.toPosition mpState.pos
              data     := output
            }
          }
        -- END COPIED
        return .next <| .mk {
          beginPos := mpState.pos.byteIdx
          messages := postCmdState.messages
          process := processCmd cmdStx cmdParserState postCmdState
        }
    }
