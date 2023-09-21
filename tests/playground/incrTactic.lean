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

def withFatalExceptions (act : IO Snapshot.Result) : BaseIO Snapshot.Result := do
  match (← act.toBaseIO) with
  | .error e => return .next <| .mk {
    messages := MessageLog.empty.add { fileName := "TODO", pos := ⟨0, 0⟩, data := e.toString }
    next := .pure .eof
  }
  | .ok a => return a

open Lean.Server.FileWorker in
partial def processLean (hOut : IO.FS.Stream) (opts : Options) (doc : DocumentMeta) : BaseIO Snapshot :=
  initial doc
where
  initial (doc : DocumentMeta) : BaseIO Snapshot := return .mk {
    messages := .empty
    next := ← BaseIO.asTask (parseHeader none doc)
    reprocess := fun doc => do BaseIO.asTask <| return .next (← initial doc)
  }
  parseHeader (oldStx : Option Syntax) (m : DocumentMeta) := Snapshot.ofProcess <| withFatalExceptions do
    let (headerStx, headerParserState, msgLog) ← do
      Parser.parseHeader m.mkInputContext
    return .next <| .mk {
      messages := msgLog
      reprocess := parseHeader headerStx m
      next := fun m => withFatalExceptions (beginPos := 0) do
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
          processNext := processCmd none headerParserState cmdState
        }
  }
  processCmd (oldStx : Option Syntax) (mpState : Parser.ModuleParserState) (cmdState : Command.State) := fun doc => do
    let beginPos := mpState.pos
    let scope := cmdState.scopes.head!
    let inputCtx := doc.mkInputContext
    let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (cmdStx, cmdParserState, msgLog) :=
      Parser.parseCommand inputCtx pmctx mpState cmdState.messages
    if oldStx == some cmdStx then
      return .unchanged
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
