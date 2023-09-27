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
opaque Fix.fix : F (Fix F) → Fix F
@[extern "fix_imp_unfix"]
opaque Fix.unfix [∀ α, Nonempty (F α)] : Fix F → F (Fix F)

---

/-! New snapshot API -/

open Lean Server Elab Command

/--
  The base class of all snapshots: all the generic information the language server
  needs about a snapshot. -/
structure Snapshot where
  /-- The messages produced by this step, to be sent to the client. -/
  msgLog : MessageLog
deriving Inhabited

structure SnapshotTask (α : Type) where
  range : String.Range
  task : Task α
deriving Nonempty

def SnapshotTask.ofIO (range : String.Range) (act : BaseIO α) : BaseIO (SnapshotTask α) := do
  return {
    range
    task := (← BaseIO.asTask act)
  }

def SnapshotTask.pure (a : α) : SnapshotTask α where
  -- irrelevant when already finished
  range := default
  task := .pure a


structure CommandFinishedSnapshot extends Snapshot where
  cmdState : Command.State
deriving Nonempty

structure TacticEvaluatedSnapshotF (TacticEvaluatedSnapshot : Type) extends Snapshot where
  next? : Option (SnapshotTask TacticEvaluatedSnapshot)
abbrev TacticEvaluatedSnapshot := Fix TacticEvaluatedSnapshotF

structure CommandSignatureProcessedSnapshot extends Snapshot where
  tacs : Array (SnapshotTask TacticEvaluatedSnapshot)
  finished : SnapshotTask CommandFinishedSnapshot
deriving Nonempty

structure CommandParsedSnapshotF (CommandParsedSnapshot : Type) extends Snapshot where
  stx : Syntax
  sig : SnapshotTask CommandSignatureProcessedSnapshot
  next? : Option (SnapshotTask CommandParsedSnapshot)
--deriving Nonempty  -- introduces unnecessary TC assumption
instance : Nonempty (CommandParsedSnapshotF CommandParsedSnapshot) :=
  .intro { (default : Snapshot) with sig := Classical.ofNonempty, stx := default, next? := default }
abbrev CommandParsedSnapshot := Fix CommandParsedSnapshotF

structure HeaderProcessedSnapshot extends Snapshot where
  cmdState? : Option Command.State
  next? : Option (SnapshotTask CommandParsedSnapshot)

structure HeaderParsedSnapshot extends Snapshot where
  stx : Syntax
  next? : Option (SnapshotTask HeaderProcessedSnapshot)

abbrev InitialSnapshot := HeaderParsedSnapshot

def withFatalExceptions (ex : Snapshot → α) (act : IO α) : BaseIO α := do
  match (← act.toBaseIO) with
  | .error e => return ex {
    msgLog := MessageLog.empty.add { fileName := "TODO", pos := ⟨0, 0⟩, data := e.toString }
  }
  | .ok a => return a

def getOrCancel (t? : Option (SnapshotTask α)) : BaseIO (Option α) := do
  let some t := t? | return none
  if (← IO.hasFinished t.task) then
    return t.task.get
  IO.cancel t.task
  return none

open Lean.Server.FileWorker in
partial def processLean (hOut : IO.FS.Stream) (opts : Options) (doc : DocumentMeta) (old? : Option InitialSnapshot) :
    BaseIO (SnapshotTask InitialSnapshot) :=
  parseHeader old?
where
  parseHeader (old? : Option HeaderParsedSnapshot) :=
    SnapshotTask.ofIO ⟨0, doc.text.source.endPos⟩ do
    withFatalExceptions ({ · with stx := .missing, next? := none }) do
    let oldNext? ← old?.bind (·.next?) |> getOrCancel
    let (stx, parserState, msgLog) ← do
      Parser.parseHeader doc.mkInputContext
    let oldNext? := if old?.any (·.stx == stx) then oldNext? else none
    return { stx, msgLog, next? := some (← processHeader oldNext? stx parserState) }
  processHeader (old? : Option HeaderProcessedSnapshot) (stx : Syntax) (parserState : Parser.ModuleParserState) :=
    SnapshotTask.ofIO ⟨0, doc.text.source.endPos⟩ do
    withFatalExceptions ({ · with next? := none, cmdState? := none }) do
    if let some old@{ cmdState? := some cmdState, .. } := old? then
      let oldNext? ← old?.bind (·.next?) |> getOrCancel
      return { old with next? := some (← parseCmd oldNext? parserState cmdState) }
    let _ ← old?.bind (·.next?) |> getOrCancel
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
      cmdState? := cmdState
      msgLog := cmdState.messages
      next? := some (← parseCmd none parserState cmdState)
    }
  parseCmd (old? : Option CommandParsedSnapshot) (parserState : Parser.ModuleParserState) (cmdState : Command.State) :
      BaseIO (SnapshotTask CommandParsedSnapshot) :=
    SnapshotTask.ofIO ⟨parserState.pos, doc.text.source.endPos⟩ do
    let beginPos := parserState.pos
    let scope := cmdState.scopes.head!
    let inputCtx := doc.mkInputContext
    let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (stx, parserState, msgLog) :=
      Parser.parseCommand inputCtx pmctx parserState cmdState.messages
    let oldNext? ← old?.bind (·.unfix.next?) |> getOrCancel
    if let some old := old? then
      let old := old.unfix
      if old.stx == stx then
        -- NOTE: we do NOT `getOrCancel` `old.sig` as its eventual result
        -- should be unchanged, so there is no reason to restart the computation
        return .fix { old with next? := (← parseCmd oldNext? parserState cmdState) }
    let oldSig? ← old?.map (·.unfix.sig) |> getOrCancel
    let sig ← SnapshotTask.ofIO (stx.getRange?.getD ⟨parserState.pos, parserState.pos⟩) do
      -- TODO: only invalidate and recreate tactics up to the first difference in
      -- the syntax trees
      if let some old := oldSig? then
        for t in old.tacs do
          IO.cancel t.task

      -- COPIED
      let cmdStateRef ← IO.mkRef { cmdState with messages := .empty }
      let cmdCtx : Elab.Command.Context := {
        cmdPos       := parserState.pos
        fileName     := inputCtx.fileName
        fileMap      := inputCtx.fileMap
        tacticCache? := none
      }
      let (output, _) ← IO.FS.withIsolatedStreams (isolateStderr := Snapshots.server.stderrAsMessages.get scope.opts) <| liftM (m := BaseIO) do
        Elab.Command.catchExceptions
          (getResetInfoTrees *> Elab.Command.elabCommandTopLevel stx)
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
      return {
        msgLog := postCmdState.messages
        -- TODO
        tacs := #[]
        finished := .pure {
          msgLog := .empty
          cmdState := (← cmdStateRef.get)
        }
      }

    return .fix <| {
      stx
      msgLog
      sig
      next? :=
        if Parser.isTerminalCommand stx then none
        else some ⟨⟨parserState.pos, doc.text.source.endPos⟩, (← BaseIO.bindTask sig.task fun sig => do
          BaseIO.bindTask sig.finished.task fun finished =>
            (·.task) <$> parseCmd none parserState finished.cmdState)⟩
    }
