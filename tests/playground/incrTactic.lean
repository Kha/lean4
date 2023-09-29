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
  /--
    The messages produced by this step. The union of message logs of all
    finished snapshots is reported to the user. -/
  msgLog : MessageLog
deriving Inhabited

/-- A task producing some snapshot type (usually a subclass of `Snapshot`). -/
-- Longer-term TODO: Give the server more control over the priority of tasks,
-- depending on e.g. the cursor position. This may require starting the tasks
-- suspended (e.g. in `Thunk`). The server may also need more dependency
-- information for this in order to avoid priority inversion.
structure SnapshotTask (α : Type) where
  /-- Range that is marked as being processed by the server while the task is running. -/
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

def SnapshotTask.cancel (t : SnapshotTask α) : BaseIO Unit :=
  IO.cancel t.task

/--
  Chain two snapshot tasks. The range is taken from the first task if not specified;
  the range of the second task is discarded. -/
def SnapshotTask.bind (t : SnapshotTask α) (act : α → BaseIO (SnapshotTask β)) (range : String.Range := t.range) :
    BaseIO (SnapshotTask β) :=
  return { range, task := (← BaseIO.bindTask t.task fun a => (·.task) <$> (act a)) }

/-! The hierarchy of Lean snapshot types -/
-- (other languages would have to design their own hierarchies)

/-- Final state of processing of a command. -/
structure CommandFinishedSnapshot extends Snapshot where
  cmdState : Command.State
deriving Nonempty

/-- State after execution of a single synchronous tactic step. -/
structure TacticEvaluatedSnapshotF (TacticEvaluatedSnapshot : Type) extends Snapshot where
  /-- Potential, potentially parallel, follow-up tactic executions. -/
  -- In the first, non-parallel version, each task will depend on its predecessor
  next : Array (SnapshotTask TacticEvaluatedSnapshot)
abbrev TacticEvaluatedSnapshot := Fix TacticEvaluatedSnapshotF

/--
  State after processing a command's signature and before executing its tactic
  body, if any. Other commands should immediately proceed to `finished`. -/
structure CommandSignatureProcessedSnapshot extends Snapshot where
  /-- Potential, potentially parallel, follow-up tactic executions. -/
  tacs : Array (SnapshotTask TacticEvaluatedSnapshot)
  /-- State after processing is finished. -/
  -- If we make proofs completely opaque, this will not have to depend on `tacs`
  finished : SnapshotTask CommandFinishedSnapshot
deriving Nonempty

/-- State after a command has been parsed. -/
structure CommandParsedSnapshotF (CommandParsedSnapshot : Type) extends Snapshot where
  stx : Syntax
  parserState : Parser.ModuleParserState
  /-- Furthest position the parser has looked at; used for incremental parsing. -/
  stopPos : String.Pos
  sig : SnapshotTask CommandSignatureProcessedSnapshot
  /-- Next command, unless this is a terminal command. -/
  -- It would be really nice to not make this depend on `sig.finished` where possible
  next? : Option (SnapshotTask CommandParsedSnapshot)
--deriving Nonempty  -- FIXME: introduces unnecessary TC assumption
instance : Nonempty (CommandParsedSnapshotF CommandParsedSnapshot) :=
  .intro { (default : Snapshot) with
    sig := Classical.ofNonempty, stx := default, next? := default, parserState := default, stopPos := default }
abbrev CommandParsedSnapshot := Fix CommandParsedSnapshotF

structure HeaderProcessedSucessfully where
  cmdState : Command.State
  next : SnapshotTask CommandParsedSnapshot

/-- State after the module header has been processed including imports. -/
structure HeaderProcessedSnapshot extends Snapshot where
  success? : Option HeaderProcessedSucessfully

structure HeaderParsedSucessfully where
  parserState : Parser.ModuleParserState
  /-- Furthest position the parser has looked at; used for incremental parsing. -/
  stopPos : String.Pos
  next : SnapshotTask HeaderProcessedSnapshot

/-- State after the module header has been parsed. -/
structure HeaderParsedSnapshot extends Snapshot where
  stx : Syntax
  success? : Option HeaderParsedSucessfully

abbrev InitialSnapshot := HeaderParsedSnapshot

/-- Reports `IO` exceptions as single snapshot message. -/
def withFatalExceptions (ex : Snapshot → α) (act : IO α) : BaseIO α := do
  match (← act.toBaseIO) with
  | .error e => return ex {
    msgLog := MessageLog.empty.add { fileName := "TODO", pos := ⟨0, 0⟩, data := e.toString }
  }
  | .ok a => return a

def get? (t? : Option (SnapshotTask α)) : BaseIO (Option α) := do
  let some t := t? | return none
  return if (← IO.hasFinished t.task) then t.task.get else none

def getOrCancel (t? : Option (SnapshotTask α)) : BaseIO (Option α) := do
  let some t := t? | return none
  if (← IO.hasFinished t.task) then
    return t.task.get
  IO.cancel t.task
  return none

/--
  Checks whether reparsing `stx` in `newSource` should result in `stx` again.
  `stopPos` is the furthest position the parser has looked at for producing
  `stx`, which usually is the extent of the subsequent token (if any) plus one. -/
-- This is a fundamentally different approach from the "go up one snapshot from
-- the point of change" in the old implementation which was failing in edge
-- cases and is not generalizable to a DAG of snapshots.
def unchangedParse (stx : Syntax) (stopPos : String.Pos) (newSource : String) : Bool :=
  if let .original start .. := stx.getHeadInfo then
    let oldSubstr := { start with stopPos }
    oldSubstr == { oldSubstr with str := newSource }
  else false

/-- Entry point of the Lean language processor. -/
-- As a general note, for each processing function we pass in the previous
-- state, if any, in order to reuse still-valid state. Thus the logic of
-- what snapshots to reuse is completely moved out of the server into the
-- language-specific processor. As there is no cheap way to check whether
-- the `Environment` is unchanged, we must make sure to pass `none` as all
-- follow-up "previous states" when we do change it.
partial def processLean (hOut : IO.FS.Stream) (opts : Options) (doc : DocumentMeta) (old? : Option InitialSnapshot) :
    BaseIO InitialSnapshot :=
  parseHeader old?
where
  parseHeader (old? : Option HeaderParsedSnapshot) := do
    let unchanged old success :=
      -- when header syntax is unchanged, reuse import processing task as is
      return { old with success? := some { success with
        next := (← success.next.bind (processHeader · old.stx success.parserState)) } }

    -- fast path: if we have parsed the header sucessfully...
    if let some old@{ success? := some success, .. } := old? then
      -- ...and the header syntax appears unchanged...
      if unchangedParse old.stx success.stopPos doc.text.source then
        -- ...go immediately to next snapshot
        return (← unchanged old success)

    withFatalExceptions ({ · with stx := .missing, success? := none }) do
      let (stx, parserState, msgLog) ← Parser.parseHeader doc.mkInputContext
      -- TODO: move into `parseHeader`; it should add the length of `peekToken`,
      -- which is the full extent the parser considered before stopping
      let stopPos := parserState.pos + (⟨1⟩ : String.Pos)

      if msgLog.hasErrors then
        return { stx, msgLog, success? := none }

      -- semi-fast path: go to next snapshot if syntax tree is unchanged
      if let some old@{ success? := some success, .. } := old? then
        if old.stx == stx then
          return (← unchanged old success)
        success.next.cancel

      return { stx, msgLog, success? := some {
        parserState
        stopPos
        next := (← processHeader none stx parserState) } }

  processHeader (old? : Option HeaderProcessedSnapshot) (stx : Syntax) (parserState : Parser.ModuleParserState) := do
    -- fast path, do not even start new task for this snapshot
    if let some old := old? then
      if let some success := old.success? then
        return .pure { old with success? := some { success with
          next := (← success.next.bind (parseCmd · parserState success.cmdState)) } }
      else
        return .pure old

    SnapshotTask.ofIO ⟨0, doc.text.source.endPos⟩ do
    withFatalExceptions ({ · with success? := none }) do
    -- discard existing continuation if any, there is nothing to reuse
    let _ ← old?.bind (·.success?) |>.map (·.next) |> getOrCancel
    -- function copied from current implementation, see below
    -- TODO: we should do this at most once per process
    let cmdState ← doImport stx
    return {
      msgLog := cmdState.messages
      success? := some { cmdState, next := (← parseCmd none parserState cmdState) } }

  parseCmd (old? : Option CommandParsedSnapshot) (parserState : Parser.ModuleParserState) (cmdState : Command.State) :
      BaseIO (SnapshotTask CommandParsedSnapshot) := do
    let old? := old?.map (·.unfix)
    let unchanged old : BaseIO CommandParsedSnapshot :=
      -- when syntax is unchanged, reuse command processing task as is
      if let some oldNext := old.next? then
        return .fix { old with
          next? := (← old.sig.bind fun sig =>
            sig.finished.bind fun finished => do
              parseCmd (← getOrCancel oldNext) old.parserState finished.cmdState) }
      else return .fix old  -- terminal command, we're done!

    -- fast path, do not even start new task for this snapshot
    if let some old := old? then
      if unchangedParse old.stx old.stopPos doc.text.source then
        return .pure (← unchanged old)

    SnapshotTask.ofIO ⟨parserState.pos, doc.text.source.endPos⟩ do
      let beginPos := parserState.pos
      let scope := cmdState.scopes.head!
      let inputCtx := doc.mkInputContext
      let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
      let (stx, parserState, msgLog) := Parser.parseCommand inputCtx pmctx parserState cmdState.messages

      -- TODO: move into `parseCommand`; it should add the length of `peekToken`,
      -- which is the full extent the parser considered before stopping
      let stopPos := parserState.pos + (⟨1⟩ : String.Pos)
      if let some old := old? then
        if old.stx == stx then
          return (← unchanged old)

      -- signature elaboration task; for now, does full elaboration
      -- TODO: do tactic snapshots, reuse old state for them
      let _ ← old?.map (·.sig) |> getOrCancel
      let sig ← SnapshotTask.ofIO (stx.getRange?.getD ⟨parserState.pos, parserState.pos⟩) do
        let cmdState ← doElab stx cmdState beginPos inputCtx scope
        return {
          msgLog := cmdState.messages
          -- TODO
          tacs := #[]
          finished := .pure {
            msgLog := .empty
            cmdState
          }
        }

      return .fix <| {
        msgLog
        stx
        parserState
        stopPos
        sig
        next? :=
          if Parser.isTerminalCommand stx then none
          -- for now, wait on "command finished" snapshot before parsing next command
          else some (← sig.bind fun sig => do
            sig.finished.bind fun finished =>
              parseCmd none parserState finished.cmdState)
      }

  -- COPIED
  doImport stx := do
    let mut srcSearchPath ← initSrcSearchPath (← getBuildDir)
    let lakePath ← match (← IO.getEnv "LAKE") with
      | some path => pure <| System.FilePath.mk path
      | none =>
        let lakePath ← match (← IO.getEnv "LEAN_SYSROOT") with
          | some path => pure <| System.FilePath.mk path / "bin" / "lake"
          | _         => pure <| (← IO.appDir) / "lake"
        pure <| lakePath.withExtension System.FilePath.exeExtension
    if let some path := System.Uri.fileUriToPath? doc.uri then
      -- NOTE: we assume for now that `lakefile.lean` does not have any non-stdlib deps
      -- NOTE: lake does not exist in stage 0 (yet?)
      if path.fileName != "lakefile.lean" && (← System.FilePath.pathExists lakePath) then
        let pkgSearchPath ← FileWorker.lakeSetupSearchPath lakePath doc (Lean.Elab.headerToImports stx) hOut
        srcSearchPath ← initSrcSearchPath (← getBuildDir) pkgSearchPath
    let (headerEnv, msgLog) ← Elab.processHeader stx opts .empty doc.mkInputContext
    let mut headerEnv := headerEnv
    try
      if let some path := System.Uri.fileUriToPath? doc.uri then
        headerEnv := headerEnv.setMainModule (← moduleNameOfFileName path none)
    catch _ => pure ()
    let cmdState := Elab.Command.mkState headerEnv msgLog opts
    return { cmdState with infoState := {
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

  doElab stx cmdState beginPos inputCtx scope := do
    let cmdStateRef ← IO.mkRef { cmdState with messages := .empty }
    let cmdCtx : Elab.Command.Context := {
      cmdPos       := beginPos
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
    return postCmdState
    -- END COPIED

/-!
  Finally, we tie everything together into one function that uses a mutable
  reference to remember the old state. As there is no asynchrony on this
  level, we don't have to worry about parallel writes to the reference that
  might not result in storing the "last" state. -/

/-- Returns a function for processing a Lean module with incremental snapshots. -/
partial def processLeanIncrementally (hOut : IO.FS.Stream) (opts : Options) :
    BaseIO (DocumentMeta → BaseIO InitialSnapshot) := do
  let oldRef ← IO.mkRef none
  return fun doc => do
    let snap ← processLean hOut opts doc (← oldRef.get)
    oldRef.set (some snap)
    return snap
