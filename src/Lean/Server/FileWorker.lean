/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.System.IO
import Std.Data.RBMap

import Lean.Environment
import Lean.Server.Snapshots
import Lean.Server.Utils
import Lean.Data.Lsp
import Lean.Data.Json.FromToJson
import Lean.Server.AsyncList

/-!
For general server architecture, see `README.md`. For details of IPC communication, see `Watchdog.lean`.
This module implements per-file worker processes.

File processing and requests+notifications against a file should be concurrent for two reasons:
- By the LSP standard, requests should be cancellable.
- Since Lean allows arbitrary user code to be executed during elaboration via the tactic framework,
  elaboration can be extremely slow and even not halt in some cases. Users should be able to
  work with the file while this is happening, e.g. make new changes to the file or send requests.

To achieve these goals, elaboration is executed in a chain of tasks, where each task corresponds to
the elaboration of one command. When the elaboration of one command is done, the next task is spawned.
On didChange notifications, we search for the task in which the change occured. If we stumble across
a task that has not yet finished before finding the task we're looking for, we terminate it
and start the elaboration there, otherwise we start the elaboration at the task where the change occured.

Requests iterate over tasks until they find the command that they need to answer the request.
In order to not block the main thread, this is done in a request task.
If a task that the request task waits for is terminated, a change occured somewhere before the
command that the request is looking for and the request sends a "content changed" error.
-/

namespace Lean
namespace Server

open Lsp
open IO
open Snapshots

private def sendDiagnostics (h : FS.Stream) (uri : DocumentUri) (version : Nat) (text : FileMap) (log : MessageLog)
  : IO Unit := do
diagnostics ← log.msgs.mapM (msgToDiagnostic text);
Lsp.writeLspNotification h "textDocument/publishDiagnostics"
  { uri         := uri,
    version?    := version,
    diagnostics := diagnostics.toArray
    : PublishDiagnosticsParams }

private def logSnapContent (s : Snapshot) (text : FileMap) : IO Unit :=
IO.eprintln $ "`" ++ text.source.extract s.beginPos (s.endPos-1) ++ "`"

inductive TaskError
| aborted
| eof
| ioError (e : IO.Error)

instance : Coe IO.Error TaskError := ⟨TaskError.ioError⟩

private def nextCmdSnap (h : FS.Stream) (uri : DocumentUri) (version : Nat) (contents : FileMap)
  : Snapshot → ExceptT TaskError IO Snapshot
| parentSnap => do
  maybeSnap ← monadLift $ compileNextCmd contents.source parentSnap;
  match maybeSnap with
  | Sum.inl snap => do
    -- NOTE(MH): This relies on the client discarding old diagnostics upon receiving new ones
    -- while prefering newer versions over old ones. The former is necessary because we do
    -- not explicitly clear older diagnostics, while the latter is necessary because we do
    -- not guarantee that diagnostics are emitted in order. Specifically, it may happen that
    -- we interrupted this elaboration task right at this point and a newer elaboration task
    -- emits diagnostics, after which we emit old diagnostics because we did not yet detect
    -- the interrupt. Explicitly clearing diagnostics is difficult for a similar reason,
    -- because we cannot guarantee that no further diagnostics are emitted after clearing
    -- them.
    monadLift $ sendDiagnostics h uri version contents snap.msgLog;
    pure snap
  | Sum.inr msgLog => do
    monadLift $ sendDiagnostics h uri version contents msgLog;
    throw TaskError.eof

def unfoldCmdSnaps (h : FS.Stream) (uri : DocumentUri) (version : Nat) (contents : FileMap)
  (initSnap : Snapshot)
: IO (AsyncList TaskError Snapshot) :=
  AsyncList.unfoldAsync
    (nextCmdSnap h uri version contents)
    initSnap
    -- TODO(MH): check for interrupt with increased precision
    (some fun _ => pure TaskError.aborted)

/-- A document editable in the sense that we track the environment
and parser state after each command so that edits can be applied
without recompiling code appearing earlier in the file. -/
structure EditableDocument :=
(version : Nat)
(text : FileMap)
/- The first snapshot is that after the header. -/
(headerSnap : Snapshot)
/- Subsequent snapshots occur after each command. -/
(cmdSnaps : AsyncList TaskError Snapshot)

namespace EditableDocument

open Elab

/-- Compiles the contents of a Lean file. -/
def compileDocument (h : FS.Stream) (uri : DocumentUri) (version : Nat) (text : FileMap) : IO EditableDocument := do
headerSnap ← Snapshots.compileHeader text.source;
cmdSnaps ← unfoldCmdSnaps h uri version text headerSnap;
pure ⟨version, text, headerSnap, cmdSnaps⟩

/-- Given `changePos`, the UTF-8 offset of a change into the pre-change source,
and the new document, updates editable doc state. -/
def updateDocument (h : FS.Stream) (uri : DocumentUri) (doc : EditableDocument) (changePos : String.Pos)
  (newVersion : Nat) (newText : FileMap) : IO EditableDocument := do
  -- The watchdog only restarts the file worker when the syntax tree of the header changes.
  -- If e.g. a newline is deleted, it will not restart this file worker, but we still
  -- need to reparse the header so the offsets are correct.
  newHeaderSnap ← reparseHeader newText.source doc.headerSnap;

  ⟨cmdSnaps, e?⟩ ← doc.cmdSnaps.updateFinishedPrefix;
  match e? with
  -- this case should not be possible. only the main task aborts tasks and ensures that aborted tasks
  -- do not show up in `snapshots` of EditableDocument below.
  | some TaskError.aborted => throwServerError
    "Internal server error: reached case that should not be possible during server file worker task branching"
  | some (TaskError.ioError ioError) => throw ioError
  | _ => do -- No error or EOF
    -- NOTE(WN): endPos is greedy in that it consumes input until the next token,
    -- so a change on some whitespace after a command recompiles it. We could
    -- be more precise.
    let validSnaps := cmdSnaps.finishedPrefix.takeWhile (fun s => s.endPos < changePos);
    -- NOTE: the watchdog never sends didChange notifs with a header change to the
    -- worker, so the header snapshot is always valid.
    let lastSnap := validSnaps.getLastD doc.headerSnap;
    newSnaps ← unfoldCmdSnaps h uri newVersion newText lastSnap;
    let newCmdSnaps := AsyncList.ofList validSnaps ++ newSnaps;
    -- NOTE: We do not cancel old tasks explicitly, the GC does this for us when no refs remain.
    pure ⟨newVersion, newText, newHeaderSnap, newCmdSnaps⟩

end EditableDocument

open EditableDocument

open IO
open Std (RBMap RBMap.empty)
open JsonRpc

abbrev PendingRequestMap := RBMap RequestID (Task (Except IO.Error Unit)) (fun a b => Decidable.decide (a < b))

structure ServerContext :=
(hIn hOut : FS.Stream)
(docRef : IO.Ref EditableDocument)
(pendingRequestsRef : IO.Ref PendingRequestMap)

abbrev ServerM := ReaderT ServerContext IO

def setDocument (val : EditableDocument) : ServerM Unit :=
fun st => st.docRef.set val

def getDocument : ServerM EditableDocument :=
fun st => st.docRef.get

def updatePendingRequests (map : PendingRequestMap → PendingRequestMap) : ServerM Unit :=
fun st => st.pendingRequestsRef.modify map

def openDocument (h : FS.Stream) (p : DidOpenTextDocumentParams) : IO EditableDocument :=
let doc := p.textDocument;
-- NOTE(WN): `toFileMap` marks line beginnings as immediately following
-- "\n", which should be enough to handle both LF and CRLF correctly.
-- This is because LSP always refers to characters by (line, column),
-- so if we get the line number correct it shouldn't matter that there
-- is a CR there.
compileDocument h doc.uri doc.version doc.text.toFileMap

def handleDidChange (p : DidChangeTextDocumentParams) : ServerM Unit := do
let docId := p.textDocument;
let changes := p.contentChanges;
oldDoc ← getDocument;
some newVersion ← pure docId.version? | throwServerError "Expected version number";
if newVersion <= oldDoc.version then throwServerError "Got outdated version number"
else when (not changes.isEmpty) $ do
  let (newDocText, minStartOff) := foldDocumentChanges changes oldDoc.text;
  st ← read;
  newDoc ← monadLift $
    updateDocument st.hOut docId.uri oldDoc minStartOff newVersion newDocText;
  setDocument newDoc

def handleCancelRequest (p : CancelParams) : ServerM Unit := do
updatePendingRequests (fun pendingRequests => pendingRequests.erase p.id)

-- TODO(MH): requests that need data from a certain command should traverse e.snapshots
-- by successively getting the next task, meaning that we might need to wait for elaboration.
-- Sebastian said something about a future function TaskIO.bind that ensures that the
-- request task will also stop waiting when the reference to the task is released by handleDidChange.
-- when that happens, the request should send a "content changed" error to the user.
-- (this way, the server doesn't get bogged down in requests for an old state of the document)
-- requests need to manually check for whether their task has been cancelled, so that they
-- can reply with a RequestCancelled error.
def handleHover (p : HoverParams) (e : EditableDocument) : IO Unit := pure ⟨⟩

def parseParams (paramType : Type*) [HasFromJson paramType] (params : Json) : ServerM paramType :=
match fromJson? params with
| some parsed => pure parsed
| none        => throwServerError $ "Got param with wrong structure: " ++ params.compress

def handleNotification (method : String) (params : Json) : ServerM Unit := do
let h := (fun paramType [HasFromJson paramType] (handler : paramType → ServerM Unit) =>
  parseParams paramType params >>= handler);
match method with
| "textDocument/didChange" => h DidChangeTextDocumentParams handleDidChange
| "$/cancelRequest"        => h CancelParams handleCancelRequest
| _                        => throwServerError $ "Got unsupported notification method: " ++ method

def queueRequest {α : Type*} (id : RequestID) (handler : α → EditableDocument → IO Unit) (params : α)
  : ServerM Unit := do
doc ← getDocument;
requestTask ← monadLift $ asTask (handler params doc);
updatePendingRequests (fun pendingRequests => pendingRequests.insert id requestTask)

def handleRequest (id : RequestID) (method : String) (params : Json)
  : ServerM Unit := do
let h := (fun paramType [HasFromJson paramType]
              (handler : paramType → EditableDocument → IO Unit) =>
           parseParams paramType params >>= queueRequest id handler);
match method with
| "textDocument/hover" => h HoverParams handleHover
| _ => throwServerError $ "Got unsupported request: " ++ method ++
                          "; params: " ++ toString params

partial def mainLoop : Unit → ServerM Unit
| () => do
  st ← read;
  msg ← readLspMessage st.hIn;
  pendingRequests ← st.pendingRequestsRef.get;
  let filterFinishedTasks : PendingRequestMap → RequestID → Task (Except IO.Error Unit) → IO PendingRequestMap :=
    (fun acc id task => do
      f ← hasFinished task;
      pure $ if f then
        acc.erase id
      else
        acc);
  pendingRequests ← monadLift $ pendingRequests.foldM filterFinishedTasks pendingRequests;
  st.pendingRequestsRef.set pendingRequests;
  match msg with
  | Message.request id method (some params) => do
    handleRequest id method (toJson params);
    mainLoop ()
  | Message.notification "exit" none => do
    -- should be sufficient to shut down the file worker.
    -- references are lost => tasks are marked as cancelled
    -- => all tasks eventually quit
    pure ()
  | Message.notification method (some params) => do
    handleNotification method (toJson params);
    mainLoop ()
  | _ => throwServerError "Got invalid JSON-RPC message"

def initAndRunWorker (i o e : FS.Stream) : IO Unit := do
i ← maybeTee "fwIn.txt" false i;
o ← maybeTee "fwOut.txt" true o;
e ← maybeTee "fwErr.txt" true e;
-- TODO(WN): act in accordance with InitializeParams
_ ← Lsp.readLspRequestAs i "initialize" InitializeParams;
param ← Lsp.readLspNotificationAs i "textDocument/didOpen" DidOpenTextDocumentParams;
_ ← IO.setStderr e; -- TODO(WN): use a stream var in WorkerM instead of global state
doc ← openDocument o param;
docRef ← IO.mkRef doc;
pendingRequestsRef ← IO.mkRef (RBMap.empty : PendingRequestMap);
runReader (mainLoop ())
  { hIn := i,
    hOut := o,
    docRef := docRef,
    pendingRequestsRef := pendingRequestsRef
    : ServerContext }

namespace Test

def runWorkerWithInputFile (fn : String) (searchPath : Option String) : IO Unit := do
o ← IO.getStdout;
e ← IO.getStderr;
FS.withFile fn FS.Mode.read (fun hFile => do
  Lean.initSearchPath searchPath;
  catch
    (Lean.Server.initAndRunWorker (FS.Stream.ofHandle hFile) o e)
    (fun err => e.putStrLn (toString err)))

end Test
end Server
end Lean

def main (args : List String) : IO UInt32 := do
i ← IO.getStdin;
o ← IO.getStdout;
e ← IO.getStderr;
Lean.initSearchPath;
catch
  (Lean.Server.initAndRunWorker i o e)
  (fun err => e.putStrLn (toString err));
pure 0
