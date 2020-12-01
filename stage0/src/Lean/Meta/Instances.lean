/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.DiscrTree

namespace Lean.Meta

structure InstanceEntry where
  keys        : Array DiscrTree.Key
  val         : Expr
  globalName? : Option Name := none

structure Instances where
  discrTree       : DiscrTree Expr := DiscrTree.empty
  globalInstances : NameSet := {}

instance : Inhabited Instances where
  default := {}

def addInstanceEntry (d : Instances) (e : InstanceEntry) : Instances := {
  d with
    discrTree := d.discrTree.insertCore e.keys e.val
    globalInstances := match e.globalName? with
      | some n => d.globalInstances.insert n
      | none   => d.globalInstances
}

builtin_initialize instanceExtension : SimplePersistentEnvExtension InstanceEntry Instances ←
  registerSimplePersistentEnvExtension {
    name          := `instanceExt,
    addEntryFn    := addInstanceEntry,
    addImportedFn := fun es => (mkStateFromImportedEntries addInstanceEntry {} es)
  }

private def mkInstanceKey (e : Expr) : MetaM (Array DiscrTree.Key) := do
  let type ← inferType e
  withNewMCtxDepth do
    let (_, _, type) ← forallMetaTelescopeReducing type
    DiscrTree.mkPath type

@[export lean_add_instance]
def addGlobalInstanceImp (env : Environment) (constName : Name) : IO Environment := do
  match env.find? constName with
  | none => throw <| IO.userError s!"unknown constant '{constName}'"
  | some cinfo =>
    let c := mkConst constName (cinfo.lparams.map mkLevelParam)
    let (keys, s, _) ← (mkInstanceKey c).toIO {} { env := env } {} {}
    return instanceExtension.addEntry s.env { keys := keys, val := c, globalName? := constName }

def addGlobalInstance [Monad m] [MonadEnv m] [MonadLiftT IO m] (declName : Name) : m Unit := do
  let env ← getEnv
  let env ← Meta.addGlobalInstanceImp env declName
  setEnv env

builtin_initialize
  registerBuiltinAttribute {
    name  := `instance,
    descr := "type class instance",
    add   := fun declName args persistent => do
      if args.hasArgs then throwError "invalid attribute 'instance', unexpected argument"
      unless persistent do throwError "invalid attribute 'instance', must be persistent"
      addGlobalInstance declName
  }

@[export lean_is_instance]
def isGlobalInstance (env : Environment) (declName : Name) : Bool :=
  Meta.instanceExtension.getState env |>.globalInstances.contains declName

def getGlobalInstancesIndex : MetaM (DiscrTree Expr) :=
  return Meta.instanceExtension.getState (← getEnv) |>.discrTree

/- Default instance support -/

structure DefaultInstanceEntry where
  className    : Name
  instanceName : Name
  priority     : Nat

abbrev PrioritySet := Std.RBTree Nat (.>.)

structure DefaultInstances where
  defaultInstances : NameMap (List (Name × Nat)) := {}
  priorities       : PrioritySet := {}

instance : Inhabited DefaultInstances where
  default := {}

def addDefaultInstanceEntry (d : DefaultInstances) (e : DefaultInstanceEntry) : DefaultInstances :=
  let d := { d with priorities := d.priorities.insert e.priority }
  match d.defaultInstances.find? e.className with
  | some insts => { d with defaultInstances := d.defaultInstances.insert e.className <| (e.instanceName, e.priority) :: insts }
  | none       => { d with defaultInstances := d.defaultInstances.insert e.className [(e.instanceName, e.priority)] }

builtin_initialize defaultInstanceExtension : SimplePersistentEnvExtension DefaultInstanceEntry DefaultInstances ←
  registerSimplePersistentEnvExtension {
    name          := `defaultInstanceExt,
    addEntryFn    := addDefaultInstanceEntry,
    addImportedFn := fun es => (mkStateFromImportedEntries addDefaultInstanceEntry {} es)
  }

def addDefaultInstance (declName : Name) (prio : Nat := 0) : MetaM Unit := do
  match (← getEnv).find? declName with
  | none => throwError! "unknown constant '{declName}'"
  | some info =>
    forallTelescopeReducing info.type fun _ type => do
      match type.getAppFn with
      | Expr.const className _ _ =>
        unless isClass (← getEnv) className do
          throwError! "invalid default instance '{declName}', it has type '({className} ...)', but {className}' is not a type class"
        setEnv <| defaultInstanceExtension.addEntry (← getEnv) { className := className, instanceName := declName, priority := prio }
      | _ => throwError! "invalid default instance '{declName}', type must be of the form '(C ...)' where 'C' is a type class"

builtin_initialize
  registerBuiltinAttribute {
    name  := `defaultInstance,
    descr := "type class default instance",
    add   := fun declName args persistent => do
      let prio ←
        if args.getNumArgs == 0 then
          pure 0
        else if args.getNumArgs == 1 then
          match args[0].isNatLit? with
          | none => throwErrorAt args[0] "unexpected argument at attribute 'defaultInstance', numeral expected"
          | some n => pure n
        else
          throwErrorAt args "too many arguments at attribute 'defaultInstance', numeral expected"
      unless persistent do throwError "invalid attribute 'defaultInstance', must be persistent"
      addDefaultInstance declName prio |>.run {} {}
      pure ()
  }

def getDefaultInstancesPriorities [Monad m] [MonadEnv m] : m PrioritySet :=
  return defaultInstanceExtension.getState (← getEnv) |>.priorities

def getDefaultInstances [Monad m] [MonadEnv m] (className : Name) : m (List (Name × Nat)) :=
  return defaultInstanceExtension.getState (← getEnv) |>.defaultInstances.find? className |>.getD []

end Lean.Meta
