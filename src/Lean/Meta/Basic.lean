/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.LOption
import Lean.Environment
import Lean.Class
import Lean.ReducibilityAttrs
import Lean.Util.Trace
import Lean.Util.RecDepth
import Lean.Util.PPExt
import Lean.Compiler.InlineAttrs
import Lean.Meta.Exception
import Lean.Meta.TransparencyMode
import Lean.Meta.DiscrTreeTypes
import Lean.Eval
import Lean.CoreM

/-
This module provides four (mutually dependent) goodies that are needed for building the elaborator and tactic frameworks.
1- Weak head normal form computation with support for metavariables and transparency modes.
2- Definitionally equality checking with support for metavariables (aka unification modulo definitional equality).
3- Type inference.
4- Type class resolution.

They are packed into the MetaM monad.
-/

namespace Lean
namespace Meta

structure Config :=
(foApprox           : Bool := false)
(ctxApprox          : Bool := false)
(quasiPatternApprox : Bool := false)
/- When `constApprox` is set to true,
   we solve `?m t =?= c` using
   `?m := fun _ => c`
   when `?m t` is not a higher-order pattern and `c` is not an application as -/
(constApprox        : Bool := false)
/-
  When the following flag is set,
  `isDefEq` throws the exeption `Exeption.isDefEqStuck`
  whenever it encounters a constraint `?m ... =?= t` where
  `?m` is read only.
  This feature is useful for type class resolution where
  we may want to notify the caller that the TC problem may be solveable
  later after it assigns `?m`. -/
(isDefEqStuckEx     : Bool := false)
(transparency       : TransparencyMode := TransparencyMode.default)
/- If zetaNonDep == false, then non dependent let-decls are not zeta expanded. -/
(zetaNonDep         : Bool := true)
/- When `trackZeta == true`, we store zetaFVarIds all free variables that have been zeta-expanded. -/
(trackZeta          : Bool := false)

structure ParamInfo :=
(implicit     : Bool      := false)
(instImplicit : Bool      := false)
(hasFwdDeps   : Bool      := false)
(backDeps     : Array Nat := #[])

instance ParamInfo.inhabited : Inhabited ParamInfo := ⟨{}⟩

structure FunInfo :=
(paramInfo  : Array ParamInfo := #[])
(resultDeps : Array Nat       := #[])

structure InfoCacheKey :=
(transparency : TransparencyMode)
(expr         : Expr)
(nargs?       : Option Nat)

namespace InfoCacheKey
instance : Inhabited InfoCacheKey := ⟨⟨arbitrary _, arbitrary _, arbitrary _⟩⟩
instance : Hashable InfoCacheKey :=
⟨fun ⟨transparency, expr, nargs⟩ => mixHash (hash transparency) $ mixHash (hash expr) (hash nargs)⟩
instance : HasBeq InfoCacheKey :=
⟨fun ⟨t₁, e₁, n₁⟩ ⟨t₂, e₂, n₂⟩ => t₁ == t₂ && n₁ == n₂ && e₁ == e₂⟩
end InfoCacheKey

open Std (PersistentArray PersistentHashMap)

abbrev SynthInstanceCache := PersistentHashMap Expr (Option Expr)

structure Cache :=
(inferType     : PersistentExprStructMap Expr := {})
(funInfo       : PersistentHashMap InfoCacheKey FunInfo := {})
(synthInstance : SynthInstanceCache := {})
(whnfDefault   : PersistentExprStructMap Expr := {}) -- cache for closed terms and `TransparencyMode.default`
(whnfAll       : PersistentExprStructMap Expr := {}) -- cache for closed terms and `TransparencyMode.all`

structure State :=
(mctx        : MetavarContext := {})
(cache       : Cache := {})
/- When `trackZeta == true`, then any let-decl free variable that is zeta expansion performed by `MetaM` is stored in `zetaFVarIds`. -/
(zetaFVarIds : NameSet := {})

instance State.inhabited : Inhabited State := ⟨{}⟩

structure Context :=
(config         : Config         := {})
(lctx           : LocalContext   := {})
(localInstances : LocalInstances := #[])

abbrev MetaM  := ReaderT Context $ StateRefT State $ CoreM

structure PostponedEntry :=
(lhs       : Level)
(rhs       : Level)

abbrev DefEqM := StateRefT (PersistentArray PostponedEntry) MetaM

instance : MonadIO MetaM :=
{ liftIO := fun α x => liftM (liftIO x : CoreM α) }

instance MetaM.inhabited {α} : Inhabited (MetaM α) :=
⟨fun _ _ => arbitrary _⟩

instance : MonadLCtx MetaM :=
{ getLCtx := do ctx ← read; pure ctx.lctx }

instance : MonadMCtx MetaM :=
{ getMCtx := do s ← get; pure s.mctx }

instance : AddMessageContext MetaM :=
{ addMessageContext := addMessageContextFull }

instance : Ref MetaM :=
{ getRef     := getRef,
  withRef    := fun α => withRef }

@[inline] def MetaM.run {α} (x : MetaM α) (ctx : Context := {}) (s : State := {}) : CoreM (α × State) :=
(x.run ctx).run s

@[inline] def MetaM.run' {α} (x : MetaM α) (ctx : Context := {}) (s : State := {}) : CoreM α :=
Prod.fst <$> x.run ctx s

@[inline] def MetaM.toIO {α} (x : MetaM α) (ctxCore : Core.Context) (sCore : Core.State) (ctx : Context := {}) (s : State := {}) : IO (α × Core.State × State) := do
((a, s), sCore) ← (x.run ctx s).toIO ctxCore sCore;
pure (a, sCore, s)

instance hasEval {α} [MetaHasEval α] : MetaHasEval (MetaM α) :=
⟨fun env opts x _ => MetaHasEval.eval env opts $ x.run'⟩

protected def throwIsDefEqStuck {α} : DefEqM α :=
throw $ Exception.internal isDefEqStuckExceptionId

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Meta;
registerTraceClass `Meta.debug

@[inline] def liftMetaM {α m} [MonadLiftT MetaM m] (x : MetaM α) : m α :=
liftM x

@[inline] def mapMetaM {m} [MonadControlT MetaM m] [Monad m] (f : forall {α}, MetaM α → MetaM α) {α} (x : m α) : m α :=
controlAt MetaM fun runInBase => f $ runInBase x

@[inline] def map1MetaM {β m} [MonadControlT MetaM m] [Monad m] (f : forall {α}, (β → MetaM α) → MetaM α) {α} (k : β → m α) : m α :=
controlAt MetaM fun runInBase => f fun b => runInBase $ k b

@[inline] def map2MetaM {β γ m} [MonadControlT MetaM m] [Monad m] (f : forall {α}, (β → γ → MetaM α) → MetaM α) {α} (k : β → γ → m α) : m α :=
controlAt MetaM fun runInBase => f fun b c => runInBase $ k b c

section Methods
variables {m : Type → Type} [MonadLiftT MetaM m]
variables {n : Type → Type} [MonadControlT MetaM n] [Monad n]

def getLocalInstances : m LocalInstances := liftMetaM do ctx ← read; pure ctx.localInstances
def getConfig : m Config := liftMetaM do ctx ← read; pure ctx.config
def setMCtx (mctx : MetavarContext) : m Unit := liftMetaM $ modify fun s => { s with mctx := mctx }
@[inline] def modifyMCtx (f : MetavarContext → MetavarContext) : m Unit :=
liftMetaM $ modify fun s => { s with mctx := f s.mctx }
def resetZetaFVarIds : m Unit := liftMetaM $ modify fun s => { s with zetaFVarIds := {} }
def getZetaFVarIds : m NameSet := liftMetaM do s ← get; pure s.zetaFVarIds

def mkWHNFRef : IO (IO.Ref (Expr → MetaM Expr)) :=
IO.mkRef $ fun _ => throwError "whnf implementation was not set"

@[init mkWHNFRef] def whnfRef : IO.Ref (Expr → MetaM Expr) := arbitrary _

def mkInferTypeRef : IO (IO.Ref (Expr → MetaM Expr)) :=
IO.mkRef $ fun _ => throwError "inferType implementation was not set"

@[init mkInferTypeRef] def inferTypeRef : IO.Ref (Expr → MetaM Expr) := arbitrary _

def mkIsExprDefEqAuxRef : IO (IO.Ref (Expr → Expr → DefEqM Bool)) :=
IO.mkRef $ fun _ _ => throwError "isDefEq implementation was not set"

@[init mkIsExprDefEqAuxRef] def isExprDefEqAuxRef : IO.Ref (Expr → Expr → DefEqM Bool) := arbitrary _

def mkSynthPendingRef : IO (IO.Ref (MVarId → MetaM Bool)) :=
IO.mkRef $ fun _ => pure false

@[init mkSynthPendingRef] def synthPendingRef : IO.Ref (MVarId → MetaM Bool) := arbitrary _

def whnf (e : Expr) : m Expr :=
liftMetaM $ withIncRecDepth do
  fn ← liftIO whnfRef.get;
  fn e

def whnfForall [Monad m] (e : Expr) : m Expr := do
e' ← whnf e;
if e'.isForall then pure e' else pure e

def inferType (e : Expr) : m Expr :=
liftMetaM $ withIncRecDepth do
  fn ← liftIO inferTypeRef.get;
  fn e

protected def isExprDefEqAux (t s : Expr) : DefEqM Bool :=
withIncRecDepth do
  fn ← liftIO isExprDefEqAuxRef.get;
  fn t s

protected def synthPending (mvarId : MVarId) : MetaM Bool :=
withIncRecDepth do
  fn ← liftIO synthPendingRef.get;
  fn mvarId

private def mkFreshExprMVarAtCore
    (mvarId : MVarId) (lctx : LocalContext) (localInsts : LocalInstances) (type : Expr) (kind : MetavarKind) (userName : Name) : MetaM Expr := do
modifyMCtx fun mctx => mctx.addExprMVarDecl mvarId userName lctx localInsts type kind;
pure $ mkMVar mvarId

def mkFreshExprMVarAt
    (lctx : LocalContext) (localInsts : LocalInstances) (type : Expr) (kind : MetavarKind := MetavarKind.natural) (userName : Name := Name.anonymous)
    : m Expr := liftMetaM do
mvarId ← mkFreshId;
mkFreshExprMVarAtCore mvarId lctx localInsts type kind userName

def mkFreshLevelMVar : m Level := liftMetaM do
mvarId ← mkFreshId;
modifyMCtx fun mctx => mctx.addLevelMVarDecl mvarId;
pure $ mkLevelMVar mvarId

private def mkFreshExprMVarCore (type : Expr) (kind : MetavarKind) (userName : Name) : MetaM Expr := do
lctx ← getLCtx;
localInsts ← getLocalInstances;
mkFreshExprMVarAt lctx localInsts type kind userName

private def mkFreshExprMVarImpl (type? : Option Expr) (kind : MetavarKind) (userName : Name) : MetaM Expr :=
match type? with
| some type => mkFreshExprMVarCore type kind userName
| none      => do
  u ← mkFreshLevelMVar;
  type ← mkFreshExprMVarCore (mkSort u) MetavarKind.natural Name.anonymous;
  mkFreshExprMVarCore type kind userName

def mkFreshExprMVar (type? : Option Expr) (kind := MetavarKind.natural) (userName := Name.anonymous) : m Expr :=
liftMetaM $ mkFreshExprMVarImpl type? kind userName

def mkFreshTypeMVar (kind := MetavarKind.natural) (userName := Name.anonymous) : m Expr := liftMetaM do
u ← mkFreshLevelMVar; mkFreshExprMVar (mkSort u) kind userName

/- Low-level version of `MkFreshExprMVar` which allows users to create/reserve a `mvarId` using `mkFreshId`, and then later create
   the metavar using this method. -/
private def mkFreshExprMVarWithIdCore (mvarId : MVarId) (type : Expr) (kind : MetavarKind := MetavarKind.natural) (userName : Name := Name.anonymous)
    : m Expr := liftMetaM do
lctx ← getLCtx;
localInsts ← getLocalInstances;
mkFreshExprMVarAtCore mvarId lctx localInsts type kind userName

def mkFreshExprMVarWithIdImpl (mvarId : MVarId) (type? : Option Expr) (kind : MetavarKind) (userName : Name) : MetaM Expr :=
match type? with
| some type => mkFreshExprMVarWithIdCore mvarId type kind userName
| none      => do
  u ← mkFreshLevelMVar;
  type ← mkFreshExprMVar (mkSort u);
  mkFreshExprMVarWithIdCore mvarId type kind userName

def mkFreshExprMVarWithId (mvarId : MVarId) (type? : Option Expr := none) (kind : MetavarKind := MetavarKind.natural) (userName := Name.anonymous) : m Expr :=
liftMetaM $ mkFreshExprMVarWithIdImpl mvarId type? kind userName

def shouldReduceAll : MetaM Bool := liftMetaM do
ctx ← read; pure $ ctx.config.transparency == TransparencyMode.all
def shouldReduceReducibleOnly : m Bool := liftMetaM do
ctx ← read; pure $ ctx.config.transparency == TransparencyMode.reducible
def getTransparency : m TransparencyMode := liftMetaM do
ctx ← read; pure $ ctx.config.transparency

-- Remark: wanted to use `private`, but in the C++ parser, `private` declarations do not shadow outer public ones.
-- TODO: fix this bug
def isReducible (constName : Name) : MetaM Bool := do
env ← getEnv; pure $ isReducible env constName

def getMVarDecl (mvarId : MVarId) : m MetavarDecl := liftMetaM do
mctx ← getMCtx;
match mctx.findDecl? mvarId with
| some d => pure d
| none   => throwError ("unknown metavariable '" ++ mkMVar mvarId ++ "'")

def setMVarKind (mvarId : MVarId) (kind : MetavarKind) : m Unit :=
modifyMCtx fun mctx => mctx.setMVarKind mvarId kind

def isReadOnlyExprMVar (mvarId : MVarId) : m Bool := liftMetaM do
mvarDecl ← getMVarDecl mvarId;
mctx     ← getMCtx;
pure $ mvarDecl.depth != mctx.depth

def isReadOnlyOrSyntheticOpaqueExprMVar (mvarId : MVarId) : m Bool := liftMetaM do
mvarDecl ← getMVarDecl mvarId;
match mvarDecl.kind with
| MetavarKind.syntheticOpaque => pure true
| _ => do
  mctx ← getMCtx;
  pure $ mvarDecl.depth != mctx.depth

def isReadOnlyLevelMVar (mvarId : MVarId) : m Bool := liftMetaM do
mctx ← getMCtx;
match mctx.findLevelDepth? mvarId with
| some depth => pure $ depth != mctx.depth
| _          => throwError ("unknown universe metavariable '" ++ mkLevelMVar mvarId ++ "'")

def renameMVar (mvarId : MVarId) (newUserName : Name) : m Unit :=
modifyMCtx fun mctx => mctx.renameMVar mvarId newUserName

def isExprMVarAssigned (mvarId : MVarId) : m Bool := liftMetaM do
mctx ← getMCtx;
pure $ mctx.isExprAssigned mvarId

def getExprMVarAssignment? (mvarId : MVarId) : m (Option Expr) := liftMetaM do
mctx ← getMCtx; pure (mctx.getExprAssignment? mvarId)

def assignExprMVar (mvarId : MVarId) (val : Expr) : m Unit := liftMetaM do
modifyMCtx fun mctx => mctx.assignExpr mvarId val

def isDelayedAssigned (mvarId : MVarId) : m Bool := liftMetaM do
mctx ← getMCtx;
pure $ mctx.isDelayedAssigned mvarId

def getDelayedAssignment? (mvarId : MVarId) : m (Option DelayedMetavarAssignment) := liftMetaM do
mctx ← getMCtx;
pure $ mctx.getDelayedAssignment? mvarId

def hasAssignableMVar (e : Expr) : m Bool := liftMetaM do
mctx ← getMCtx;
pure $ mctx.hasAssignableMVar e

def throwUnknownFVar {α} (fvarId : FVarId) : MetaM α :=
throwError ("unknown free variable '" ++ mkFVar fvarId ++ "'")

def findLocalDecl? (fvarId : FVarId) : m (Option LocalDecl) := liftMetaM do
lctx ← getLCtx;
pure $ lctx.find? fvarId

def getLocalDecl (fvarId : FVarId) : m LocalDecl := liftMetaM do
lctx ← getLCtx;
match lctx.find? fvarId with
| some d => pure d
| none   => throwUnknownFVar fvarId

def getFVarLocalDecl (fvar : Expr) : m LocalDecl := liftMetaM do
getLocalDecl fvar.fvarId!

def getLocalDeclFromUserName (userName : Name) : m LocalDecl := liftMetaM do
lctx ← getLCtx;
match lctx.findFromUserName? userName with
| some d => pure d
| none   => throwError ("unknown local declaration '" ++ userName ++ "'")

def instantiateMVars (e : Expr) : m Expr := liftMetaM do
if e.hasMVar then
  modifyGet $ fun s =>
    let (e, mctx) := s.mctx.instantiateMVars e;
    (e, { s with mctx := mctx })
else
  pure e

def instantiateLocalDeclMVars (localDecl : LocalDecl) : m LocalDecl := liftMetaM do
match localDecl with
  | LocalDecl.cdecl idx id n type bi  => do
    type ← instantiateMVars type;
    pure $ LocalDecl.cdecl idx id n type bi
  | LocalDecl.ldecl idx id n type val nonDep => do
    type ← instantiateMVars type;
    val ← instantiateMVars val;
    pure $ LocalDecl.ldecl idx id n type val nonDep

@[inline] private def liftMkBindingM {α} (x : MetavarContext.MkBindingM α) : MetaM α := do
mctx ← getMCtx;
ngen ← getNGen;
lctx ← getLCtx;
match x lctx { mctx := mctx, ngen := ngen } with
| EStateM.Result.ok e newS => do
  setNGen newS.ngen;
  setMCtx newS.mctx;
  pure e
| EStateM.Result.error (MetavarContext.MkBinding.Exception.revertFailure mctx lctx toRevert decl) newS => do
  setMCtx newS.mctx;
  setNGen newS.ngen;
  throwError "failed to create binder due to failure when reverting variable dependencies"

def mkForallFVars (xs : Array Expr) (e : Expr) : m Expr := liftMetaM do
if xs.isEmpty then pure e else liftMkBindingM $ MetavarContext.mkForall xs e

def mkLambdaFVars (xs : Array Expr) (e : Expr) : m Expr := liftMetaM do
if xs.isEmpty then pure e else liftMkBindingM $ MetavarContext.mkLambda xs e

def mkLetFVars (xs : Array Expr) (e : Expr) : m Expr :=
mkLambdaFVars xs e

def mkArrow (d b : Expr) : m Expr := liftMetaM do
n ← Core.mkFreshUserName `x;
pure $ Lean.mkForall n BinderInfo.default d b

def mkForallUsedOnly (xs : Array Expr) (e : Expr) : m (Expr × Nat) := liftMetaM do
if xs.isEmpty then pure (e, 0) else liftMkBindingM $ MetavarContext.mkForallUsedOnly xs e

def elimMVarDeps (xs : Array Expr) (e : Expr) (preserveOrder : Bool := false) : m Expr := liftMetaM do
if xs.isEmpty then pure e else liftMkBindingM $ MetavarContext.elimMVarDeps xs e preserveOrder

@[inline] def withConfig {α} (f : Config → Config) : n α → n α :=
mapMetaM fun _ => adaptReader (fun (ctx : Context) => { ctx with config := f ctx.config })

@[inline] def withTrackingZeta {α} (x : n α) : n α :=
withConfig (fun cfg => { cfg with trackZeta := true }) x

@[inline] def withTransparency {α} (mode : TransparencyMode) : n α → n α :=
mapMetaM fun _ => withConfig (fun config => { config with transparency := mode })

@[inline] def withReducible {α} (x : n α) : n α :=
withTransparency TransparencyMode.reducible x

@[inline] def withAtLeastTransparency {α} (mode : TransparencyMode) (x : n α) : n α :=
withConfig
  (fun config =>
    let oldMode := config.transparency;
    let mode    := if oldMode.lt mode then mode else oldMode;
    { config with transparency := mode })
  x

def throwUnknownConstant {α} (constName : Name) : MetaM α :=
throwError ("unknown constant '" ++ constName ++ "'")

def getConst? (constName : Name) : MetaM (Option ConstantInfo) := do
env ← getEnv;
match env.find? constName with
| some (info@(ConstantInfo.thmInfo _)) =>
  condM shouldReduceAll (pure (some info)) (pure none)
| some (info@(ConstantInfo.defnInfo _)) =>
  condM shouldReduceReducibleOnly
    (condM (isReducible constName) (pure (some info)) (pure none))
    (pure (some info))
| some info => pure (some info)
| none      => throwUnknownConstant constName

def getConstNoEx? (constName : Name) : MetaM (Option ConstantInfo) := do
env ← getEnv;
match env.find? constName with
| some (info@(ConstantInfo.thmInfo _)) =>
  condM shouldReduceAll (pure (some info)) (pure none)
| some (info@(ConstantInfo.defnInfo _)) =>
  condM shouldReduceReducibleOnly
    (condM (isReducible constName) (pure (some info)) (pure none))
    (pure (some info))
| some info => pure (some info)
| none      => pure none

/-- Save cache, execute `x`, restore cache -/
@[inline] private def savingCacheImpl {α} (x : MetaM α) : MetaM α := do
s ← get;
let savedCache := s.cache;
finally x (modify fun s => { s with cache := savedCache })

@[inline] def savingCache {α} : n α → n α :=
mapMetaM fun _ => savingCacheImpl

private def isClassQuickConst? (constName : Name) : MetaM (LOption Name) := do
env ← getEnv;
if isClass env constName then
  pure (LOption.some constName)
else do
  cinfo? ← getConst? constName;
  match cinfo? with
  | some _ => pure LOption.undef
  | none   => pure LOption.none

private partial def isClassQuick? : Expr → MetaM (LOption Name)
| Expr.bvar _ _        => pure LOption.none
| Expr.lit _ _         => pure LOption.none
| Expr.fvar _ _        => pure LOption.none
| Expr.sort _ _        => pure LOption.none
| Expr.lam _ _ _ _     => pure LOption.none
| Expr.letE _ _ _ _ _  => pure LOption.undef
| Expr.proj _ _ _  _   => pure LOption.undef
| Expr.forallE _ _ b _ => isClassQuick? b
| Expr.mdata _ e _     => isClassQuick? e
| Expr.const n _ _     => isClassQuickConst? n
| Expr.mvar mvarId _   => do
  val? ← getExprMVarAssignment? mvarId;
  match val? with
  | some val => isClassQuick? val
  | none     => pure LOption.none
| Expr.app f _ _       =>
  match f.getAppFn with
  | Expr.const n _ _  => isClassQuickConst? n
  | Expr.lam _ _ _ _  => pure LOption.undef
  | _                 => pure LOption.none
| Expr.localE _ _ _ _ => unreachable!

def saveAndResetSynthInstanceCache : MetaM SynthInstanceCache := do
s ← get;
let savedSythInstance := s.cache.synthInstance;
modify $ fun s => { s with cache := { s.cache with synthInstance := {} } };
pure savedSythInstance

def restoreSynthInstanceCache (cache : SynthInstanceCache) : MetaM Unit :=
modify $ fun s => { s with cache := { s.cache with synthInstance := cache } }

@[inline] private def resettingSynthInstanceCacheImpl {α} (x : MetaM α) : MetaM α := do
savedSythInstance ← saveAndResetSynthInstanceCache;
finally x (restoreSynthInstanceCache savedSythInstance)

/-- Reset `synthInstance` cache, execute `x`, and restore cache -/
@[inline] def resettingSynthInstanceCache {α} : n α → n α :=
mapMetaM fun _ => resettingSynthInstanceCacheImpl

@[inline] def resettingSynthInstanceCacheWhen {α} (b : Bool) (x : n α) : n α :=
if b then resettingSynthInstanceCache x else x

private def withNewLocalInstanceImp {α} (className : Name) (fvar : Expr) (k : MetaM α) : MetaM α := do
localDecl ← getFVarLocalDecl fvar;
/- Recall that we use `auxDecl` binderInfo when compiling recursive declarations. -/
match localDecl.binderInfo with
| BinderInfo.auxDecl => k
| _ =>
  resettingSynthInstanceCache $
    adaptReader
      (fun (ctx : Context) => { ctx with localInstances := ctx.localInstances.push { className := className, fvar := fvar } })
      k

/-- Add entry `{ className := className, fvar := fvar }` to localInstances,
    and then execute continuation `k`.
    It resets the type class cache using `resettingSynthInstanceCache`. -/
def withNewLocalInstance {α} (className : Name) (fvar : Expr) : n α → n α :=
mapMetaM fun _ => withNewLocalInstanceImp className fvar

/--
  `withNewLocalInstances isClassExpensive fvars j k` updates the vector or local instances
  using free variables `fvars[j] ... fvars.back`, and execute `k`.

  - `isClassExpensive` is defined later.
  - The type class chache is reset whenever a new local instance is found.
  - `isClassExpensive` uses `whnf` which depends (indirectly) on the set of local instances.
    Thus, each new local instance requires a new `resettingSynthInstanceCache`. -/
@[specialize] private partial def withNewLocalInstancesImp {α}
    (isClassExpensive? : Expr → MetaM (Option Name))
    (fvars : Array Expr) : Nat → MetaM α → MetaM α
| i, k =>
  if h : i < fvars.size then do
    let fvar := fvars.get ⟨i, h⟩;
    decl ← getFVarLocalDecl fvar;
    c?   ← isClassQuick? decl.type;
    match c? with
    | LOption.none   => withNewLocalInstancesImp (i+1) k
    | LOption.undef  => do
      c? ← isClassExpensive? decl.type;
      match c? with
      | none   => withNewLocalInstancesImp (i+1) k
      | some c => withNewLocalInstance c fvar $ withNewLocalInstancesImp (i+1) k
    | LOption.some c => withNewLocalInstance c fvar $ withNewLocalInstancesImp (i+1) k
  else
    k

private def fvarsSizeLtMaxFVars (fvars : Array Expr) (maxFVars? : Option Nat) : Bool :=
match maxFVars? with
| some maxFVars => fvars.size < maxFVars
| none          => true

/--
  `forallTelescopeAux whnf k lctx fvars j type`
  Remarks:
  - `lctx` is the `MetaM` local context exteded with the declaration for `fvars`.
  - `type` is the type we are computing the telescope for. It contains only
    dangling bound variables in the range `[j, fvars.size)`
  - if `reducing? == true` and `type` is not `forallE`, we use `whnf`.
  - when `type` is not a `forallE` nor it can't be reduced to one, we
    excute the continuation `k`.

  Here is an example that demonstrates the `reducing?`.
  Suppose we have
  ```
  abbrev StateM s a := s -> Prod a s
  ```
  Now, assume we are trying to build the telescope for
  ```
  forall (x : Nat), StateM Int Bool
  ```
  if `reducing? == true`, the function executes `k #[(x : Nat) (s : Int)] Bool`.
  if `reducing? == false`, the function executes `k #[(x : Nat)] (StateM Int Bool)`

  if `maxFVars?` is `some max`, then we interrupt the telescope construction
  when `fvars.size == max`
-/
@[specialize] private partial def forallTelescopeReducingAuxAux {α}
    (isClassExpensive? : Expr → MetaM (Option Name))
    (reducing?         : Bool) (maxFVars? : Option Nat)
    (k                 : Array Expr → Expr → MetaM α)
    : LocalContext → Array Expr → Nat → Expr → MetaM α
| lctx, fvars, j, type@(Expr.forallE n d b c) => do
  let process : Unit → MetaM α := fun _ => do {
    let d     := d.instantiateRevRange j fvars.size fvars;
    fvarId ← mkFreshId;
    let lctx  := lctx.mkLocalDecl fvarId n d c.binderInfo;
    let fvar  := mkFVar fvarId;
    let fvars := fvars.push fvar;
    forallTelescopeReducingAuxAux lctx fvars j b
  };
  if fvarsSizeLtMaxFVars fvars maxFVars? then
    process ()
  else
    let type := type.instantiateRevRange j fvars.size fvars;
    adaptReader (fun (ctx : Context) => { ctx with lctx := lctx }) $
      withNewLocalInstancesImp isClassExpensive? fvars j $
        k fvars type
| lctx, fvars, j, type =>
  let type := type.instantiateRevRange j fvars.size fvars;
  adaptReader (fun (ctx : Context) => { ctx with lctx := lctx }) $
    withNewLocalInstancesImp isClassExpensive? fvars j $
      if reducing? && fvarsSizeLtMaxFVars fvars maxFVars? then do
        newType ← whnf type;
        if newType.isForall then
          forallTelescopeReducingAuxAux lctx fvars fvars.size newType
        else
          k fvars type
      else
        k fvars type

/- We need this auxiliary definition because it depends on `isClassExpensive`,
   and `isClassExpensive` depends on it. -/
@[specialize] private def forallTelescopeReducingAux {α}
    (isClassExpensive? : Expr → MetaM (Option Name))
    (type : Expr) (maxFVars? : Option Nat) (k : Array Expr → Expr → MetaM α) : MetaM α := do
match maxFVars? with
| some 0 => k #[] type
| _ => do
  newType ← whnf type;
  if newType.isForall then do
    lctx ← getLCtx;
    forallTelescopeReducingAuxAux isClassExpensive? true maxFVars? k lctx #[] 0 newType
  else
    k #[] type

private partial def isClassExpensive? : Expr → MetaM (Option Name)
| type => withReducible $ -- when testing whether a type is a type class, we only unfold reducible constants.
  forallTelescopeReducingAux isClassExpensive? type none $ fun xs type => do
    match type.getAppFn with
    | Expr.const c _ _ => do
      env ← getEnv;
      pure $ if isClass env c then some c else none
    | _ => pure none

private def isClassImp? (type : Expr) : MetaM (Option Name) := do
c? ← isClassQuick? type;
match c? with
| LOption.none   => pure none
| LOption.some c => pure (some c)
| LOption.undef  => isClassExpensive? type

def isClass? (type : Expr) : m (Option Name) :=
liftMetaM $ catch (isClassImp? type) (fun _ => pure none)

private def withNewLocalInstancesImpAux {α} (fvars : Array Expr) (j : Nat) : n α → n α :=
mapMetaM fun _ => withNewLocalInstancesImp isClassExpensive? fvars j

def withNewLocalInstances {α} (fvars : Array Expr) (j : Nat) : n α → n α :=
mapMetaM fun _ => withNewLocalInstancesImpAux fvars j

private def forallTelescopeImp {α} (type : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
lctx ← getLCtx;
forallTelescopeReducingAuxAux isClassExpensive? false none k lctx #[] 0 type

/--
  Given `type` of the form `forall xs, A`, execute `k xs A`.
  This combinator will declare local declarations, create free variables for them,
  execute `k` with updated local context, and make sure the cache is restored after executing `k`. -/
def forallTelescope {α} (type : Expr) (k : Array Expr → Expr → n α) : n α :=
map2MetaM (fun _ k => forallTelescopeImp type k) k

@[noinline] private def forallTelescopeReducingImp {α} (type : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α :=
forallTelescopeReducingAux isClassExpensive? type none k

/--
  Similar to `forallTelescope`, but given `type` of the form `forall xs, A`,
  it reduces `A` and continues bulding the telescope if it is a `forall`. -/
def forallTelescopeReducing {α} (type : Expr) (k : Array Expr → Expr → n α) : n α :=
map2MetaM (fun _ k => forallTelescopeReducingImp type k) k

@[noinline] private def forallBoundedTelescopeImp {α} (type : Expr) (maxFVars? : Option Nat) (k : Array Expr → Expr → MetaM α) : MetaM α :=
forallTelescopeReducingAux isClassExpensive? type maxFVars? k

/--
  Similar to `forallTelescopeReducing`, stops constructing the telescope when
  it reaches size `maxFVars`. -/
def forallBoundedTelescope {α} (type : Expr) (maxFVars? : Option Nat) (k : Array Expr → Expr → n α) : n α :=
map2MetaM (fun _ k => forallBoundedTelescopeImp type maxFVars? k) k

/-- Similar to `forallTelescopeAuxAux` but for lambda and let expressions. -/
private partial def lambdaTelescopeAux {α}
    (k : Array Expr → Expr → MetaM α)
    : Bool → LocalContext → Array Expr → Nat → Expr → MetaM α
| consumeLet, lctx, fvars, j, Expr.lam n d b c => do
  let d := d.instantiateRevRange j fvars.size fvars;
  fvarId ← mkFreshId;
  let lctx := lctx.mkLocalDecl fvarId n d c.binderInfo;
  let fvar := mkFVar fvarId;
  lambdaTelescopeAux consumeLet lctx (fvars.push fvar) j b
| true, lctx, fvars, j, Expr.letE n t v b _ => do
  let t := t.instantiateRevRange j fvars.size fvars;
  let v := v.instantiateRevRange j fvars.size fvars;
  fvarId ← mkFreshId;
  let lctx := lctx.mkLetDecl fvarId n t v;
  let fvar := mkFVar fvarId;
  lambdaTelescopeAux true lctx (fvars.push fvar) j b
| _, lctx, fvars, j, e =>
  let e := e.instantiateRevRange j fvars.size fvars;
  adaptReader (fun (ctx : Context) => { ctx with lctx := lctx }) $
    withNewLocalInstancesImp isClassExpensive? fvars j $ do
      k fvars e

private def lambdaTelescopeImp {α} (e : Expr) (consumeLet : Bool) (k : Array Expr → Expr → MetaM α) : MetaM α := do
lctx ← getLCtx;
lambdaTelescopeAux k consumeLet lctx #[] 0 e

/-- Similar to `forallTelescope` but for lambda and let expressions. -/
def lambdaLetTelescope {α} (type : Expr) (k : Array Expr → Expr → n α) : n α :=
map2MetaM (fun _ k => lambdaTelescopeImp type true k) k

/-- Similar to `forallTelescope` but for lambda expressions. -/
def lambdaTelescope {α} (type : Expr) (k : Array Expr → Expr → n α) : n α :=
map2MetaM (fun _ k => lambdaTelescopeImp type false k) k

def getParamNamesImp (declName : Name) : MetaM (Array Name) := do
cinfo ← getConstInfo declName;
forallTelescopeReducing cinfo.type $ fun xs _ => do
  xs.mapM $ fun x => do
    localDecl ← getLocalDecl x.fvarId!;
    pure localDecl.userName

/-- Return the parameter names for the givel global declaration. -/
def getParamNames (declName : Name) : m (Array Name) :=
liftMetaM $ getParamNamesImp declName

-- `kind` specifies the metavariable kind for metavariables not corresponding to instance implicit `[ ... ]` arguments.
private partial def forallMetaTelescopeReducingAux
    (reducing? : Bool) (maxMVars? : Option Nat) (kind : MetavarKind)
    : Array Expr → Array BinderInfo → Nat → Expr → MetaM (Array Expr × Array BinderInfo × Expr)
| mvars, bis, j, type@(Expr.forallE n d b c) => do
  let process : Unit → MetaM (Array Expr × Array BinderInfo × Expr) := fun _ => do {
    let d  := d.instantiateRevRange j mvars.size mvars;
    let k  := if c.binderInfo.isInstImplicit then  MetavarKind.synthetic else kind;
    mvar ← mkFreshExprMVar d k n;
    let mvars := mvars.push mvar;
    let bis   := bis.push c.binderInfo;
    forallMetaTelescopeReducingAux mvars bis j b
  };
  match maxMVars? with
  | none          => process ()
  | some maxMVars =>
    if mvars.size < maxMVars then
      process ()
    else
      let type := type.instantiateRevRange j mvars.size mvars;
      pure (mvars, bis, type)
| mvars, bis, j, type =>
  let type := type.instantiateRevRange j mvars.size mvars;
  if reducing? then do
    newType ← whnf type;
    if newType.isForall then
      forallMetaTelescopeReducingAux mvars bis mvars.size newType
    else
      pure (mvars, bis, type)
  else
    pure (mvars, bis, type)

/-- Similar to `forallTelescope`, but creates metavariables instead of free variables. -/
def forallMetaTelescope (e : Expr) (kind := MetavarKind.natural) : m (Array Expr × Array BinderInfo × Expr) :=
liftMetaM $ forallMetaTelescopeReducingAux false none kind #[] #[] 0 e

/-- Similar to `forallTelescopeReducing`, but creates metavariables instead of free variables. -/
def forallMetaTelescopeReducing (e : Expr) (maxMVars? : Option Nat := none) (kind := MetavarKind.natural) : m (Array Expr × Array BinderInfo × Expr) :=
liftMetaM $ forallMetaTelescopeReducingAux true maxMVars? kind #[] #[] 0 e

/-- Similar to `forallMetaTelescopeReducingAux` but for lambda expressions. -/
private partial def lambdaMetaTelescopeAux (maxMVars? : Option Nat)
    : Array Expr → Array BinderInfo → Nat → Expr → MetaM (Array Expr × Array BinderInfo × Expr)
| mvars, bis, j, type => do
  let finalize : Unit → MetaM (Array Expr × Array BinderInfo × Expr) := fun _ => do {
    let type := type.instantiateRevRange j mvars.size mvars;
    pure (mvars, bis, type)
  };
  let process : Unit → MetaM (Array Expr × Array BinderInfo × Expr) := fun _ => do {
    match type with
    | Expr.lam n d b c => do
      let d     := d.instantiateRevRange j mvars.size mvars;
      mvar ← mkFreshExprMVar d;
      let mvars := mvars.push mvar;
      let bis   := bis.push c.binderInfo;
      lambdaMetaTelescopeAux mvars bis j b
    | _ => finalize ()
  };
  match maxMVars? with
  | none          => process ()
  | some maxMVars =>
    if mvars.size < maxMVars then
      process ()
    else
      finalize ()

/-- Similar to `forallMetaTelescope` but for lambda expressions. -/
def lambdaMetaTelescope (e : Expr) (maxMVars? : Option Nat := none) : m (Array Expr × Array BinderInfo × Expr) :=
liftMetaM $ lambdaMetaTelescopeAux maxMVars? #[] #[] 0 e

private def withNewFVar {α} (fvar fvarType : Expr) (k : Expr → MetaM α) : MetaM α := do
c? ← isClass? fvarType;
match c? with
| none   => k fvar
| some c => withNewLocalInstance c fvar $ k fvar

private def withLocalDeclImp {α} (n : Name) (bi : BinderInfo) (type : Expr) (k : Expr → MetaM α) : MetaM α := do
fvarId ← mkFreshId;
ctx ← read;
let lctx := ctx.lctx.mkLocalDecl fvarId n type bi;
let fvar := mkFVar fvarId;
adaptReader (fun (ctx : Context) => { ctx with lctx := lctx }) $
  withNewFVar fvar type k

def withLocalDecl {α} (name : Name) (bi : BinderInfo) (type : Expr) (k : Expr → n α) : n α :=
map1MetaM (fun _ k => withLocalDeclImp name bi type k) k

def withLocalDeclD {α} (name : Name) (type : Expr) (k : Expr → n α) : n α :=
withLocalDecl name BinderInfo.default type k

private def withLetDeclImp {α} (n : Name) (type : Expr) (val : Expr) (k : Expr → MetaM α) : MetaM α := do
fvarId ← mkFreshId;
ctx ← read;
let lctx := ctx.lctx.mkLetDecl fvarId n type val;
let fvar := mkFVar fvarId;
adaptReader (fun (ctx : Context) => { ctx with lctx := lctx }) $
  withNewFVar fvar type k

def withLetDecl {α} (name : Name) (type : Expr) (val : Expr) (k : Expr → n α) : n α :=
map1MetaM (fun _ k => withLetDeclImp name type val k) k

private def withExistingLocalDeclsImp {α} (decls : List LocalDecl) (k : MetaM α) : MetaM α := do
ctx ← read;
let numLocalInstances := ctx.localInstances.size;
let lctx := decls.foldl (fun (lctx : LocalContext) decl => lctx.addDecl decl) ctx.lctx;
adaptReader (fun (ctx : Context) => { ctx with lctx := lctx }) do
  newLocalInsts ← decls.foldlM
    (fun (newlocalInsts : Array LocalInstance) (decl : LocalDecl) => (do {
      c? ← isClass? decl.type;
      match c? with
      | none   => pure newlocalInsts
      | some c => pure $ newlocalInsts.push { className := c, fvar := decl.toExpr } } : MetaM _))
    ctx.localInstances;
  if newLocalInsts.size == numLocalInstances then
    k
  else
    resettingSynthInstanceCache $ adaptReader (fun (ctx : Context) => { ctx with localInstances := newLocalInsts }) k

def withExistingLocalDecls {α} (decls : List LocalDecl) : n α → n α :=
mapMetaM fun _ => withExistingLocalDeclsImp decls

private def withNewMCtxDepthImp {α} (x : MetaM α) : MetaM α := do
s ← get;
let savedMCtx  := s.mctx;
modifyMCtx fun mctx => mctx.incDepth;
finally x (setMCtx savedMCtx)

/--
  Save cache and `MetavarContext`, bump the `MetavarContext` depth, execute `x`,
  and restore saved data. -/
def withNewMCtxDepth {α} : n α → n α :=
mapMetaM fun _ => withNewMCtxDepthImp

private def withLocalContextImp {α} (lctx : LocalContext) (localInsts : LocalInstances) (x : MetaM α) : MetaM α := do
localInstsCurr ← getLocalInstances;
adaptReader (fun (ctx : Context) => { ctx with lctx := lctx, localInstances := localInsts }) $
  if localInsts == localInstsCurr then
    x
  else
    resettingSynthInstanceCache x

def withLCtx {α} (lctx : LocalContext) (localInsts : LocalInstances) : n α → n α :=
mapMetaM fun _ => withLocalContextImp lctx localInsts

private def withMVarContextImp {α} (mvarId : MVarId) (x : MetaM α) : MetaM α := do
mvarDecl ← getMVarDecl mvarId;
withLocalContextImp mvarDecl.lctx mvarDecl.localInstances x

/--
  Execute `x` using the given metavariable `LocalContext` and `LocalInstances`.
  The type class resolution cache is flushed when executing `x` if its `LocalInstances` are
  different from the current ones. -/
def withMVarContext {α} (mvarId : MVarId) : n α → n α :=
mapMetaM fun _ => withMVarContextImp mvarId

private def withMCtxImp {α} (mctx : MetavarContext) (x : MetaM α) : MetaM α := do
mctx' ← getMCtx;
setMCtx mctx;
finally x (setMCtx mctx')

def withMCtx {α} (mctx : MetavarContext) : n α → n α :=
mapMetaM fun _ => withMCtxImp mctx

@[inline] private def approxDefEqImp {α} (x : MetaM α) : MetaM α :=
withConfig (fun config => { config with foApprox := true, ctxApprox := true, quasiPatternApprox := true}) x

/-- Execute `x` using approximate unification: `foApprox`, `ctxApprox` and `quasiPatternApprox`.  -/
@[inline] def approxDefEq {α} : n α → n α :=
mapMetaM fun _ => approxDefEqImp

@[inline] private def fullApproxDefEqImp {α} (x : MetaM α) : MetaM α :=
withConfig (fun config => { config with foApprox := true, ctxApprox := true, quasiPatternApprox := true, constApprox := true }) x

/--
  Similar to `approxDefEq`, but uses all available approximations.
  We don't use `constApprox` by default at `approxDefEq` because it often produces undesirable solution for monadic code.
  For example, suppose we have `pure (x > 0)` which has type `?m Prop`. We also have the goal `[HasPure ?m]`.
  Now, assume the expected type is `IO Bool`. Then, the unification constraint `?m Prop =?= IO Bool` could be solved
  as `?m := fun _ => IO Bool` using `constApprox`, but this spurious solution would generate a failure when we try to
  solve `[HasPure (fun _ => IO Bool)]` -/
@[inline] def fullApproxDefEq {α} : n α → n α :=
mapMetaM fun _ => fullApproxDefEqImp

@[inline] private def liftStateMCtx {α} (x : StateM MetavarContext α) : MetaM α := do
mctx ← getMCtx;
let (a, mctx) := x.run mctx;
setMCtx mctx;
pure a

def instantiateLevelMVars (u : Level) : m Level :=
liftMetaM $ liftStateMCtx $ MetavarContext.instantiateLevelMVars u

def normalizeLevel (u : Level) : m Level :=
liftMetaM do u ← instantiateLevelMVars u; pure u.normalize

def assignLevelMVar (mvarId : MVarId) (u : Level) : m Unit :=
modifyMCtx fun mctx => mctx.assignLevel mvarId u

def whnfD [MonadLiftT MetaM n] (e : Expr) : n Expr :=
withTransparency TransparencyMode.default $ whnf e

def setInlineAttribute (declName : Name) (kind := Compiler.InlineAttributeKind.inline): m Unit := liftMetaM do
env ← getEnv;
match Compiler.setInlineAttribute env declName kind with
| Except.ok env    => setEnv env
| Except.error msg => throwError msg

private partial def instantiateForallAux (ps : Array Expr) : Nat → Expr → MetaM Expr
| i, e =>
  if h : i < ps.size then do
    let p := ps.get ⟨i, h⟩;
    e ← whnf e;
    match e with
    | Expr.forallE _ _ b _ => instantiateForallAux (i+1) (b.instantiate1 p)
    | _                    => throwError "invalid instantiateForall, too many parameters"
  else
    pure e

/- Given `e` of the form `forall (a_1 : A_1) ... (a_n : A_n), B[a_1, ..., a_n]` and `p_1 : A_1, ... p_n : A_n`, return `B[p_1, ..., p_n]`. -/
def instantiateForall (e : Expr) (ps : Array Expr) : m Expr :=
liftMetaM $ instantiateForallAux ps 0 e

private partial def instantiateLambdaAux (ps : Array Expr) : Nat → Expr → MetaM Expr
| i, e =>
  if h : i < ps.size then do
    let p := ps.get ⟨i, h⟩;
    e ← whnf e;
    match e with
    | Expr.lam _ _ b _ => instantiateLambdaAux (i+1) (b.instantiate1 p)
    | _                => throwError "invalid instantiateLambda, too many parameters"
  else
    pure e

/- Given `e` of the form `fun (a_1 : A_1) ... (a_n : A_n) => t[a_1, ..., a_n]` and `p_1 : A_1, ... p_n : A_n`, return `t[p_1, ..., p_n]`.
   It uses `whnf` to reduce `e` if it is not a lambda -/
def instantiateLambda (e : Expr) (ps : Array Expr) : m Expr :=
liftMetaM $ instantiateLambdaAux ps 0 e

/-- Return true iff `e` depends on the free variable `fvarId` -/
def dependsOn (e : Expr) (fvarId : FVarId) : m Bool := liftMetaM do
mctx ← getMCtx;
pure $ mctx.exprDependsOn e fvarId

def ppExprImp (e : Expr) : MetaM Format := do
env  ← getEnv;
mctx ← getMCtx;
lctx ← getLCtx;
opts ← getOptions;
liftIO $ Lean.ppExpr { env := env, mctx := mctx, lctx := lctx, opts := opts } e

def ppExpr (e : Expr) : m Format :=
liftMetaM $ ppExprImp e

@[inline] protected def orelse {α} (x y : MetaM α) : MetaM α := do
env  ← getEnv;
mctx ← getMCtx;
catch x (fun _ => do setEnv env; setMCtx mctx; y)

instance Meta.hasOrelse {α} : HasOrelse (MetaM α) := ⟨Meta.orelse⟩

@[inline] private def orelseMergeErrorsImp {α} (x y : MetaM α)
  (mergeRef : Syntax → Syntax → Syntax := fun r₁ r₂ => r₁)
  (mergeMsg : MessageData → MessageData → MessageData := fun m₁ m₂ => m₁ ++ Format.line ++ m₂)
  : MetaM α := do
env  ← getEnv;
mctx ← getMCtx;
catch x fun ex => do
  setEnv env; setMCtx mctx;
  match ex with
  | Exception.error ref₁ m₁ =>
    catch y fun ex => match ex with
    | Exception.error ref₂ m₂ => throw $ Exception.error (mergeRef ref₁ ref₂) (mergeMsg m₁ m₂)
    | _ => throw ex
  | _ => throw ex

/--
  Similar to `orelse`, but merge errors. Note that internal errors are not caught.
  The default `mergeRef` uses the `ref` (position information) for the first message.
  The default `mergeMsg` combines error messages using `Format.line ++ Format.line` as a separator. -/
@[inline] def orelseMergeErrors {α m} [MonadControlT MetaM m] [Monad m] (x y : m α)
  (mergeRef : Syntax → Syntax → Syntax := fun r₁ r₂ => r₁)
  (mergeMsg : MessageData → MessageData → MessageData := fun m₁ m₂ => m₁ ++ Format.line ++ Format.line ++ m₂)
  : m α := do
controlAt MetaM fun runInBase => orelseMergeErrorsImp (runInBase x) (runInBase y) mergeRef mergeMsg

/-- Execute `x`, and apply `f` to the produced error message -/
def mapErrorImp {α} (x : MetaM α) (f : MessageData → MessageData) : MetaM α :=
catch x fun ex => match ex with
  | Exception.error ref msg => throw $ Exception.error ref $ f msg
  | _ => throw ex

@[inline] def mapError {α m} [MonadControlT MetaM m] [Monad m] (x : m α) (f : MessageData → MessageData) : m α :=
controlAt MetaM fun runInBase => mapErrorImp (runInBase x) f

/-- `commitWhenSome? x` executes `x` and keep modifications when it returns `some a`. -/
@[specialize] def commitWhenSome? {α} (x? : MetaM (Option α)) : MetaM (Option α) := do
env  ← getEnv;
mctx ← getMCtx;
catch
  (do
    a? ← x?;
    match a? with
    | some a => pure a?
    | none   => do setEnv env; setMCtx mctx; pure none)
  (fun ex => do setEnv env; setMCtx mctx; throw ex)

end Methods
end Meta

export Meta (MetaM)

end Lean
