/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import private Init.Control.Reader
import private Init.Lean.NameGenerator
import private Init.Lean.Environment
import private Init.Lean.Trace
import private Init.Lean.AuxRecursor
import private Init.Lean.WHNF
import private Init.Lean.ReducibilityAttrs

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

inductive TransparencyMode
| all | default | reducible

namespace TransparencyMode
instance : Inhabited TransparencyMode := ⟨TransparencyMode.default⟩

def beq : TransparencyMode → TransparencyMode → Bool
| all,       all       => true
| default,   default   => true
| reducible, reducible => true
| _,         _         => false

instance : HasBeq TransparencyMode := ⟨beq⟩

def hash : TransparencyMode → USize
| all       => 7
| default   => 11
| reducible => 13

instance : Hashable TransparencyMode := ⟨hash⟩

end TransparencyMode

structure LocalInstance :=
(className : Name)
(fvar      : Expr)

abbrev LocalInstances := Array LocalInstance

structure Config :=
(opts               : Options := {})
(foApprox           : Bool    := false)
(ctxApprox          : Bool    := false)
(quasiPatternApprox : Bool    := false)
(transparency       : TransparencyMode := TransparencyMode.default)

structure Cache :=
(whnf      : PersistentHashMap (TransparencyMode × Expr) Expr := {})
(inferType : PersistentHashMap Expr Expr := {})

structure ExceptionContext :=
(env : Environment) (mctx : MetavarContext) (lctx : LocalContext)

inductive Exception
| unknownConst         (constName : Name) (ctx : ExceptionContext)
| unknownFVar          (fvarId : Name) (ctx : ExceptionContext)
| unknownMVar          (mvarId : Name) (ctx : ExceptionContext)
| functionExpected     (fType : Expr) (args : Array Expr) (ctx : ExceptionContext)
| incorrectNumOfLevels (constName : Name) (constLvls : List Level) (ctx : ExceptionContext)
| invalidProjection    (structName : Name) (idx : Nat) (s : Expr) (ctx : ExceptionContext)
| other                (msg : String)

structure Context :=
(config         : Config         := {})
(lctx           : LocalContext   := {})
(localInstances : LocalInstances := #[])

structure PostponedEntry :=
(lhs       : Level)
(updateLhs : Bool)
(rhs       : Level)
(updateRhs : Bool)

structure State :=
(env            : Environment)
(mctx           : MetavarContext       := {})
(cache          : Cache                := {})
(ngen           : NameGenerator        := {})
(traceState     : TraceState           := {})
(postponed      : Array PostponedEntry := #[])

abbrev MetaM := ReaderT Context (EStateM Exception State)

@[inline] private def getLCtx : MetaM LocalContext :=
do ctx ← read; pure ctx.lctx

@[inline] private def getMCtx : MetaM MetavarContext :=
do s ← get; pure s.mctx

@[inline] private def getEnv : MetaM Environment :=
do s ← get; pure s.env

@[inline] private def throwEx {α} (f : ExceptionContext → Exception) : MetaM α :=
do ctx ← read;
   s ← get;
   throw (f {env := s.env, mctx := s.mctx, lctx := ctx.lctx })

@[inline] private def reduceAll? : MetaM Bool :=
do ctx ← read; pure $ ctx.config.transparency == TransparencyMode.all

@[inline] private def reduceReducibleOnly? : MetaM Bool :=
do ctx ← read; pure $ ctx.config.transparency == TransparencyMode.reducible

@[inline] private def getTransparency : MetaM TransparencyMode :=
do ctx ← read; pure $ ctx.config.transparency

@[inline] private def getOptions : MetaM Options :=
do ctx ← read; pure ctx.config.opts

@[inline] def isReducible (n : Name) : MetaM Bool :=
do env ← getEnv; pure $ isReducible env n

@[inline] private def getTraceState : MetaM TraceState :=
do s ← get; pure s.traceState

instance tracer : SimpleMonadTracerAdapter MetaM :=
{ getOptions       := getOptions,
  getTraceState    := getTraceState,
  modifyTraceState := fun f => modify $ fun s => { traceState := f s.traceState, .. s } }

private def getConst (constName : Name) : MetaM (Option ConstantInfo) :=
do env ← getEnv;
   match env.find constName with
   | some (info@(ConstantInfo.thmInfo _)) =>
     condM reduceAll? (pure (some info)) (pure none)
   | some info                            =>
     condM reduceReducibleOnly?
       (condM (isReducible constName) (pure (some info)) (pure none))
       (pure (some info))
   | none                                 =>
     throwEx $ Exception.unknownConst constName

private def isAuxDef? (constName : Name) : MetaM Bool :=
do env ← getEnv; pure (isAuxRecursor env constName || isNoConfusion env constName)

private def getLocalDecl (fvarId : Name) : MetaM LocalDecl :=
do lctx ← getLCtx;
   match lctx.find fvarId with
   | some d => pure d
   | none   => throwEx $ Exception.unknownFVar fvarId

@[inline] private def getMVarAssignment (mvarId : Name) : MetaM (Option Expr) :=
do mctx ← getMCtx; pure (mctx.getExprAssignment mvarId)

@[inline] private def getCachedWHNF (e : Expr) : MetaM (Option Expr) :=
do t ← getTransparency;
   s ← get;
   pure $ s.cache.whnf.find (t, e)

@[inline] private def cacheWHNF (e : Expr) (r : Expr) : MetaM Unit :=
do t ← getTransparency;
   modify $ fun s => { cache := { whnf := s.cache.whnf.insert (t, e) r, .. s.cache }, .. s }

@[specialize] private partial def whnfAux
    (inferType         : Expr → MetaM Expr)
    (isDefEq           : Expr → Expr → MetaM Bool)
    (synthesizePending : Expr → MetaM Bool)
    : Expr → MetaM Expr
| e => whnfEasyCases getLocalDecl getMVarAssignment e $ fun e => do
  cached? ← getCachedWHNF e;
  match cached? with
  | some r => pure r
  | none   => do
    e ← whnfCore getConst isAuxDef? whnfAux inferType isDefEq getLocalDecl getMVarAssignment e;
    r ← unfoldDefinition getConst isAuxDef? whnfAux inferType isDefEq synthesizePending getLocalDecl getMVarAssignment e (fun _ => pure e) whnfAux;
    cacheWHNF e r;
    pure r

@[specialize] private def getForallResultType
    (whnf      : Expr → MetaM Expr)
    (fType : Expr) (args : Array Expr) : MetaM Expr :=
do (j, fType) ← args.size.foldM
     (fun i (acc : Nat × Expr) =>
       let (j, type) := acc;
       match type with
       | Expr.forallE _ _ _ b => pure (j, b)
       | _ => do
         type ← whnf $ type.instantiateRevRange j i args;
         match type with
         | Expr.forallE _ _ _ b => pure (i, b)
         | _ => throwEx $ Exception.functionExpected fType args)
     (0, fType);
   pure $ fType.instantiateRevRange j args.size args

@[specialize] private def inferAppType
    (whnf      : Expr → MetaM Expr)
    (inferType : Expr → MetaM Expr)
    (f : Expr) (args : Array Expr) : MetaM Expr :=
do fType ← inferType f;
   getForallResultType whnf fType args

private def inferConstType (c : Name) (lvls : List Level) : MetaM Expr :=
do env ← getEnv;
   match env.find c with
   | some cinfo =>
     if cinfo.lparams.length == lvls.length then
       throwEx $ Exception.incorrectNumOfLevels c lvls
     else
       pure $ cinfo.instantiateTypeLevelParams lvls
   | none =>
     throwEx $ Exception.unknownConst c

@[specialize] private def inferProjType
    (whnf      : Expr → MetaM Expr)
    (inferType : Expr → MetaM Expr)
    (structName : Name) (idx : Nat) (e : Expr) : MetaM Expr :=
do let failed : Unit → MetaM Expr := fun _ => throwEx $ Exception.invalidProjection structName idx e;
   structType ← inferType e;
   structType ← whnf structType;
   env ← getEnv;
   matchConst env structType.getAppFn failed $ fun structInfo structLvls => do
     match structInfo with
     | ConstantInfo.inductInfo { nparams := n, ctors := [ctor], .. } =>
       let structParams := structType.getAppArgs;
       if n != structParams.size then failed ()
       else match env.find ctor with
         | none            => failed ()
         | some (ctorInfo) => do
           let ctorType := ctorInfo.instantiateTypeLevelParams structLvls;
           ctorType ← getForallResultType whnf ctorType structParams;
           ctorType ← idx.foldM
             (fun i ctorType => do
               ctorType ← whnf ctorType;
               match ctorType with
               | Expr.forallE _ _ _ body =>
                 if body.hasLooseBVars then
                   pure $ body.instantiate1 $ Expr.proj structName i e
                 else
                   pure body
               | _ => failed ())
             ctorType;
           ctorType ← whnf ctorType;
           match ctorType with
           | Expr.forallE _ _ d _ => pure d
           | _                    => failed ()
     | _ => failed ()

private def inferMVarType (mvarId : Name) : MetaM Expr :=
do mctx ← getMCtx;
   match mctx.findDecl mvarId with
   | some d => pure d.type
   | none   => throwEx $ Exception.unknownMVar mvarId

private def inferFVarType (fvarId : Name) : MetaM Expr :=
do lctx ← getLCtx;
   match lctx.find fvarId with
   | some d => pure d.type
   | none   => throwEx $ Exception.unknownFVar fvarId

@[inline] private def checkInferTypeCache (e : Expr) (inferType : MetaM Expr) : MetaM Expr :=
do s ← get;
   match s.cache.inferType.find e with
   | some type => pure type
   | none => do
     type ← inferType;
     modify $ fun s => { cache := { inferType := s.cache.inferType.insert e type, .. s.cache }, .. s };
     pure type

@[specialize] private partial def inferTypeAux
    (whnf      : Expr → MetaM Expr)
    : Expr → MetaM Expr
| Expr.const c lvls     => inferConstType c lvls
| e@(Expr.proj n i s)   => checkInferTypeCache e (inferProjType whnf inferTypeAux n i s)
| e@(Expr.app f _)      => checkInferTypeCache e (inferAppType whnf inferTypeAux f e.getAppArgs)
| Expr.mvar mvarId      => inferMVarType mvarId
| Expr.fvar fvarId      => inferFVarType fvarId
| Expr.bvar _           => unreachable!
| Expr.mdata _ e        => inferTypeAux e
| Expr.lit v            => pure v.type
| Expr.sort lvl         => pure $ Expr.sort (Level.succ lvl)
| Expr.lam n bi d b     => throw $ Exception.other "not implemented yet"
| Expr.forallE n bi d b => throw $ Exception.other "not implemented yet"
| Expr.letE n t v b     => throw $ Exception.other "not implemented yet"

#exit

@[inline] private def liftStateMCtx {α} (x : StateM σ α) : TypeUtilM σ ϕ α :=
fun _ s =>
  let (a, mctx) := x.run s.mctx;
  EStateM.Result.ok a { mctx := mctx, .. s }

export AbstractMetavarContext (hasAssignableLevelMVar isReadOnlyLevelMVar auxMVarSupport getExprAssignment)

/- ===========================
   inferType
   =========================== -/
@[specialize] private def inferTypeAux
    [AbstractMetavarContext σ]
    [AbstractTypeUtilCache ϕ]
    (whnf : Expr → TypeUtilM σ ϕ Expr)
    (inferType : Expr → TypeUtilM σ ϕ Expr)
    (isDefEq : Expr → Expr → TypeUtilM σ ϕ Bool)
    : Expr → TypeUtilM σ ϕ Expr :=
fun _ => throw $ TypeUtilException.other "not implemented yet"

/- ===========================
   isDefEq for universe levels
   =========================== -/

private def instantiateLevelMVars [AbstractMetavarContext σ] (lvl : Level) : TypeUtilM σ ϕ Level :=
liftStateMCtx $ AbstractMetavarContext.instantiateLevelMVars lvl

private def assignLevel [AbstractMetavarContext σ] (mvarId : Name) (lvl : Level) : TypeUtilM σ ϕ Unit :=
modify $ fun s => { mctx := AbstractMetavarContext.assignLevel s.mctx mvarId lvl, .. s }

private def mkFreshLevelMVar [AbstractMetavarContext σ] : TypeUtilM σ ϕ Level :=
modifyGet $ fun s => (Level.mvar s.ngen.curr, { ngen := s.ngen.next, .. s })

private def strictOccursMaxAux (lvl : Level) : Level → Bool
| Level.max u v => strictOccursMaxAux u || strictOccursMaxAux v
| u             => u != lvl && lvl.occurs u

/--
  Return true iff `lvl` occurs in `max u_1 ... u_n` and `lvl != u_i` for all `i in [1, n]`.
  That is, `lvl` is a proper level subterm of some `u_i`. -/
private def strictOccursMax (lvl : Level) : Level → Bool
| Level.max u v => strictOccursMaxAux lvl u || strictOccursMaxAux lvl v
| _             => false

/-- `mkMaxArgsDiff mvarId (max u_1 ... (mvar mvarId) ... u_n) v` => `max v u_1 ... u_n` -/
private def mkMaxArgsDiff (mvarId : Name) : Level → Level → Level
| Level.max u v,     acc => mkMaxArgsDiff v $ mkMaxArgsDiff u acc
| l@(Level.mvar id), acc => if id != mvarId then Level.max acc l else acc
| l,                 acc => Level.max acc l

/--
  Solve `?m =?= max ?m v` by creating a fresh metavariable `?n`
  and assigning `?m := max ?n v` -/
private def solveSelfMax [AbstractMetavarContext σ] (mvarId : Name) (v : Level) : TypeUtilM σ ϕ Unit :=
do n ← mkFreshLevelMVar;
   let lhs := mkMaxArgsDiff mvarId v n;
   assignLevel mvarId lhs

private def postponeIsLevelDefEq (lhs : Level) (updateLhs : Bool) (rhs : Level) (updateRhs : Bool) : TypeUtilM σ ϕ Unit :=
modify $ fun s => { postponed := s.postponed.push { lhs := lhs, updateLhs := updateLhs, rhs := rhs, updateRhs := updateRhs }, .. s }

private partial def isLevelDefEqAux [AbstractMetavarContext σ] (updateLhs updateRhs : Bool) : Level → Level → TypeUtilM σ ϕ Bool
| Level.succ lhs, Level.succ rhs => isLevelDefEqAux lhs rhs
| lhs, rhs =>
  if lhs == rhs then
    pure true
  else do
    trace! `type_context.level_is_def_eq (lhs ++ " =?= " ++ rhs);
    lhs' ← instantiateLevelMVars lhs;
    let lhs' := lhs'.normalize;
    rhs' ← instantiateLevelMVars rhs;
    let rhs' := rhs'.normalize;
    if lhs != lhs' || rhs != rhs' then
      isLevelDefEqAux lhs' rhs'
    else do
      mctx ← getMCtx;
      if (!updateLhs || !hasAssignableLevelMVar mctx lhs) &&
         (!updateRhs || !hasAssignableLevelMVar mctx rhs) then
        pure false
      else if updateLhs && lhs.isMVar && !isReadOnlyLevelMVar mctx lhs.mvarId! && !lhs.occurs rhs then do
        assignLevel lhs.mvarId! rhs;
        pure true
      else if auxMVarSupport σ && updateLhs && lhs.isMVar && !isReadOnlyLevelMVar mctx lhs.mvarId! && !strictOccursMax lhs rhs then do
        solveSelfMax lhs.mvarId! rhs;
        pure true
      else if updateRhs && rhs.isMVar && !isReadOnlyLevelMVar mctx rhs.mvarId! && !rhs.occurs lhs then do
        assignLevel rhs.mvarId! lhs;
        pure true
      else if auxMVarSupport σ && updateRhs && rhs.isMVar && !isReadOnlyLevelMVar mctx rhs.mvarId! && !strictOccursMax rhs lhs then do
        solveSelfMax rhs.mvarId! lhs;
        pure true
      else if lhs.isMVar || rhs.isMVar then
        pure false
      else
        if lhs.isSucc || rhs.isSucc then
          match lhs.dec, rhs.dec with
          | some lhs', some rhs' => isLevelDefEqAux lhs' rhs'
          | _,         _         => do
            postponeIsLevelDefEq lhs updateLhs rhs updateRhs;
            pure true
        else do
          postponeIsLevelDefEq lhs updateLhs rhs updateRhs;
          pure true

private def getNumPostponed : TypeUtilM σ ϕ Nat :=
do s ← get;
   pure s.postponed.size

private def getResetPostponed : TypeUtilM σ ϕ (Array PostponedEntry) :=
do s ← get;
   let ps := s.postponed;
   modify $ fun s => { postponed := #[], .. s };
   pure ps

private def processPostponedStep [AbstractMetavarContext σ] : TypeUtilM σ ϕ Bool :=
traceCtx `type_context.level_is_def_eq.postponed_step $ do
  ps ← getResetPostponed;
  ps.foldlM
    (fun (r : Bool) (p : PostponedEntry) =>
      if r then
        isLevelDefEqAux p.updateLhs p.updateRhs p.lhs p.rhs
      else
        pure false)
    true

private partial def processPostponedAux [AbstractMetavarContext σ] : Bool → TypeUtilM σ ϕ Bool
| mayPostpone => do
  numPostponed ← getNumPostponed;
  if numPostponed == 0 then
    pure true
  else do
    trace! `type_context.level_is_def_eq ("processing #" ++ toString numPostponed ++ " postponed is-def-eq level constraints");
    r ← processPostponedStep;
    if !r then
      pure r
    else do
      numPostponed' ← getNumPostponed;
      if numPostponed' == 0 then
        pure true
      else if numPostponed' < numPostponed then
        processPostponedAux mayPostpone
      else do
        trace! `type_context.level_is_def_eq ("no progress solving pending is-def-eq level constraints");
        pure mayPostpone

private def processPostponed [AbstractMetavarContext σ] (mayPostpone : Bool) : TypeUtilM σ ϕ Bool :=
do numPostponed ← getNumPostponed;
   if numPostponed == 0 then pure true
   else traceCtx `type_context.level_is_def_eq.postponed $ processPostponedAux mayPostpone

@[inline] private def restoreIfFalse (x : TypeUtilM σ ϕ Bool) : TypeUtilM σ ϕ Bool :=
do s ← get;
   let mctx      := s.mctx;
   let postponed := s.postponed;
   catch
     (do b ← x;
       unless b $ modify $ fun s => { mctx := mctx, postponed := postponed, .. s };
       pure b)
     (fun e => do
       modify $ fun s => { mctx := mctx, postponed := postponed, .. s };
       throw e)

/- ===========================
   isDefEq for Expr
   =========================== -/
@[specialize] private def isDefEqAux
    [AbstractMetavarContext σ]
    [AbstractTypeUtilCache ϕ]
    (whnf : Expr → TypeUtilM σ ϕ Expr)
    (inferType : Expr → TypeUtilM σ ϕ Expr)
    (isDefEq : Expr → Expr → TypeUtilM σ ϕ Bool)
    : Expr → Expr → TypeUtilM σ ϕ Bool :=
fun _ _ => throw $ TypeUtilException.other "not implemented yet"

/- Public interface -/

def isLevelDefEq [AbstractMetavarContext σ] (u v : Level) (mayPostpone : Bool := false) : TypeUtilM σ ϕ Bool :=
restoreIfFalse $ do
  r ← isLevelDefEqAux true true u v;
  if !r then pure false
  else processPostponed mayPostpone

/- =========================================== -/
/- BIG HACK until we add `mutual` keyword back -/
/- =========================================== -/
inductive TypeUtilOp
| whnfOp | inferTypeOp | isDefEqOp
open TypeUtilOp
private def exprToBool : Expr → Bool
| Expr.sort Level.zero => false
| _                    => true
private def boolToExpr : Bool → Expr
| false => Expr.sort Level.zero
| true  => Expr.bvar 0

private partial def auxFixpoint [AbstractMetavarContext σ] [AbstractTypeUtilCache ϕ] : TypeUtilOp → Expr → Expr → TypeUtilM σ ϕ Expr
| op, e₁, e₂ =>
  let whnf      := fun e => auxFixpoint whnfOp e e;
  let inferType := fun e => auxFixpoint inferTypeOp e e;
  let isDefEq   := fun e₁ e₂ => exprToBool <$> auxFixpoint isDefEqOp e₁ e₂;
  match op with
  | whnfOp      => whnfAux whnf inferType isDefEq e₁
  | inferTypeOp => inferTypeAux whnf inferType isDefEq e₁
  | isDefEqOp   => boolToExpr <$> isDefEqAux whnf inferType isDefEq e₁ e₂

def whnf [AbstractMetavarContext σ] [AbstractTypeUtilCache ϕ] (e : Expr) : TypeUtilM σ ϕ Expr :=
auxFixpoint whnfOp e e

def inferType [AbstractMetavarContext σ] [AbstractTypeUtilCache ϕ] (e : Expr) : TypeUtilM σ ϕ Expr :=
auxFixpoint inferTypeOp e e

def isDefEq [AbstractMetavarContext σ] [AbstractTypeUtilCache ϕ] (e₁ e₂ : Expr) : TypeUtilM σ ϕ Bool :=
exprToBool <$> auxFixpoint isDefEqOp e₁ e₂
/- =========================================== -/
/-          END OF BIG HACK                    -/
/- =========================================== -/

end TypeUtil

inductive TypeUtilNoCache
| mk

instance typeContextNoCacheIsAbstractTCCache : AbstractTypeUtilCache TypeUtilNoCache :=
{ getWHNF := fun _ _ _ => none,
  setWHNF := fun s _ _ _ => s }

end Lean
