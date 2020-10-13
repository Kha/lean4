// Lean compiler output
// Module: Lean.Meta.Tactic.Induction
// Imports: Init Lean.Meta.RecursorInfo Lean.Meta.SynthInstance Lean.Meta.Tactic.Util Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Clear Lean.Meta.Tactic.FVarSubst
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at_Lean_Meta_induction___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize___main(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity(lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8;
lean_object* l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__2;
lean_object* l_Lean_Meta_induction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3;
lean_object* l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at_Lean_Meta_induction___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___boxed(lean_object**);
lean_object* l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2;
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_Lean_Level_Inhabited;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Lean_Meta_InferType_4__getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___boxed(lean_object**);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2;
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__2;
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_elem___main___at_Lean_Meta_induction___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__4;
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2;
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7;
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*);
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1;
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__9;
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3;
lean_object* l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__5;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
lean_object* l_Lean_MetavarContext_localDeclDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InductionSubgoal_inhabited___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7;
lean_object* l___private_Lean_Meta_SynthInstance_10__synthInstanceImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
uint8_t l_List_elem___main___at_Lean_Meta_induction___spec__5(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6;
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3;
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___boxed(lean_object**);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_introNCore___spec__4(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5;
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1;
extern lean_object* l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__3;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6;
uint8_t l_Lean_Level_isZero(lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed(lean_object**);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3;
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3;
lean_object* l_Lean_Meta_InductionSubgoal_inhabited;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__3;
lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
return x_11;
}
case 10:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_1 = x_12;
goto _start;
}
default: 
{
lean_object* x_14; 
x_14 = lean_box(0);
x_2 = x_14;
goto block_7;
}
}
block_7:
{
uint8_t x_3; 
lean_dec(x_2);
x_3 = l_Lean_Expr_isHeadBetaTarget(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Expr_headBeta(x_1);
x_1 = x_5;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Expr_isForall(x_9);
if (x_10 == 0)
{
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
else
{
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = l_Lean_Expr_isForall(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("induction");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed recursor");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to generate type class instance parameter");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Meta_whnfForall___at___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___spec__1(x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 7)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l___private_Lean_Meta_SynthInstance_10__synthInstanceImp(x_19, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_mkApp(x_4, x_21);
x_3 = x_12;
x_4 = x_23;
x_9 = x_22;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_4);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_27 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8;
x_28 = lean_box(0);
x_29 = l_Lean_Meta_throwTacticEx___rarg(x_26, x_1, x_27, x_28, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_17);
lean_dec(x_4);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_dec(x_16);
x_35 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_36 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_37 = lean_box(0);
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_35, x_1, x_36, x_37, x_5, x_6, x_7, x_8, x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
return x_16;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_16);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_13);
if (x_43 == 0)
{
return x_13;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_3, 1);
x_48 = lean_ctor_get(x_11, 0);
x_49 = lean_array_get_size(x_2);
x_50 = lean_nat_dec_lt(x_48, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_4);
x_51 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_52 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_53 = lean_box(0);
x_54 = l_Lean_Meta_throwTacticEx___rarg(x_51, x_1, x_52, x_53, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_array_fget(x_2, x_48);
x_56 = l_Lean_mkApp(x_4, x_55);
x_3 = x_47;
x_4 = x_56;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_InductionSubgoal_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_InductionSubgoal_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_InductionSubgoal_inhabited___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_whnfForall___at___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 7)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_expr_instantiate1(x_13, x_3);
lean_dec(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_ctor_get(x_10, 2);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_expr_instantiate1(x_16, x_3);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_21 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_22 = lean_box(0);
x_23 = l_Lean_Meta_throwTacticEx___rarg(x_20, x_1, x_21, x_22, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
return x_9;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
x_12 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
x_13 = lean_nat_add(x_3, x_10);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = l_Lean_Name_inhabited;
x_16 = lean_array_get(x_15, x_1, x_12);
x_17 = lean_nat_sub(x_12, x_3);
lean_dec(x_12);
x_18 = lean_nat_sub(x_17, x_10);
lean_dec(x_17);
x_19 = lean_array_get(x_15, x_4, x_18);
lean_dec(x_18);
x_20 = l_Lean_mkFVar(x_19);
x_21 = l_Lean_Meta_FVarSubst_insert(x_7, x_16, x_20);
x_6 = x_11;
x_7 = x_21;
goto _start;
}
else
{
lean_dec(x_12);
x_6 = x_11;
goto _start;
}
}
else
{
lean_dec(x_6);
return x_7;
}
}
}
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
x_12 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
x_13 = lean_nat_add(x_3, x_10);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = l_Lean_Name_inhabited;
x_16 = lean_array_get(x_15, x_1, x_12);
x_17 = lean_nat_sub(x_12, x_3);
lean_dec(x_12);
x_18 = lean_nat_sub(x_17, x_10);
lean_dec(x_17);
x_19 = lean_array_get(x_15, x_4, x_18);
lean_dec(x_18);
x_20 = l_Lean_mkFVar(x_19);
x_21 = l_Lean_Meta_FVarSubst_insert(x_7, x_16, x_20);
x_6 = x_11;
x_7 = x_21;
goto _start;
}
else
{
lean_dec(x_12);
x_6 = x_11;
goto _start;
}
}
else
{
lean_dec(x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_synthInstance_x3f___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_array_fget(x_3, x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
x_20 = l_Lean_mkApp(x_18, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_21 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_19, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_5, 1, x_22);
lean_ctor_set(x_5, 0, x_20);
x_4 = x_16;
x_10 = x_23;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_20);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
lean_inc(x_14);
x_31 = l_Lean_mkApp(x_29, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_32 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_30, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_33);
x_4 = x_16;
x_5 = x_35;
x_10 = x_34;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_39 = x_32;
} else {
 lean_dec_ref(x_32);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_21 = l_Lean_Meta_whnfForall___at___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___spec__1(x_13, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Expr_isForall(x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
if (x_14 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_12);
x_25 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_26 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_27 = lean_box(0);
x_28 = l_Lean_Meta_throwTacticEx___rarg(x_25, x_1, x_26, x_27, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(x_1, x_12, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_15);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_15);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_3, 3);
x_39 = lean_nat_dec_lt(x_10, x_38);
if (x_39 == 0)
{
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
if (x_14 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_15);
lean_dec(x_12);
x_40 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_41 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_42 = lean_box(0);
x_43 = l_Lean_Meta_throwTacticEx___rarg(x_40, x_1, x_41, x_42, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(x_1, x_12, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_15);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_15);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = l_Lean_Meta_RecursorInfo_firstIndexPos(x_3);
x_54 = lean_nat_dec_eq(x_10, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_inc(x_1);
x_55 = l_Lean_Meta_getMVarTag(x_1, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_194; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_194 = lean_nat_dec_le(x_8, x_11);
if (x_194 == 0)
{
x_58 = x_57;
goto block_193;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_dec(x_56);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_195 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_196 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_197 = lean_box(0);
x_198 = l_Lean_Meta_throwTacticEx___rarg(x_195, x_1, x_196, x_197, x_16, x_17, x_18, x_19, x_57);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_199 = !lean_is_exclusive(x_198);
if (x_199 == 0)
{
return x_198;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_198, 0);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_198);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
block_193:
{
if (lean_obj_tag(x_22) == 7)
{
lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; uint8_t x_143; uint8_t x_144; 
x_59 = lean_ctor_get(x_22, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_22, 1);
lean_inc(x_60);
x_61 = lean_ctor_get_uint64(x_22, sizeof(void*)*3);
x_62 = l_Lean_Expr_headBeta(x_60);
x_143 = (uint8_t)((x_61 << 24) >> 61);
x_144 = l_Lean_BinderInfo_isInstImplicit(x_143);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_box(0);
x_63 = x_145;
goto block_142;
}
else
{
uint8_t x_146; 
x_146 = l_Array_isEmpty___rarg(x_2);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_box(0);
x_63 = x_147;
goto block_142;
}
else
{
lean_object* x_148; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_62);
x_148 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(x_62, x_16, x_17, x_18, x_19, x_58);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l_Lean_Name_append___main(x_56, x_59);
lean_dec(x_56);
lean_inc(x_16);
x_152 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_62, x_151, x_16, x_17, x_18, x_19, x_150);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
lean_inc(x_153);
x_155 = l_Lean_mkApp(x_12, x_153);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_156 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_22, x_153, x_16, x_17, x_18, x_19, x_154);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_unsigned_to_nat(1u);
x_160 = lean_nat_add(x_10, x_159);
lean_dec(x_10);
x_161 = lean_nat_add(x_11, x_159);
lean_dec(x_11);
x_162 = l_Lean_Expr_mvarId_x21(x_153);
lean_dec(x_153);
x_163 = lean_box(0);
x_164 = l_Array_empty___closed__1;
x_165 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_165, 2, x_163);
x_166 = lean_array_push(x_15, x_165);
x_10 = x_160;
x_11 = x_161;
x_12 = x_155;
x_13 = x_157;
x_15 = x_166;
x_20 = x_158;
goto _start;
}
else
{
uint8_t x_168; 
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_168 = !lean_is_exclusive(x_156);
if (x_168 == 0)
{
return x_156;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_156, 0);
x_170 = lean_ctor_get(x_156, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_156);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_56);
x_172 = lean_ctor_get(x_148, 1);
lean_inc(x_172);
lean_dec(x_148);
x_173 = lean_ctor_get(x_149, 0);
lean_inc(x_173);
lean_dec(x_149);
lean_inc(x_173);
x_174 = l_Lean_mkApp(x_12, x_173);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_175 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_22, x_173, x_16, x_17, x_18, x_19, x_172);
lean_dec(x_173);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_unsigned_to_nat(1u);
x_179 = lean_nat_add(x_10, x_178);
lean_dec(x_10);
x_180 = lean_nat_add(x_11, x_178);
lean_dec(x_11);
x_10 = x_179;
x_11 = x_180;
x_12 = x_174;
x_13 = x_176;
x_20 = x_177;
goto _start;
}
else
{
uint8_t x_182; 
lean_dec(x_174);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_175);
if (x_182 == 0)
{
return x_175;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_175, 0);
x_184 = lean_ctor_get(x_175, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_175);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_148);
if (x_186 == 0)
{
return x_148;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_148, 0);
x_188 = lean_ctor_get(x_148, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_148);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
}
block_142:
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_63);
lean_inc(x_62);
x_64 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_62);
x_65 = lean_nat_dec_lt(x_64, x_6);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_66 = lean_nat_sub(x_64, x_6);
lean_dec(x_64);
x_67 = lean_array_get_size(x_4);
x_68 = lean_array_get_size(x_7);
x_69 = lean_nat_sub(x_67, x_68);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_69, x_70);
lean_dec(x_69);
x_124 = lean_array_get_size(x_2);
x_125 = lean_nat_dec_lt(x_11, x_124);
lean_dec(x_124);
x_126 = l_Lean_Name_append___main(x_56, x_59);
lean_dec(x_56);
lean_inc(x_16);
x_127 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_62, x_126, x_16, x_17, x_18, x_19, x_58);
if (x_125 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_box(0);
x_72 = x_130;
x_73 = x_128;
x_74 = x_129;
goto block_123;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_127, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_dec(x_127);
x_133 = lean_array_fget(x_2, x_11);
x_72 = x_133;
x_73 = x_131;
x_74 = x_132;
goto block_123;
}
block_123:
{
lean_object* x_75; lean_object* x_76; 
lean_inc(x_73);
x_75 = l_Lean_mkApp(x_12, x_73);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_76 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_22, x_73, x_16, x_17, x_18, x_19, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Expr_mvarId_x21(x_73);
lean_dec(x_73);
x_80 = l_Lean_Expr_fvarId_x21(x_5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_81 = l_Lean_Meta_tryClear(x_79, x_80, x_16, x_17, x_18, x_19, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = 0;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_85 = l_Lean_Meta_introNCore(x_82, x_66, x_72, x_84, x_16, x_17, x_18, x_19, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_box(0);
x_91 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_92 = l_Lean_Meta_introNCore(x_89, x_71, x_90, x_91, x_16, x_17, x_18, x_19, x_87);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
lean_inc(x_9);
lean_inc(x_67);
x_97 = l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(x_4, x_7, x_68, x_95, x_67, x_67, x_9);
lean_dec(x_67);
lean_dec(x_95);
lean_dec(x_68);
x_98 = x_88;
x_99 = lean_unsigned_to_nat(0u);
x_100 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_99, x_98);
x_101 = x_100;
x_102 = lean_nat_add(x_10, x_70);
lean_dec(x_10);
x_103 = lean_nat_add(x_11, x_70);
lean_dec(x_11);
x_104 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_104, 0, x_96);
lean_ctor_set(x_104, 1, x_101);
lean_ctor_set(x_104, 2, x_97);
x_105 = lean_array_push(x_15, x_104);
x_10 = x_102;
x_11 = x_103;
x_12 = x_75;
x_13 = x_77;
x_15 = x_105;
x_20 = x_94;
goto _start;
}
else
{
uint8_t x_107; 
lean_dec(x_88);
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_92);
if (x_107 == 0)
{
return x_92;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_92, 0);
x_109 = lean_ctor_get(x_92, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_92);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_85);
if (x_111 == 0)
{
return x_85;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_85, 0);
x_113 = lean_ctor_get(x_85, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_85);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_81);
if (x_115 == 0)
{
return x_81;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_81, 0);
x_117 = lean_ctor_get(x_81, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_81);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_76);
if (x_119 == 0)
{
return x_76;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_76, 0);
x_121 = lean_ctor_get(x_76, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_76);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_134 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_135 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_136 = lean_box(0);
x_137 = l_Lean_Meta_throwTacticEx___rarg(x_134, x_1, x_135, x_136, x_16, x_17, x_18, x_19, x_58);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
return x_137;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_137);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_56);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_190 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
x_191 = l_unreachable_x21___rarg(x_190);
x_192 = lean_apply_5(x_191, x_16, x_17, x_18, x_19, x_58);
return x_192;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_203 = !lean_is_exclusive(x_55);
if (x_203 == 0)
{
return x_55;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_55, 0);
x_205 = lean_ctor_get(x_55, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_55);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_12);
lean_ctor_set(x_207, 1, x_22);
x_208 = lean_unsigned_to_nat(0u);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_209 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4(x_1, x_7, x_7, x_208, x_207, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
lean_dec(x_210);
lean_inc(x_5);
x_214 = l_Lean_mkApp(x_212, x_5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_215 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_213, x_5, x_16, x_17, x_18, x_19, x_211);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_unsigned_to_nat(1u);
x_219 = lean_nat_add(x_10, x_218);
lean_dec(x_10);
x_220 = lean_array_get_size(x_7);
x_221 = lean_nat_add(x_219, x_220);
lean_dec(x_220);
lean_dec(x_219);
x_222 = 1;
x_10 = x_221;
x_12 = x_214;
x_13 = x_216;
x_14 = x_222;
x_20 = x_217;
goto _start;
}
else
{
uint8_t x_224; 
lean_dec(x_214);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_224 = !lean_is_exclusive(x_215);
if (x_224 == 0)
{
return x_215;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_215, 0);
x_226 = lean_ctor_get(x_215, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_215);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_228 = !lean_is_exclusive(x_209);
if (x_228 == 0)
{
return x_209;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_209, 0);
x_230 = lean_ctor_get(x_209, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_209);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
}
}
}
else
{
uint8_t x_232; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_232 = !lean_is_exclusive(x_21);
if (x_232 == 0)
{
return x_21;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_21, 0);
x_234 = lean_ctor_get(x_21, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_21);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
}
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_14);
lean_dec(x_14);
x_22 = l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
x_21 = l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_21;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_14);
lean_dec(x_14);
x_22 = l___private_Lean_Meta_Tactic_Induction_4__finalizeAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_1);
x_14 = l_Lean_Meta_getMVarType(x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_3, 7);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_List_lengthAux___main___rarg(x_21, x_22);
x_24 = lean_ctor_get(x_3, 5);
x_25 = l_List_lengthAux___main___rarg(x_24, x_22);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_25, x_26);
lean_dec(x_25);
x_28 = 0;
x_29 = l_Array_empty___closed__1;
x_30 = l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(x_1, x_2, x_3, x_4, x_5, x_17, x_6, x_23, x_7, x_27, x_22, x_8, x_19, x_28, x_29, x_9, x_10, x_11, x_12, x_20);
lean_dec(x_23);
lean_dec(x_17);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected major premise type ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_indentExpr(x_2);
x_9 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_12 = lean_box(0);
x_13 = l_Lean_Meta_throwTacticEx___rarg(x_11, x_1, x_10, x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at_Lean_Meta_induction___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
x_9 = l_unreachable_x21___rarg(x_8);
x_10 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_inc(x_3);
lean_inc(x_11);
x_12 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 4);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_13, sizeof(void*)*5);
lean_dec(x_13);
x_21 = l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__3(x_3, x_4, x_5, x_6, x_18);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
if (x_20 == 0)
{
lean_object* x_48; 
lean_free_object(x_21);
lean_dec(x_2);
x_48 = lean_box(0);
x_25 = x_48;
goto block_47;
}
else
{
uint8_t x_49; 
x_49 = lean_ctor_get_uint8(x_23, 6);
if (x_49 == 0)
{
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_21, 0, x_2);
return x_21;
}
else
{
lean_object* x_50; 
lean_free_object(x_21);
lean_dec(x_2);
x_50 = lean_box(0);
x_25 = x_50;
goto block_47;
}
}
block_47:
{
uint8_t x_26; 
lean_dec(x_25);
x_26 = lean_ctor_get_uint8(x_23, 7);
lean_dec(x_23);
if (x_26 == 0)
{
lean_dec(x_11);
x_2 = x_19;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_st_ref_take(x_4, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_29, 2);
x_33 = lean_box(0);
x_34 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_32, x_11, x_33);
lean_ctor_set(x_29, 2, x_34);
x_35 = lean_st_ref_set(x_4, x_29, x_30);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_2 = x_19;
x_7 = x_36;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
x_40 = lean_ctor_get(x_29, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_41 = lean_box(0);
x_42 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_40, x_11, x_41);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_st_ref_set(x_4, x_43, x_30);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_2 = x_19;
x_7 = x_45;
goto _start;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_21, 0);
x_52 = lean_ctor_get(x_21, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_21);
if (x_20 == 0)
{
lean_object* x_70; 
lean_dec(x_2);
x_70 = lean_box(0);
x_53 = x_70;
goto block_69;
}
else
{
uint8_t x_71; 
x_71 = lean_ctor_get_uint8(x_51, 6);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_51);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_2);
lean_ctor_set(x_72, 1, x_52);
return x_72;
}
else
{
lean_object* x_73; 
lean_dec(x_2);
x_73 = lean_box(0);
x_53 = x_73;
goto block_69;
}
}
block_69:
{
uint8_t x_54; 
lean_dec(x_53);
x_54 = lean_ctor_get_uint8(x_51, 7);
lean_dec(x_51);
if (x_54 == 0)
{
lean_dec(x_11);
x_2 = x_19;
x_7 = x_52;
goto _start;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = lean_st_ref_take(x_4, x_52);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 2);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
x_64 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_61, x_11, x_63);
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(0, 3, 0);
} else {
 x_65 = x_62;
}
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_65, 2, x_64);
x_66 = lean_st_ref_set(x_4, x_65, x_58);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_2 = x_19;
x_7 = x_67;
goto _start;
}
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_12);
if (x_74 == 0)
{
return x_12;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_12, 0);
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_12);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
case 2:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_2, 0);
lean_inc(x_78);
x_79 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1(x_78, x_3, x_4, x_5, x_6, x_7);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_79, 0);
lean_dec(x_82);
lean_ctor_set(x_79, 0, x_2);
return x_79;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_2);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_2);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_dec(x_79);
x_86 = lean_ctor_get(x_80, 0);
lean_inc(x_86);
lean_dec(x_80);
x_2 = x_86;
x_7 = x_85;
goto _start;
}
}
case 4:
{
lean_object* x_88; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_88 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_88, 1);
x_92 = l_Lean_Expr_isAppOf(x_90, x_1);
if (x_92 == 0)
{
lean_object* x_93; 
lean_free_object(x_88);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_90);
x_93 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_90, x_3, x_4, x_5, x_6, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = !lean_is_exclusive(x_93);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_93, 0);
lean_dec(x_96);
lean_ctor_set(x_93, 0, x_90);
return x_93;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_90);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_90);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
lean_dec(x_93);
x_100 = lean_ctor_get(x_94, 0);
lean_inc(x_100);
lean_dec(x_94);
x_2 = x_100;
x_7 = x_99;
goto _start;
}
}
else
{
uint8_t x_102; 
lean_dec(x_90);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_102 = !lean_is_exclusive(x_93);
if (x_102 == 0)
{
return x_93;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_93, 0);
x_104 = lean_ctor_get(x_93, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_93);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_88;
}
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_88, 0);
x_107 = lean_ctor_get(x_88, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_88);
x_108 = l_Lean_Expr_isAppOf(x_106, x_1);
if (x_108 == 0)
{
lean_object* x_109; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_106);
x_109 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_106, x_3, x_4, x_5, x_6, x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_106);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_106);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_dec(x_109);
x_115 = lean_ctor_get(x_110, 0);
lean_inc(x_115);
lean_dec(x_110);
x_2 = x_115;
x_7 = x_114;
goto _start;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_106);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_117 = lean_ctor_get(x_109, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_109, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_119 = x_109;
} else {
 lean_dec_ref(x_109);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_106);
lean_ctor_set(x_121, 1, x_107);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_122 = !lean_is_exclusive(x_88);
if (x_122 == 0)
{
return x_88;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_88, 0);
x_124 = lean_ctor_get(x_88, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_88);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
case 5:
{
lean_object* x_126; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_126 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_128 = lean_ctor_get(x_126, 0);
x_129 = lean_ctor_get(x_126, 1);
x_130 = l_Lean_Expr_isAppOf(x_128, x_1);
if (x_130 == 0)
{
lean_object* x_131; 
lean_free_object(x_126);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_128);
x_131 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_128, x_3, x_4, x_5, x_6, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
uint8_t x_133; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_133 = !lean_is_exclusive(x_131);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_131, 0);
lean_dec(x_134);
lean_ctor_set(x_131, 0, x_128);
return x_131;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
lean_dec(x_131);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_128);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_128);
x_137 = lean_ctor_get(x_131, 1);
lean_inc(x_137);
lean_dec(x_131);
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
lean_dec(x_132);
x_2 = x_138;
x_7 = x_137;
goto _start;
}
}
else
{
uint8_t x_140; 
lean_dec(x_128);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_140 = !lean_is_exclusive(x_131);
if (x_140 == 0)
{
return x_131;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_131, 0);
x_142 = lean_ctor_get(x_131, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_131);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_126;
}
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_144 = lean_ctor_get(x_126, 0);
x_145 = lean_ctor_get(x_126, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_126);
x_146 = l_Lean_Expr_isAppOf(x_144, x_1);
if (x_146 == 0)
{
lean_object* x_147; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_144);
x_147 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_144, x_3, x_4, x_5, x_6, x_145);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_144);
x_152 = lean_ctor_get(x_147, 1);
lean_inc(x_152);
lean_dec(x_147);
x_153 = lean_ctor_get(x_148, 0);
lean_inc(x_153);
lean_dec(x_148);
x_2 = x_153;
x_7 = x_152;
goto _start;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_144);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_155 = lean_ctor_get(x_147, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_147, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_157 = x_147;
} else {
 lean_dec_ref(x_147);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
else
{
lean_object* x_159; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_144);
lean_ctor_set(x_159, 1, x_145);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_160 = !lean_is_exclusive(x_126);
if (x_160 == 0)
{
return x_126;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_126, 0);
x_162 = lean_ctor_get(x_126, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_126);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
case 8:
{
lean_object* x_164; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_164 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_164) == 0)
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = lean_ctor_get(x_164, 0);
x_167 = lean_ctor_get(x_164, 1);
x_168 = l_Lean_Expr_isAppOf(x_166, x_1);
if (x_168 == 0)
{
lean_object* x_169; 
lean_free_object(x_164);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_166);
x_169 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_166, x_3, x_4, x_5, x_6, x_167);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_obj_tag(x_170) == 0)
{
uint8_t x_171; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_171 = !lean_is_exclusive(x_169);
if (x_171 == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_169, 0);
lean_dec(x_172);
lean_ctor_set(x_169, 0, x_166);
return x_169;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
lean_dec(x_169);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_166);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_166);
x_175 = lean_ctor_get(x_169, 1);
lean_inc(x_175);
lean_dec(x_169);
x_176 = lean_ctor_get(x_170, 0);
lean_inc(x_176);
lean_dec(x_170);
x_2 = x_176;
x_7 = x_175;
goto _start;
}
}
else
{
uint8_t x_178; 
lean_dec(x_166);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_178 = !lean_is_exclusive(x_169);
if (x_178 == 0)
{
return x_169;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_169, 0);
x_180 = lean_ctor_get(x_169, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_169);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_164;
}
}
else
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_182 = lean_ctor_get(x_164, 0);
x_183 = lean_ctor_get(x_164, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_164);
x_184 = l_Lean_Expr_isAppOf(x_182, x_1);
if (x_184 == 0)
{
lean_object* x_185; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_182);
x_185 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_182, x_3, x_4, x_5, x_6, x_183);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_182);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_182);
x_190 = lean_ctor_get(x_185, 1);
lean_inc(x_190);
lean_dec(x_185);
x_191 = lean_ctor_get(x_186, 0);
lean_inc(x_191);
lean_dec(x_186);
x_2 = x_191;
x_7 = x_190;
goto _start;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_182);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_193 = lean_ctor_get(x_185, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_185, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_195 = x_185;
} else {
 lean_dec_ref(x_185);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
else
{
lean_object* x_197; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_182);
lean_ctor_set(x_197, 1, x_183);
return x_197;
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_198 = !lean_is_exclusive(x_164);
if (x_198 == 0)
{
return x_164;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_164, 0);
x_200 = lean_ctor_get(x_164, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_164);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
case 10:
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_2, 1);
lean_inc(x_202);
lean_dec(x_2);
x_2 = x_202;
goto _start;
}
case 11:
{
lean_object* x_204; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_204 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_204) == 0)
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_206 = lean_ctor_get(x_204, 0);
x_207 = lean_ctor_get(x_204, 1);
x_208 = l_Lean_Expr_isAppOf(x_206, x_1);
if (x_208 == 0)
{
lean_object* x_209; 
lean_free_object(x_204);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_206);
x_209 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_206, x_3, x_4, x_5, x_6, x_207);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_obj_tag(x_210) == 0)
{
uint8_t x_211; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_211 = !lean_is_exclusive(x_209);
if (x_211 == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_209, 0);
lean_dec(x_212);
lean_ctor_set(x_209, 0, x_206);
return x_209;
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_209, 1);
lean_inc(x_213);
lean_dec(x_209);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_206);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_206);
x_215 = lean_ctor_get(x_209, 1);
lean_inc(x_215);
lean_dec(x_209);
x_216 = lean_ctor_get(x_210, 0);
lean_inc(x_216);
lean_dec(x_210);
x_2 = x_216;
x_7 = x_215;
goto _start;
}
}
else
{
uint8_t x_218; 
lean_dec(x_206);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_218 = !lean_is_exclusive(x_209);
if (x_218 == 0)
{
return x_209;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_209, 0);
x_220 = lean_ctor_get(x_209, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_209);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_204;
}
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_222 = lean_ctor_get(x_204, 0);
x_223 = lean_ctor_get(x_204, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_204);
x_224 = l_Lean_Expr_isAppOf(x_222, x_1);
if (x_224 == 0)
{
lean_object* x_225; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_222);
x_225 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_222, x_3, x_4, x_5, x_6, x_223);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_228 = x_225;
} else {
 lean_dec_ref(x_225);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_222);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_222);
x_230 = lean_ctor_get(x_225, 1);
lean_inc(x_230);
lean_dec(x_225);
x_231 = lean_ctor_get(x_226, 0);
lean_inc(x_231);
lean_dec(x_226);
x_2 = x_231;
x_7 = x_230;
goto _start;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_222);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_233 = lean_ctor_get(x_225, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_225, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_235 = x_225;
} else {
 lean_dec_ref(x_225);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
}
else
{
lean_object* x_237; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_222);
lean_ctor_set(x_237, 1, x_223);
return x_237;
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_238 = !lean_is_exclusive(x_204);
if (x_238 == 0)
{
return x_204;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_204, 0);
x_240 = lean_ctor_get(x_204, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_204);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
case 12:
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_2);
x_242 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
x_243 = l_unreachable_x21___rarg(x_242);
x_244 = lean_apply_5(x_243, x_3, x_4, x_5, x_6, x_7);
return x_244;
}
default: 
{
lean_object* x_245; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_2);
lean_ctor_set(x_245, 1, x_7);
return x_245;
}
}
}
}
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at_Lean_Meta_induction___spec__3(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Expr_isAppOf(x_10, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = lean_box(0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = l_Lean_Expr_isAppOf(x_14, x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise type is ill-formed");
return x_1;
}
}
static lean_object* _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_5, 1);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_array_get_size(x_4);
x_19 = lean_nat_dec_le(x_18, x_17);
lean_dec(x_18);
if (x_19 == 0)
{
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = l_Lean_indentExpr(x_3);
x_22 = l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_box(0);
x_25 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_23, x_24, x_6, x_7, x_8, x_9, x_10);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
uint8_t l_List_elem___main___at_Lean_Meta_induction___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_nat_dec_eq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
static lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is an index in major premise, but it depends on index occurring at position #");
return x_1;
}
}
static lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is an index in major premise, but it occurs in previous arguments");
return x_1;
}
}
static lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is an index in major premise, but it occurs more than once");
return x_1;
}
}
static lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_10, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_60; uint8_t x_79; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_10, x_18);
lean_dec(x_10);
x_20 = lean_nat_sub(x_9, x_19);
x_21 = lean_nat_sub(x_20, x_18);
lean_dec(x_20);
x_22 = l_Lean_Expr_Inhabited;
x_23 = lean_array_get(x_22, x_4, x_21);
x_79 = lean_nat_dec_eq(x_21, x_7);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = lean_expr_eqv(x_23, x_8);
if (x_80 == 0)
{
x_60 = x_15;
goto block_78;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_8);
x_82 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_83 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9;
x_85 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_indentExpr(x_3);
x_87 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_box(0);
x_89 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_87, x_88, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_11);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_89);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
x_60 = x_15;
goto block_78;
}
block_59:
{
uint8_t x_25; 
x_25 = lean_nat_dec_lt(x_7, x_21);
if (x_25 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
x_10 = x_19;
x_15 = x_24;
goto _start;
}
else
{
uint8_t x_27; 
x_27 = l_List_elem___main___at_Lean_Meta_induction___spec__5(x_21, x_6);
if (x_27 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
x_10 = x_19;
x_15 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
x_29 = l_Lean_Expr_isFVar(x_23);
if (x_29 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
x_10 = x_19;
x_15 = x_24;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Expr_fvarId_x21(x_8);
lean_inc(x_11);
x_32 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_31, x_11, x_12, x_13, x_14, x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Expr_fvarId_x21(x_23);
lean_dec(x_23);
lean_inc(x_5);
x_36 = l_Lean_MetavarContext_localDeclDependsOn(x_5, x_33, x_35);
lean_dec(x_35);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_dec(x_21);
x_10 = x_19;
x_15 = x_34;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_3);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_8);
x_40 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_nat_add(x_21, x_18);
lean_dec(x_21);
x_45 = l_Nat_repr(x_44);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_box(0);
x_50 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_48, x_49, x_11, x_12, x_13, x_14, x_34);
lean_dec(x_11);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_32);
if (x_55 == 0)
{
return x_32;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_32, 0);
x_57 = lean_ctor_get(x_32, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_32);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
}
block_78:
{
uint8_t x_61; 
x_61 = lean_nat_dec_lt(x_21, x_7);
if (x_61 == 0)
{
x_24 = x_60;
goto block_59;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = l_Lean_Expr_fvarId_x21(x_8);
lean_inc(x_23);
lean_inc(x_5);
x_63 = l_Lean_MetavarContext_exprDependsOn(x_5, x_23, x_62);
lean_dec(x_62);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
x_24 = x_60;
goto block_59;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_8);
x_66 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_indentExpr(x_3);
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_box(0);
x_73 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_71, x_72, x_11, x_12, x_13, x_14, x_60);
lean_dec(x_11);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
return x_73;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_73);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_15);
return x_95;
}
}
}
static lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise type index ");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" is not variable ");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_8);
x_15 = lean_nat_dec_lt(x_7, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = x_8;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_54; 
x_18 = lean_array_fget(x_8, x_7);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_fset(x_8, x_7, x_19);
x_21 = x_18;
x_22 = lean_array_get_size(x_4);
x_54 = lean_nat_dec_le(x_22, x_21);
if (x_54 == 0)
{
x_23 = x_13;
goto block_53;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
x_55 = l_Lean_indentExpr(x_3);
x_56 = l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_box(0);
x_59 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_57, x_58, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
block_53:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_39; 
x_24 = l_Lean_Expr_Inhabited;
x_25 = lean_array_get(x_24, x_4, x_21);
x_39 = l_Lean_Expr_isFVar(x_25);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_25);
x_41 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_indentExpr(x_3);
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_box(0);
x_48 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_46, x_47, x_9, x_10, x_11, x_12, x_23);
lean_dec(x_9);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
x_26 = x_23;
goto block_38;
}
block_38:
{
lean_object* x_27; 
lean_inc(x_9);
lean_inc(x_22);
lean_inc(x_25);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_21, x_25, x_22, x_22, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_7, x_29);
x_31 = x_25;
x_32 = lean_array_fset(x_20, x_7, x_31);
lean_dec(x_7);
x_7 = x_30;
x_8 = x_32;
x_13 = x_28;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = l_Lean_Name_inhabited;
x_11 = lean_array_get(x_10, x_2, x_4);
x_12 = l_Lean_mkFVar(x_11);
x_13 = l_Lean_Meta_FVarSubst_insert(x_5, x_9, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_4 = x_15;
x_5 = x_13;
goto _start;
}
}
}
lean_object* l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Level_normalize___main(x_9);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = l_Lean_Level_normalize___main(x_11);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_dec(x_17);
lean_inc(x_3);
x_18 = lean_array_push(x_16, x_3);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_5, 1, x_20);
lean_ctor_set(x_5, 0, x_18);
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec(x_5);
lean_inc(x_3);
x_24 = lean_array_push(x_23, x_3);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_5 = x_27;
x_6 = x_22;
goto _start;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_6, 1);
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_array_get_size(x_4);
x_35 = lean_nat_dec_le(x_34, x_33);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Lean_Level_Inhabited;
x_37 = lean_array_get(x_36, x_4, x_33);
x_38 = lean_array_push(x_31, x_37);
lean_ctor_set(x_5, 0, x_38);
x_6 = x_30;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_free_object(x_5);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_3);
x_40 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_41 = lean_box(0);
x_42 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_40, x_41, x_7, x_8, x_9, x_10, x_11);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_6, 1);
x_48 = lean_ctor_get(x_5, 0);
x_49 = lean_ctor_get(x_5, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_5);
x_50 = lean_ctor_get(x_13, 0);
x_51 = lean_array_get_size(x_4);
x_52 = lean_nat_dec_le(x_51, x_50);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = l_Lean_Level_Inhabited;
x_54 = lean_array_get(x_53, x_4, x_50);
x_55 = lean_array_push(x_48, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_49);
x_5 = x_56;
x_6 = x_47;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_3);
x_58 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_59 = lean_box(0);
x_60 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_58, x_59, x_7, x_8, x_9, x_10, x_11);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise is not of the form (C ...)");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("recursor '");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' can only eliminate into Prop");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
switch (lean_obj_tag(x_14)) {
case 4:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_List_redLength___main___rarg(x_22);
x_24 = lean_mk_empty_array_with_capacity(x_23);
lean_dec(x_23);
x_25 = l_List_toArrayAux___main___rarg(x_22, x_24);
x_26 = lean_ctor_get(x_4, 2);
x_27 = l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_inc(x_13);
lean_inc(x_8);
lean_inc(x_3);
x_28 = l_List_foldlM___main___at_Lean_Meta_induction___spec__10(x_3, x_8, x_13, x_25, x_27, x_26, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = l_Lean_Level_isZero(x_13);
lean_dec(x_13);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_33);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_35 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_35, 0, x_1);
x_36 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__9;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_box(0);
x_41 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_39, x_40, x_17, x_18, x_19, x_20, x_32);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_3);
x_46 = l_Array_toList___rarg(x_33);
lean_dec(x_33);
x_47 = l_Lean_mkConst(x_1, x_46);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_8);
x_48 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_8, x_15, x_5, x_47, x_17, x_18, x_19, x_20, x_32);
lean_dec(x_15);
if (lean_obj_tag(x_48) == 0)
{
if (x_6 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_17);
lean_inc(x_10);
x_51 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_10, x_12, x_17, x_18, x_19, x_20, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_mkApp(x_49, x_52);
x_55 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_54, x_17, x_18, x_19, x_20, x_53);
lean_dec(x_10);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_49);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_56 = !lean_is_exclusive(x_51);
if (x_56 == 0)
{
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_51, 0);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_51);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_48, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_dec(x_48);
x_62 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_11);
x_63 = lean_array_push(x_62, x_11);
lean_inc(x_17);
x_64 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_63, x_12, x_17, x_18, x_19, x_20, x_61);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_17);
lean_inc(x_10);
x_67 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_10, x_65, x_17, x_18, x_19, x_20, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_mkApp(x_60, x_68);
x_71 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_70, x_17, x_18, x_19, x_20, x_69);
lean_dec(x_10);
return x_71;
}
else
{
uint8_t x_72; 
lean_dec(x_60);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_72 = !lean_is_exclusive(x_67);
if (x_72 == 0)
{
return x_67;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_67, 0);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_67);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_60);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_76 = !lean_is_exclusive(x_64);
if (x_76 == 0)
{
return x_64;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_64, 0);
x_78 = lean_ctor_get(x_64, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_64);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_80 = !lean_is_exclusive(x_48);
if (x_80 == 0)
{
return x_48;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_48, 0);
x_82 = lean_ctor_get(x_48, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_48);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_13);
lean_dec(x_3);
x_84 = lean_ctor_get(x_28, 1);
lean_inc(x_84);
lean_dec(x_28);
x_85 = lean_ctor_get(x_29, 0);
lean_inc(x_85);
lean_dec(x_29);
x_86 = l_Array_toList___rarg(x_85);
lean_dec(x_85);
x_87 = l_Lean_mkConst(x_1, x_86);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_8);
x_88 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_8, x_15, x_5, x_87, x_17, x_18, x_19, x_20, x_84);
lean_dec(x_15);
if (lean_obj_tag(x_88) == 0)
{
if (x_6 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_17);
lean_inc(x_10);
x_91 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_10, x_12, x_17, x_18, x_19, x_20, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_mkApp(x_89, x_92);
x_95 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_94, x_17, x_18, x_19, x_20, x_93);
lean_dec(x_10);
return x_95;
}
else
{
uint8_t x_96; 
lean_dec(x_89);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_96 = !lean_is_exclusive(x_91);
if (x_96 == 0)
{
return x_91;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_91, 0);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_91);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_88, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_88, 1);
lean_inc(x_101);
lean_dec(x_88);
x_102 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_11);
x_103 = lean_array_push(x_102, x_11);
lean_inc(x_17);
x_104 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_103, x_12, x_17, x_18, x_19, x_20, x_101);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_17);
lean_inc(x_10);
x_107 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_10, x_105, x_17, x_18, x_19, x_20, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_mkApp(x_100, x_108);
x_111 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_110, x_17, x_18, x_19, x_20, x_109);
lean_dec(x_10);
return x_111;
}
else
{
uint8_t x_112; 
lean_dec(x_100);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_112 = !lean_is_exclusive(x_107);
if (x_112 == 0)
{
return x_107;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_107, 0);
x_114 = lean_ctor_get(x_107, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_107);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_100);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_116 = !lean_is_exclusive(x_104);
if (x_116 == 0)
{
return x_104;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_104, 0);
x_118 = lean_ctor_get(x_104, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_104);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_120 = !lean_is_exclusive(x_88);
if (x_120 == 0)
{
return x_88;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_88, 0);
x_122 = lean_ctor_get(x_88, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_88);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_28);
if (x_124 == 0)
{
return x_28;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_28, 0);
x_126 = lean_ctor_get(x_28, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_28);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
case 5:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_14, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_14, 1);
lean_inc(x_129);
lean_dec(x_14);
x_130 = lean_array_set(x_15, x_16, x_129);
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_nat_sub(x_16, x_131);
lean_dec(x_16);
x_14 = x_128;
x_15 = x_130;
x_16 = x_132;
goto _start;
}
default: 
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_134 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3;
x_135 = lean_box(0);
x_136 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_134, x_135, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
return x_136;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after revert&intro");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__3;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__4;
x_5 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_20 = l___private_Lean_Meta_InferType_4__getLevelImp(x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9(x_21, x_15, x_16, x_17, x_18, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_15);
x_26 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_15, x_16, x_17, x_18, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_LocalDecl_type(x_27);
lean_dec(x_27);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_29);
x_30 = l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(x_29, x_2, x_15, x_16, x_17, x_18, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_3, x_29, x_15, x_16, x_17, x_18, x_32);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_29);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Expr_getAppNumArgsAux___main(x_35, x_36);
x_38 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_37);
x_39 = lean_mk_array(x_37, x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_37, x_40);
lean_dec(x_37);
x_42 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_13, x_14, x_24, x_35, x_39, x_41, x_15, x_16, x_17, x_18, x_34);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_20);
if (x_51 == 0)
{
return x_20;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_20, 0);
x_53 = lean_ctor_get(x_20, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_20);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not support dependent elimination, but conclusion depends on major premise");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_9);
x_17 = lean_ctor_get(x_6, 5);
lean_inc(x_17);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_18 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_17, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_13, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_6, 6);
lean_inc(x_24);
x_25 = l_List_redLength___main___rarg(x_24);
x_26 = lean_mk_empty_array_with_capacity(x_25);
lean_dec(x_25);
lean_inc(x_24);
x_27 = l_List_toArrayAux___main___rarg(x_24, x_26);
x_28 = x_27;
x_29 = lean_unsigned_to_nat(0u);
lean_inc(x_23);
lean_inc(x_5);
lean_inc(x_1);
x_30 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_5);
lean_closure_set(x_30, 2, x_8);
lean_closure_set(x_30, 3, x_10);
lean_closure_set(x_30, 4, x_23);
lean_closure_set(x_30, 5, x_24);
lean_closure_set(x_30, 6, x_29);
lean_closure_set(x_30, 7, x_28);
x_31 = x_30;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_32 = lean_apply_5(x_31, x_12, x_13, x_14, x_15, x_22);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_1);
x_35 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_38 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = l_Lean_MetavarContext_exprDependsOn(x_23, x_36, x_2);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
x_39 = x_37;
goto block_89;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_92 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_92, 0, x_3);
x_93 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_94 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_96 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_box(0);
x_98 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_96, x_97, x_12, x_13, x_14, x_15, x_37);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
return x_98;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_98);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_23);
x_39 = x_37;
goto block_89;
}
block_89:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
lean_inc(x_33);
x_40 = x_33;
x_41 = l_Array_umapMAux___main___at_Lean_Meta_introNCore___spec__4(x_29, x_40);
x_42 = x_41;
x_43 = lean_array_push(x_42, x_2);
x_44 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_45 = l_Lean_Meta_revert(x_1, x_43, x_44, x_12, x_13, x_14, x_15, x_39);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_array_get_size(x_33);
x_51 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_52 = l_Lean_Meta_introNCore(x_49, x_50, x_51, x_44, x_12, x_13, x_14, x_15, x_47);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_57 = l_Lean_Meta_intro1Core(x_56, x_44, x_12, x_13, x_14, x_15, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_box(0);
x_63 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_33, x_55, x_33, x_29, x_62);
lean_dec(x_33);
lean_inc(x_61);
x_64 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_64, 0, x_61);
x_65 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_66 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_65, x_64, x_12, x_13, x_14, x_15, x_59);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = x_55;
x_69 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_29, x_68);
x_70 = x_69;
lean_inc(x_60);
x_71 = l_Lean_mkFVar(x_60);
lean_inc(x_61);
x_72 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_72, 0, x_61);
x_73 = lean_box(x_38);
lean_inc(x_61);
x_74 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_74, 0, x_60);
lean_closure_set(x_74, 1, x_7);
lean_closure_set(x_74, 2, x_61);
lean_closure_set(x_74, 3, x_3);
lean_closure_set(x_74, 4, x_4);
lean_closure_set(x_74, 5, x_5);
lean_closure_set(x_74, 6, x_6);
lean_closure_set(x_74, 7, x_17);
lean_closure_set(x_74, 8, x_73);
lean_closure_set(x_74, 9, x_48);
lean_closure_set(x_74, 10, x_63);
lean_closure_set(x_74, 11, x_70);
lean_closure_set(x_74, 12, x_71);
x_75 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_75, 0, x_72);
lean_closure_set(x_75, 1, x_74);
x_76 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_61, x_75, x_12, x_13, x_14, x_15, x_67);
return x_76;
}
else
{
uint8_t x_77; 
lean_dec(x_55);
lean_dec(x_48);
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_57);
if (x_77 == 0)
{
return x_57;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_57, 0);
x_79 = lean_ctor_get(x_57, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_57);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_48);
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_52);
if (x_81 == 0)
{
return x_52;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_52, 0);
x_83 = lean_ctor_get(x_52, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_52);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_45);
if (x_85 == 0)
{
return x_45;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_45, 0);
x_87 = lean_ctor_get(x_45, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_45);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_33);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_35);
if (x_103 == 0)
{
return x_35;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_35, 0);
x_105 = lean_ctor_get(x_35, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_35);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_32);
if (x_107 == 0)
{
return x_32;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_32, 0);
x_109 = lean_ctor_get(x_32, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_32);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_18);
if (x_111 == 0)
{
return x_18;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_18, 0);
x_113 = lean_ctor_get(x_18, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_18);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
case 1:
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_11);
lean_dec(x_9);
x_115 = lean_ctor_get(x_6, 5);
lean_inc(x_115);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_116 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_115, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_st_ref_get(x_13, x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_6, 6);
lean_inc(x_122);
x_123 = l_List_redLength___main___rarg(x_122);
x_124 = lean_mk_empty_array_with_capacity(x_123);
lean_dec(x_123);
lean_inc(x_122);
x_125 = l_List_toArrayAux___main___rarg(x_122, x_124);
x_126 = x_125;
x_127 = lean_unsigned_to_nat(0u);
lean_inc(x_121);
lean_inc(x_5);
lean_inc(x_1);
x_128 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_128, 0, x_1);
lean_closure_set(x_128, 1, x_5);
lean_closure_set(x_128, 2, x_8);
lean_closure_set(x_128, 3, x_10);
lean_closure_set(x_128, 4, x_121);
lean_closure_set(x_128, 5, x_122);
lean_closure_set(x_128, 6, x_127);
lean_closure_set(x_128, 7, x_126);
x_129 = x_128;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_130 = lean_apply_5(x_129, x_12, x_13, x_14, x_15, x_120);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_1);
x_133 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_136 == 0)
{
lean_object* x_188; uint8_t x_189; 
x_188 = l_Lean_MetavarContext_exprDependsOn(x_121, x_134, x_2);
x_189 = lean_unbox(x_188);
lean_dec(x_188);
if (x_189 == 0)
{
x_137 = x_135;
goto block_187;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
lean_dec(x_131);
lean_dec(x_115);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_190 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_190, 0, x_3);
x_191 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_192 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
x_193 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_194 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_box(0);
x_196 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_194, x_195, x_12, x_13, x_14, x_15, x_135);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_197 = !lean_is_exclusive(x_196);
if (x_197 == 0)
{
return x_196;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_196, 0);
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_196);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
else
{
lean_dec(x_134);
lean_dec(x_121);
x_137 = x_135;
goto block_187;
}
block_187:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; 
lean_inc(x_131);
x_138 = x_131;
x_139 = l_Array_umapMAux___main___at_Lean_Meta_introNCore___spec__4(x_127, x_138);
x_140 = x_139;
x_141 = lean_array_push(x_140, x_2);
x_142 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_143 = l_Lean_Meta_revert(x_1, x_141, x_142, x_12, x_13, x_14, x_15, x_137);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_148 = lean_array_get_size(x_131);
x_149 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_150 = l_Lean_Meta_introNCore(x_147, x_148, x_149, x_142, x_12, x_13, x_14, x_15, x_145);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_155 = l_Lean_Meta_intro1Core(x_154, x_142, x_12, x_13, x_14, x_15, x_152);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
x_160 = lean_box(0);
x_161 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_131, x_153, x_131, x_127, x_160);
lean_dec(x_131);
lean_inc(x_159);
x_162 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_162, 0, x_159);
x_163 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_164 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_163, x_162, x_12, x_13, x_14, x_15, x_157);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = x_153;
x_167 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_127, x_166);
x_168 = x_167;
lean_inc(x_158);
x_169 = l_Lean_mkFVar(x_158);
lean_inc(x_159);
x_170 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_170, 0, x_159);
x_171 = lean_box(x_136);
lean_inc(x_159);
x_172 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_172, 0, x_158);
lean_closure_set(x_172, 1, x_7);
lean_closure_set(x_172, 2, x_159);
lean_closure_set(x_172, 3, x_3);
lean_closure_set(x_172, 4, x_4);
lean_closure_set(x_172, 5, x_5);
lean_closure_set(x_172, 6, x_6);
lean_closure_set(x_172, 7, x_115);
lean_closure_set(x_172, 8, x_171);
lean_closure_set(x_172, 9, x_146);
lean_closure_set(x_172, 10, x_161);
lean_closure_set(x_172, 11, x_168);
lean_closure_set(x_172, 12, x_169);
x_173 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_173, 0, x_170);
lean_closure_set(x_173, 1, x_172);
x_174 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_159, x_173, x_12, x_13, x_14, x_15, x_165);
return x_174;
}
else
{
uint8_t x_175; 
lean_dec(x_153);
lean_dec(x_146);
lean_dec(x_131);
lean_dec(x_115);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_175 = !lean_is_exclusive(x_155);
if (x_175 == 0)
{
return x_155;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_155, 0);
x_177 = lean_ctor_get(x_155, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_155);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_146);
lean_dec(x_131);
lean_dec(x_115);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_179 = !lean_is_exclusive(x_150);
if (x_179 == 0)
{
return x_150;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_150, 0);
x_181 = lean_ctor_get(x_150, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_150);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_131);
lean_dec(x_115);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_183 = !lean_is_exclusive(x_143);
if (x_183 == 0)
{
return x_143;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_143, 0);
x_185 = lean_ctor_get(x_143, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_143);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_131);
lean_dec(x_121);
lean_dec(x_115);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_201 = !lean_is_exclusive(x_133);
if (x_201 == 0)
{
return x_133;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_133, 0);
x_203 = lean_ctor_get(x_133, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_133);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_121);
lean_dec(x_115);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_205 = !lean_is_exclusive(x_130);
if (x_205 == 0)
{
return x_130;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_130, 0);
x_207 = lean_ctor_get(x_130, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_130);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_115);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = !lean_is_exclusive(x_116);
if (x_209 == 0)
{
return x_116;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_116, 0);
x_211 = lean_ctor_get(x_116, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_116);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
case 2:
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_11);
lean_dec(x_9);
x_213 = lean_ctor_get(x_6, 5);
lean_inc(x_213);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_214 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_213, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
x_216 = lean_st_ref_get(x_13, x_215);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_ctor_get(x_217, 0);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_ctor_get(x_6, 6);
lean_inc(x_220);
x_221 = l_List_redLength___main___rarg(x_220);
x_222 = lean_mk_empty_array_with_capacity(x_221);
lean_dec(x_221);
lean_inc(x_220);
x_223 = l_List_toArrayAux___main___rarg(x_220, x_222);
x_224 = x_223;
x_225 = lean_unsigned_to_nat(0u);
lean_inc(x_219);
lean_inc(x_5);
lean_inc(x_1);
x_226 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_226, 0, x_1);
lean_closure_set(x_226, 1, x_5);
lean_closure_set(x_226, 2, x_8);
lean_closure_set(x_226, 3, x_10);
lean_closure_set(x_226, 4, x_219);
lean_closure_set(x_226, 5, x_220);
lean_closure_set(x_226, 6, x_225);
lean_closure_set(x_226, 7, x_224);
x_227 = x_226;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_228 = lean_apply_5(x_227, x_12, x_13, x_14, x_15, x_218);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
lean_inc(x_1);
x_231 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_230);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_234 == 0)
{
lean_object* x_286; uint8_t x_287; 
x_286 = l_Lean_MetavarContext_exprDependsOn(x_219, x_232, x_2);
x_287 = lean_unbox(x_286);
lean_dec(x_286);
if (x_287 == 0)
{
x_235 = x_233;
goto block_285;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
lean_dec(x_229);
lean_dec(x_213);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_288 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_288, 0, x_3);
x_289 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_290 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_288);
x_291 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_292 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_293 = lean_box(0);
x_294 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_292, x_293, x_12, x_13, x_14, x_15, x_233);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_295 = !lean_is_exclusive(x_294);
if (x_295 == 0)
{
return x_294;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_294, 0);
x_297 = lean_ctor_get(x_294, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_294);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
else
{
lean_dec(x_232);
lean_dec(x_219);
x_235 = x_233;
goto block_285;
}
block_285:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; 
lean_inc(x_229);
x_236 = x_229;
x_237 = l_Array_umapMAux___main___at_Lean_Meta_introNCore___spec__4(x_225, x_236);
x_238 = x_237;
x_239 = lean_array_push(x_238, x_2);
x_240 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_241 = l_Lean_Meta_revert(x_1, x_239, x_240, x_12, x_13, x_14, x_15, x_235);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_ctor_get(x_242, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_242, 1);
lean_inc(x_245);
lean_dec(x_242);
x_246 = lean_array_get_size(x_229);
x_247 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_248 = l_Lean_Meta_introNCore(x_245, x_246, x_247, x_240, x_12, x_13, x_14, x_15, x_243);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_ctor_get(x_249, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_249, 1);
lean_inc(x_252);
lean_dec(x_249);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_253 = l_Lean_Meta_intro1Core(x_252, x_240, x_12, x_13, x_14, x_15, x_250);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_ctor_get(x_254, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_254, 1);
lean_inc(x_257);
lean_dec(x_254);
x_258 = lean_box(0);
x_259 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_229, x_251, x_229, x_225, x_258);
lean_dec(x_229);
lean_inc(x_257);
x_260 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_260, 0, x_257);
x_261 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_262 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_261, x_260, x_12, x_13, x_14, x_15, x_255);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_264 = x_251;
x_265 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_225, x_264);
x_266 = x_265;
lean_inc(x_256);
x_267 = l_Lean_mkFVar(x_256);
lean_inc(x_257);
x_268 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_268, 0, x_257);
x_269 = lean_box(x_234);
lean_inc(x_257);
x_270 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_270, 0, x_256);
lean_closure_set(x_270, 1, x_7);
lean_closure_set(x_270, 2, x_257);
lean_closure_set(x_270, 3, x_3);
lean_closure_set(x_270, 4, x_4);
lean_closure_set(x_270, 5, x_5);
lean_closure_set(x_270, 6, x_6);
lean_closure_set(x_270, 7, x_213);
lean_closure_set(x_270, 8, x_269);
lean_closure_set(x_270, 9, x_244);
lean_closure_set(x_270, 10, x_259);
lean_closure_set(x_270, 11, x_266);
lean_closure_set(x_270, 12, x_267);
x_271 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_271, 0, x_268);
lean_closure_set(x_271, 1, x_270);
x_272 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_257, x_271, x_12, x_13, x_14, x_15, x_263);
return x_272;
}
else
{
uint8_t x_273; 
lean_dec(x_251);
lean_dec(x_244);
lean_dec(x_229);
lean_dec(x_213);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_273 = !lean_is_exclusive(x_253);
if (x_273 == 0)
{
return x_253;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_253, 0);
x_275 = lean_ctor_get(x_253, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_253);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
else
{
uint8_t x_277; 
lean_dec(x_244);
lean_dec(x_229);
lean_dec(x_213);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_277 = !lean_is_exclusive(x_248);
if (x_277 == 0)
{
return x_248;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_248, 0);
x_279 = lean_ctor_get(x_248, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_248);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
return x_280;
}
}
}
else
{
uint8_t x_281; 
lean_dec(x_229);
lean_dec(x_213);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_281 = !lean_is_exclusive(x_241);
if (x_281 == 0)
{
return x_241;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_241, 0);
x_283 = lean_ctor_get(x_241, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_241);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
}
else
{
uint8_t x_299; 
lean_dec(x_229);
lean_dec(x_219);
lean_dec(x_213);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_299 = !lean_is_exclusive(x_231);
if (x_299 == 0)
{
return x_231;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_231, 0);
x_301 = lean_ctor_get(x_231, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_231);
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
}
}
else
{
uint8_t x_303; 
lean_dec(x_219);
lean_dec(x_213);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_303 = !lean_is_exclusive(x_228);
if (x_303 == 0)
{
return x_228;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_228, 0);
x_305 = lean_ctor_get(x_228, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_228);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
return x_306;
}
}
}
else
{
uint8_t x_307; 
lean_dec(x_213);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_307 = !lean_is_exclusive(x_214);
if (x_307 == 0)
{
return x_214;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_214, 0);
x_309 = lean_ctor_get(x_214, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_214);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
case 3:
{
lean_object* x_311; lean_object* x_312; 
lean_dec(x_11);
lean_dec(x_9);
x_311 = lean_ctor_get(x_6, 5);
lean_inc(x_311);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_312 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_311, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
lean_dec(x_312);
x_314 = lean_st_ref_get(x_13, x_313);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = lean_ctor_get(x_315, 0);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_ctor_get(x_6, 6);
lean_inc(x_318);
x_319 = l_List_redLength___main___rarg(x_318);
x_320 = lean_mk_empty_array_with_capacity(x_319);
lean_dec(x_319);
lean_inc(x_318);
x_321 = l_List_toArrayAux___main___rarg(x_318, x_320);
x_322 = x_321;
x_323 = lean_unsigned_to_nat(0u);
lean_inc(x_317);
lean_inc(x_5);
lean_inc(x_1);
x_324 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_324, 0, x_1);
lean_closure_set(x_324, 1, x_5);
lean_closure_set(x_324, 2, x_8);
lean_closure_set(x_324, 3, x_10);
lean_closure_set(x_324, 4, x_317);
lean_closure_set(x_324, 5, x_318);
lean_closure_set(x_324, 6, x_323);
lean_closure_set(x_324, 7, x_322);
x_325 = x_324;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_326 = lean_apply_5(x_325, x_12, x_13, x_14, x_15, x_316);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
lean_inc(x_1);
x_329 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_328);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
x_332 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_332 == 0)
{
lean_object* x_384; uint8_t x_385; 
x_384 = l_Lean_MetavarContext_exprDependsOn(x_317, x_330, x_2);
x_385 = lean_unbox(x_384);
lean_dec(x_384);
if (x_385 == 0)
{
x_333 = x_331;
goto block_383;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
lean_dec(x_327);
lean_dec(x_311);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_386 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_386, 0, x_3);
x_387 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_388 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_386);
x_389 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_390 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set(x_390, 1, x_389);
x_391 = lean_box(0);
x_392 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_390, x_391, x_12, x_13, x_14, x_15, x_331);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_393 = !lean_is_exclusive(x_392);
if (x_393 == 0)
{
return x_392;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_392, 0);
x_395 = lean_ctor_get(x_392, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_392);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
}
else
{
lean_dec(x_330);
lean_dec(x_317);
x_333 = x_331;
goto block_383;
}
block_383:
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; 
lean_inc(x_327);
x_334 = x_327;
x_335 = l_Array_umapMAux___main___at_Lean_Meta_introNCore___spec__4(x_323, x_334);
x_336 = x_335;
x_337 = lean_array_push(x_336, x_2);
x_338 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_339 = l_Lean_Meta_revert(x_1, x_337, x_338, x_12, x_13, x_14, x_15, x_333);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
x_342 = lean_ctor_get(x_340, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_340, 1);
lean_inc(x_343);
lean_dec(x_340);
x_344 = lean_array_get_size(x_327);
x_345 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_346 = l_Lean_Meta_introNCore(x_343, x_344, x_345, x_338, x_12, x_13, x_14, x_15, x_341);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_347, 1);
lean_inc(x_350);
lean_dec(x_347);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_351 = l_Lean_Meta_intro1Core(x_350, x_338, x_12, x_13, x_14, x_15, x_348);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = lean_ctor_get(x_352, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_352, 1);
lean_inc(x_355);
lean_dec(x_352);
x_356 = lean_box(0);
x_357 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_327, x_349, x_327, x_323, x_356);
lean_dec(x_327);
lean_inc(x_355);
x_358 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_358, 0, x_355);
x_359 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_360 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_359, x_358, x_12, x_13, x_14, x_15, x_353);
x_361 = lean_ctor_get(x_360, 1);
lean_inc(x_361);
lean_dec(x_360);
x_362 = x_349;
x_363 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_323, x_362);
x_364 = x_363;
lean_inc(x_354);
x_365 = l_Lean_mkFVar(x_354);
lean_inc(x_355);
x_366 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_366, 0, x_355);
x_367 = lean_box(x_332);
lean_inc(x_355);
x_368 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_368, 0, x_354);
lean_closure_set(x_368, 1, x_7);
lean_closure_set(x_368, 2, x_355);
lean_closure_set(x_368, 3, x_3);
lean_closure_set(x_368, 4, x_4);
lean_closure_set(x_368, 5, x_5);
lean_closure_set(x_368, 6, x_6);
lean_closure_set(x_368, 7, x_311);
lean_closure_set(x_368, 8, x_367);
lean_closure_set(x_368, 9, x_342);
lean_closure_set(x_368, 10, x_357);
lean_closure_set(x_368, 11, x_364);
lean_closure_set(x_368, 12, x_365);
x_369 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_369, 0, x_366);
lean_closure_set(x_369, 1, x_368);
x_370 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_355, x_369, x_12, x_13, x_14, x_15, x_361);
return x_370;
}
else
{
uint8_t x_371; 
lean_dec(x_349);
lean_dec(x_342);
lean_dec(x_327);
lean_dec(x_311);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_371 = !lean_is_exclusive(x_351);
if (x_371 == 0)
{
return x_351;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_351, 0);
x_373 = lean_ctor_get(x_351, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_351);
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
return x_374;
}
}
}
else
{
uint8_t x_375; 
lean_dec(x_342);
lean_dec(x_327);
lean_dec(x_311);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_375 = !lean_is_exclusive(x_346);
if (x_375 == 0)
{
return x_346;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_346, 0);
x_377 = lean_ctor_get(x_346, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_346);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
else
{
uint8_t x_379; 
lean_dec(x_327);
lean_dec(x_311);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_379 = !lean_is_exclusive(x_339);
if (x_379 == 0)
{
return x_339;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_339, 0);
x_381 = lean_ctor_get(x_339, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_339);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
}
else
{
uint8_t x_397; 
lean_dec(x_327);
lean_dec(x_317);
lean_dec(x_311);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_397 = !lean_is_exclusive(x_329);
if (x_397 == 0)
{
return x_329;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_329, 0);
x_399 = lean_ctor_get(x_329, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_329);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
else
{
uint8_t x_401; 
lean_dec(x_317);
lean_dec(x_311);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_401 = !lean_is_exclusive(x_326);
if (x_401 == 0)
{
return x_326;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_326, 0);
x_403 = lean_ctor_get(x_326, 1);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_326);
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_403);
return x_404;
}
}
}
else
{
uint8_t x_405; 
lean_dec(x_311);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_405 = !lean_is_exclusive(x_312);
if (x_405 == 0)
{
return x_312;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_312, 0);
x_407 = lean_ctor_get(x_312, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_312);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
return x_408;
}
}
}
case 4:
{
lean_object* x_409; lean_object* x_410; 
lean_dec(x_11);
lean_dec(x_9);
x_409 = lean_ctor_get(x_6, 5);
lean_inc(x_409);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_410 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_409, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
lean_dec(x_410);
x_412 = lean_st_ref_get(x_13, x_411);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
x_415 = lean_ctor_get(x_413, 0);
lean_inc(x_415);
lean_dec(x_413);
x_416 = lean_ctor_get(x_6, 6);
lean_inc(x_416);
x_417 = l_List_redLength___main___rarg(x_416);
x_418 = lean_mk_empty_array_with_capacity(x_417);
lean_dec(x_417);
lean_inc(x_416);
x_419 = l_List_toArrayAux___main___rarg(x_416, x_418);
x_420 = x_419;
x_421 = lean_unsigned_to_nat(0u);
lean_inc(x_415);
lean_inc(x_5);
lean_inc(x_1);
x_422 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_422, 0, x_1);
lean_closure_set(x_422, 1, x_5);
lean_closure_set(x_422, 2, x_8);
lean_closure_set(x_422, 3, x_10);
lean_closure_set(x_422, 4, x_415);
lean_closure_set(x_422, 5, x_416);
lean_closure_set(x_422, 6, x_421);
lean_closure_set(x_422, 7, x_420);
x_423 = x_422;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_424 = lean_apply_5(x_423, x_12, x_13, x_14, x_15, x_414);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
lean_inc(x_1);
x_427 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_426);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; uint8_t x_430; lean_object* x_431; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_430 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_430 == 0)
{
lean_object* x_482; uint8_t x_483; 
x_482 = l_Lean_MetavarContext_exprDependsOn(x_415, x_428, x_2);
x_483 = lean_unbox(x_482);
lean_dec(x_482);
if (x_483 == 0)
{
x_431 = x_429;
goto block_481;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; 
lean_dec(x_425);
lean_dec(x_409);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_484 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_484, 0, x_3);
x_485 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_486 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_484);
x_487 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_488 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
x_489 = lean_box(0);
x_490 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_488, x_489, x_12, x_13, x_14, x_15, x_429);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_491 = !lean_is_exclusive(x_490);
if (x_491 == 0)
{
return x_490;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_490, 0);
x_493 = lean_ctor_get(x_490, 1);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_490);
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
return x_494;
}
}
}
else
{
lean_dec(x_428);
lean_dec(x_415);
x_431 = x_429;
goto block_481;
}
block_481:
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; lean_object* x_437; 
lean_inc(x_425);
x_432 = x_425;
x_433 = l_Array_umapMAux___main___at_Lean_Meta_introNCore___spec__4(x_421, x_432);
x_434 = x_433;
x_435 = lean_array_push(x_434, x_2);
x_436 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_437 = l_Lean_Meta_revert(x_1, x_435, x_436, x_12, x_13, x_14, x_15, x_431);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
lean_dec(x_437);
x_440 = lean_ctor_get(x_438, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_438, 1);
lean_inc(x_441);
lean_dec(x_438);
x_442 = lean_array_get_size(x_425);
x_443 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_444 = l_Lean_Meta_introNCore(x_441, x_442, x_443, x_436, x_12, x_13, x_14, x_15, x_439);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
lean_dec(x_444);
x_447 = lean_ctor_get(x_445, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_445, 1);
lean_inc(x_448);
lean_dec(x_445);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_449 = l_Lean_Meta_intro1Core(x_448, x_436, x_12, x_13, x_14, x_15, x_446);
if (lean_obj_tag(x_449) == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
lean_dec(x_449);
x_452 = lean_ctor_get(x_450, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_450, 1);
lean_inc(x_453);
lean_dec(x_450);
x_454 = lean_box(0);
x_455 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_425, x_447, x_425, x_421, x_454);
lean_dec(x_425);
lean_inc(x_453);
x_456 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_456, 0, x_453);
x_457 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_458 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_457, x_456, x_12, x_13, x_14, x_15, x_451);
x_459 = lean_ctor_get(x_458, 1);
lean_inc(x_459);
lean_dec(x_458);
x_460 = x_447;
x_461 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_421, x_460);
x_462 = x_461;
lean_inc(x_452);
x_463 = l_Lean_mkFVar(x_452);
lean_inc(x_453);
x_464 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_464, 0, x_453);
x_465 = lean_box(x_430);
lean_inc(x_453);
x_466 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_466, 0, x_452);
lean_closure_set(x_466, 1, x_7);
lean_closure_set(x_466, 2, x_453);
lean_closure_set(x_466, 3, x_3);
lean_closure_set(x_466, 4, x_4);
lean_closure_set(x_466, 5, x_5);
lean_closure_set(x_466, 6, x_6);
lean_closure_set(x_466, 7, x_409);
lean_closure_set(x_466, 8, x_465);
lean_closure_set(x_466, 9, x_440);
lean_closure_set(x_466, 10, x_455);
lean_closure_set(x_466, 11, x_462);
lean_closure_set(x_466, 12, x_463);
x_467 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_467, 0, x_464);
lean_closure_set(x_467, 1, x_466);
x_468 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_453, x_467, x_12, x_13, x_14, x_15, x_459);
return x_468;
}
else
{
uint8_t x_469; 
lean_dec(x_447);
lean_dec(x_440);
lean_dec(x_425);
lean_dec(x_409);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_469 = !lean_is_exclusive(x_449);
if (x_469 == 0)
{
return x_449;
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_470 = lean_ctor_get(x_449, 0);
x_471 = lean_ctor_get(x_449, 1);
lean_inc(x_471);
lean_inc(x_470);
lean_dec(x_449);
x_472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_471);
return x_472;
}
}
}
else
{
uint8_t x_473; 
lean_dec(x_440);
lean_dec(x_425);
lean_dec(x_409);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_473 = !lean_is_exclusive(x_444);
if (x_473 == 0)
{
return x_444;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_474 = lean_ctor_get(x_444, 0);
x_475 = lean_ctor_get(x_444, 1);
lean_inc(x_475);
lean_inc(x_474);
lean_dec(x_444);
x_476 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set(x_476, 1, x_475);
return x_476;
}
}
}
else
{
uint8_t x_477; 
lean_dec(x_425);
lean_dec(x_409);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_477 = !lean_is_exclusive(x_437);
if (x_477 == 0)
{
return x_437;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_478 = lean_ctor_get(x_437, 0);
x_479 = lean_ctor_get(x_437, 1);
lean_inc(x_479);
lean_inc(x_478);
lean_dec(x_437);
x_480 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_480, 0, x_478);
lean_ctor_set(x_480, 1, x_479);
return x_480;
}
}
}
}
else
{
uint8_t x_495; 
lean_dec(x_425);
lean_dec(x_415);
lean_dec(x_409);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_495 = !lean_is_exclusive(x_427);
if (x_495 == 0)
{
return x_427;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_427, 0);
x_497 = lean_ctor_get(x_427, 1);
lean_inc(x_497);
lean_inc(x_496);
lean_dec(x_427);
x_498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_498, 0, x_496);
lean_ctor_set(x_498, 1, x_497);
return x_498;
}
}
}
else
{
uint8_t x_499; 
lean_dec(x_415);
lean_dec(x_409);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_499 = !lean_is_exclusive(x_424);
if (x_499 == 0)
{
return x_424;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_500 = lean_ctor_get(x_424, 0);
x_501 = lean_ctor_get(x_424, 1);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_424);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_501);
return x_502;
}
}
}
else
{
uint8_t x_503; 
lean_dec(x_409);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_503 = !lean_is_exclusive(x_410);
if (x_503 == 0)
{
return x_410;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = lean_ctor_get(x_410, 0);
x_505 = lean_ctor_get(x_410, 1);
lean_inc(x_505);
lean_inc(x_504);
lean_dec(x_410);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_505);
return x_506;
}
}
}
case 5:
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_507 = lean_ctor_get(x_9, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_9, 1);
lean_inc(x_508);
lean_dec(x_9);
x_509 = lean_array_set(x_10, x_11, x_508);
x_510 = lean_unsigned_to_nat(1u);
x_511 = lean_nat_sub(x_11, x_510);
lean_dec(x_11);
x_9 = x_507;
x_10 = x_509;
x_11 = x_511;
goto _start;
}
case 6:
{
lean_object* x_513; lean_object* x_514; 
lean_dec(x_11);
lean_dec(x_9);
x_513 = lean_ctor_get(x_6, 5);
lean_inc(x_513);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_514 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_513, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_515 = lean_ctor_get(x_514, 1);
lean_inc(x_515);
lean_dec(x_514);
x_516 = lean_st_ref_get(x_13, x_515);
x_517 = lean_ctor_get(x_516, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_516, 1);
lean_inc(x_518);
lean_dec(x_516);
x_519 = lean_ctor_get(x_517, 0);
lean_inc(x_519);
lean_dec(x_517);
x_520 = lean_ctor_get(x_6, 6);
lean_inc(x_520);
x_521 = l_List_redLength___main___rarg(x_520);
x_522 = lean_mk_empty_array_with_capacity(x_521);
lean_dec(x_521);
lean_inc(x_520);
x_523 = l_List_toArrayAux___main___rarg(x_520, x_522);
x_524 = x_523;
x_525 = lean_unsigned_to_nat(0u);
lean_inc(x_519);
lean_inc(x_5);
lean_inc(x_1);
x_526 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_526, 0, x_1);
lean_closure_set(x_526, 1, x_5);
lean_closure_set(x_526, 2, x_8);
lean_closure_set(x_526, 3, x_10);
lean_closure_set(x_526, 4, x_519);
lean_closure_set(x_526, 5, x_520);
lean_closure_set(x_526, 6, x_525);
lean_closure_set(x_526, 7, x_524);
x_527 = x_526;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_528 = lean_apply_5(x_527, x_12, x_13, x_14, x_15, x_518);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_528, 1);
lean_inc(x_530);
lean_dec(x_528);
lean_inc(x_1);
x_531 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_530);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; uint8_t x_534; lean_object* x_535; 
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
lean_dec(x_531);
x_534 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_534 == 0)
{
lean_object* x_586; uint8_t x_587; 
x_586 = l_Lean_MetavarContext_exprDependsOn(x_519, x_532, x_2);
x_587 = lean_unbox(x_586);
lean_dec(x_586);
if (x_587 == 0)
{
x_535 = x_533;
goto block_585;
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; 
lean_dec(x_529);
lean_dec(x_513);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_588 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_588, 0, x_3);
x_589 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_590 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_588);
x_591 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_592 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
x_593 = lean_box(0);
x_594 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_592, x_593, x_12, x_13, x_14, x_15, x_533);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_595 = !lean_is_exclusive(x_594);
if (x_595 == 0)
{
return x_594;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_596 = lean_ctor_get(x_594, 0);
x_597 = lean_ctor_get(x_594, 1);
lean_inc(x_597);
lean_inc(x_596);
lean_dec(x_594);
x_598 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_598, 0, x_596);
lean_ctor_set(x_598, 1, x_597);
return x_598;
}
}
}
else
{
lean_dec(x_532);
lean_dec(x_519);
x_535 = x_533;
goto block_585;
}
block_585:
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; uint8_t x_540; lean_object* x_541; 
lean_inc(x_529);
x_536 = x_529;
x_537 = l_Array_umapMAux___main___at_Lean_Meta_introNCore___spec__4(x_525, x_536);
x_538 = x_537;
x_539 = lean_array_push(x_538, x_2);
x_540 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_541 = l_Lean_Meta_revert(x_1, x_539, x_540, x_12, x_13, x_14, x_15, x_535);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_541, 1);
lean_inc(x_543);
lean_dec(x_541);
x_544 = lean_ctor_get(x_542, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_542, 1);
lean_inc(x_545);
lean_dec(x_542);
x_546 = lean_array_get_size(x_529);
x_547 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_548 = l_Lean_Meta_introNCore(x_545, x_546, x_547, x_540, x_12, x_13, x_14, x_15, x_543);
if (lean_obj_tag(x_548) == 0)
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
lean_dec(x_548);
x_551 = lean_ctor_get(x_549, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_549, 1);
lean_inc(x_552);
lean_dec(x_549);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_553 = l_Lean_Meta_intro1Core(x_552, x_540, x_12, x_13, x_14, x_15, x_550);
if (lean_obj_tag(x_553) == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_554 = lean_ctor_get(x_553, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_553, 1);
lean_inc(x_555);
lean_dec(x_553);
x_556 = lean_ctor_get(x_554, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_554, 1);
lean_inc(x_557);
lean_dec(x_554);
x_558 = lean_box(0);
x_559 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_529, x_551, x_529, x_525, x_558);
lean_dec(x_529);
lean_inc(x_557);
x_560 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_560, 0, x_557);
x_561 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_562 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_561, x_560, x_12, x_13, x_14, x_15, x_555);
x_563 = lean_ctor_get(x_562, 1);
lean_inc(x_563);
lean_dec(x_562);
x_564 = x_551;
x_565 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_525, x_564);
x_566 = x_565;
lean_inc(x_556);
x_567 = l_Lean_mkFVar(x_556);
lean_inc(x_557);
x_568 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_568, 0, x_557);
x_569 = lean_box(x_534);
lean_inc(x_557);
x_570 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_570, 0, x_556);
lean_closure_set(x_570, 1, x_7);
lean_closure_set(x_570, 2, x_557);
lean_closure_set(x_570, 3, x_3);
lean_closure_set(x_570, 4, x_4);
lean_closure_set(x_570, 5, x_5);
lean_closure_set(x_570, 6, x_6);
lean_closure_set(x_570, 7, x_513);
lean_closure_set(x_570, 8, x_569);
lean_closure_set(x_570, 9, x_544);
lean_closure_set(x_570, 10, x_559);
lean_closure_set(x_570, 11, x_566);
lean_closure_set(x_570, 12, x_567);
x_571 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_571, 0, x_568);
lean_closure_set(x_571, 1, x_570);
x_572 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_557, x_571, x_12, x_13, x_14, x_15, x_563);
return x_572;
}
else
{
uint8_t x_573; 
lean_dec(x_551);
lean_dec(x_544);
lean_dec(x_529);
lean_dec(x_513);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_573 = !lean_is_exclusive(x_553);
if (x_573 == 0)
{
return x_553;
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_574 = lean_ctor_get(x_553, 0);
x_575 = lean_ctor_get(x_553, 1);
lean_inc(x_575);
lean_inc(x_574);
lean_dec(x_553);
x_576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_576, 0, x_574);
lean_ctor_set(x_576, 1, x_575);
return x_576;
}
}
}
else
{
uint8_t x_577; 
lean_dec(x_544);
lean_dec(x_529);
lean_dec(x_513);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_577 = !lean_is_exclusive(x_548);
if (x_577 == 0)
{
return x_548;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_578 = lean_ctor_get(x_548, 0);
x_579 = lean_ctor_get(x_548, 1);
lean_inc(x_579);
lean_inc(x_578);
lean_dec(x_548);
x_580 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_580, 0, x_578);
lean_ctor_set(x_580, 1, x_579);
return x_580;
}
}
}
else
{
uint8_t x_581; 
lean_dec(x_529);
lean_dec(x_513);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_581 = !lean_is_exclusive(x_541);
if (x_581 == 0)
{
return x_541;
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_582 = lean_ctor_get(x_541, 0);
x_583 = lean_ctor_get(x_541, 1);
lean_inc(x_583);
lean_inc(x_582);
lean_dec(x_541);
x_584 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_584, 0, x_582);
lean_ctor_set(x_584, 1, x_583);
return x_584;
}
}
}
}
else
{
uint8_t x_599; 
lean_dec(x_529);
lean_dec(x_519);
lean_dec(x_513);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_599 = !lean_is_exclusive(x_531);
if (x_599 == 0)
{
return x_531;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_600 = lean_ctor_get(x_531, 0);
x_601 = lean_ctor_get(x_531, 1);
lean_inc(x_601);
lean_inc(x_600);
lean_dec(x_531);
x_602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_602, 0, x_600);
lean_ctor_set(x_602, 1, x_601);
return x_602;
}
}
}
else
{
uint8_t x_603; 
lean_dec(x_519);
lean_dec(x_513);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_603 = !lean_is_exclusive(x_528);
if (x_603 == 0)
{
return x_528;
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_604 = lean_ctor_get(x_528, 0);
x_605 = lean_ctor_get(x_528, 1);
lean_inc(x_605);
lean_inc(x_604);
lean_dec(x_528);
x_606 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_606, 0, x_604);
lean_ctor_set(x_606, 1, x_605);
return x_606;
}
}
}
else
{
uint8_t x_607; 
lean_dec(x_513);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_607 = !lean_is_exclusive(x_514);
if (x_607 == 0)
{
return x_514;
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_608 = lean_ctor_get(x_514, 0);
x_609 = lean_ctor_get(x_514, 1);
lean_inc(x_609);
lean_inc(x_608);
lean_dec(x_514);
x_610 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_610, 0, x_608);
lean_ctor_set(x_610, 1, x_609);
return x_610;
}
}
}
case 7:
{
lean_object* x_611; lean_object* x_612; 
lean_dec(x_11);
lean_dec(x_9);
x_611 = lean_ctor_get(x_6, 5);
lean_inc(x_611);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_612 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_611, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_613 = lean_ctor_get(x_612, 1);
lean_inc(x_613);
lean_dec(x_612);
x_614 = lean_st_ref_get(x_13, x_613);
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_614, 1);
lean_inc(x_616);
lean_dec(x_614);
x_617 = lean_ctor_get(x_615, 0);
lean_inc(x_617);
lean_dec(x_615);
x_618 = lean_ctor_get(x_6, 6);
lean_inc(x_618);
x_619 = l_List_redLength___main___rarg(x_618);
x_620 = lean_mk_empty_array_with_capacity(x_619);
lean_dec(x_619);
lean_inc(x_618);
x_621 = l_List_toArrayAux___main___rarg(x_618, x_620);
x_622 = x_621;
x_623 = lean_unsigned_to_nat(0u);
lean_inc(x_617);
lean_inc(x_5);
lean_inc(x_1);
x_624 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_624, 0, x_1);
lean_closure_set(x_624, 1, x_5);
lean_closure_set(x_624, 2, x_8);
lean_closure_set(x_624, 3, x_10);
lean_closure_set(x_624, 4, x_617);
lean_closure_set(x_624, 5, x_618);
lean_closure_set(x_624, 6, x_623);
lean_closure_set(x_624, 7, x_622);
x_625 = x_624;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_626 = lean_apply_5(x_625, x_12, x_13, x_14, x_15, x_616);
if (lean_obj_tag(x_626) == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_627 = lean_ctor_get(x_626, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_626, 1);
lean_inc(x_628);
lean_dec(x_626);
lean_inc(x_1);
x_629 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_628);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; lean_object* x_631; uint8_t x_632; lean_object* x_633; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_629, 1);
lean_inc(x_631);
lean_dec(x_629);
x_632 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_632 == 0)
{
lean_object* x_684; uint8_t x_685; 
x_684 = l_Lean_MetavarContext_exprDependsOn(x_617, x_630, x_2);
x_685 = lean_unbox(x_684);
lean_dec(x_684);
if (x_685 == 0)
{
x_633 = x_631;
goto block_683;
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; uint8_t x_693; 
lean_dec(x_627);
lean_dec(x_611);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_686 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_686, 0, x_3);
x_687 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_688 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_688, 0, x_687);
lean_ctor_set(x_688, 1, x_686);
x_689 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_690 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_690, 0, x_688);
lean_ctor_set(x_690, 1, x_689);
x_691 = lean_box(0);
x_692 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_690, x_691, x_12, x_13, x_14, x_15, x_631);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_693 = !lean_is_exclusive(x_692);
if (x_693 == 0)
{
return x_692;
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_694 = lean_ctor_get(x_692, 0);
x_695 = lean_ctor_get(x_692, 1);
lean_inc(x_695);
lean_inc(x_694);
lean_dec(x_692);
x_696 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_696, 0, x_694);
lean_ctor_set(x_696, 1, x_695);
return x_696;
}
}
}
else
{
lean_dec(x_630);
lean_dec(x_617);
x_633 = x_631;
goto block_683;
}
block_683:
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; uint8_t x_638; lean_object* x_639; 
lean_inc(x_627);
x_634 = x_627;
x_635 = l_Array_umapMAux___main___at_Lean_Meta_introNCore___spec__4(x_623, x_634);
x_636 = x_635;
x_637 = lean_array_push(x_636, x_2);
x_638 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_639 = l_Lean_Meta_revert(x_1, x_637, x_638, x_12, x_13, x_14, x_15, x_633);
if (lean_obj_tag(x_639) == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_639, 1);
lean_inc(x_641);
lean_dec(x_639);
x_642 = lean_ctor_get(x_640, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_640, 1);
lean_inc(x_643);
lean_dec(x_640);
x_644 = lean_array_get_size(x_627);
x_645 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_646 = l_Lean_Meta_introNCore(x_643, x_644, x_645, x_638, x_12, x_13, x_14, x_15, x_641);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_647 = lean_ctor_get(x_646, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_646, 1);
lean_inc(x_648);
lean_dec(x_646);
x_649 = lean_ctor_get(x_647, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_647, 1);
lean_inc(x_650);
lean_dec(x_647);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_651 = l_Lean_Meta_intro1Core(x_650, x_638, x_12, x_13, x_14, x_15, x_648);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_651, 1);
lean_inc(x_653);
lean_dec(x_651);
x_654 = lean_ctor_get(x_652, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_652, 1);
lean_inc(x_655);
lean_dec(x_652);
x_656 = lean_box(0);
x_657 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_627, x_649, x_627, x_623, x_656);
lean_dec(x_627);
lean_inc(x_655);
x_658 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_658, 0, x_655);
x_659 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_660 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_659, x_658, x_12, x_13, x_14, x_15, x_653);
x_661 = lean_ctor_get(x_660, 1);
lean_inc(x_661);
lean_dec(x_660);
x_662 = x_649;
x_663 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_623, x_662);
x_664 = x_663;
lean_inc(x_654);
x_665 = l_Lean_mkFVar(x_654);
lean_inc(x_655);
x_666 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_666, 0, x_655);
x_667 = lean_box(x_632);
lean_inc(x_655);
x_668 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_668, 0, x_654);
lean_closure_set(x_668, 1, x_7);
lean_closure_set(x_668, 2, x_655);
lean_closure_set(x_668, 3, x_3);
lean_closure_set(x_668, 4, x_4);
lean_closure_set(x_668, 5, x_5);
lean_closure_set(x_668, 6, x_6);
lean_closure_set(x_668, 7, x_611);
lean_closure_set(x_668, 8, x_667);
lean_closure_set(x_668, 9, x_642);
lean_closure_set(x_668, 10, x_657);
lean_closure_set(x_668, 11, x_664);
lean_closure_set(x_668, 12, x_665);
x_669 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_669, 0, x_666);
lean_closure_set(x_669, 1, x_668);
x_670 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_655, x_669, x_12, x_13, x_14, x_15, x_661);
return x_670;
}
else
{
uint8_t x_671; 
lean_dec(x_649);
lean_dec(x_642);
lean_dec(x_627);
lean_dec(x_611);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_671 = !lean_is_exclusive(x_651);
if (x_671 == 0)
{
return x_651;
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_672 = lean_ctor_get(x_651, 0);
x_673 = lean_ctor_get(x_651, 1);
lean_inc(x_673);
lean_inc(x_672);
lean_dec(x_651);
x_674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_674, 0, x_672);
lean_ctor_set(x_674, 1, x_673);
return x_674;
}
}
}
else
{
uint8_t x_675; 
lean_dec(x_642);
lean_dec(x_627);
lean_dec(x_611);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_675 = !lean_is_exclusive(x_646);
if (x_675 == 0)
{
return x_646;
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_676 = lean_ctor_get(x_646, 0);
x_677 = lean_ctor_get(x_646, 1);
lean_inc(x_677);
lean_inc(x_676);
lean_dec(x_646);
x_678 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_678, 0, x_676);
lean_ctor_set(x_678, 1, x_677);
return x_678;
}
}
}
else
{
uint8_t x_679; 
lean_dec(x_627);
lean_dec(x_611);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_679 = !lean_is_exclusive(x_639);
if (x_679 == 0)
{
return x_639;
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_680 = lean_ctor_get(x_639, 0);
x_681 = lean_ctor_get(x_639, 1);
lean_inc(x_681);
lean_inc(x_680);
lean_dec(x_639);
x_682 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_682, 0, x_680);
lean_ctor_set(x_682, 1, x_681);
return x_682;
}
}
}
}
else
{
uint8_t x_697; 
lean_dec(x_627);
lean_dec(x_617);
lean_dec(x_611);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_697 = !lean_is_exclusive(x_629);
if (x_697 == 0)
{
return x_629;
}
else
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; 
x_698 = lean_ctor_get(x_629, 0);
x_699 = lean_ctor_get(x_629, 1);
lean_inc(x_699);
lean_inc(x_698);
lean_dec(x_629);
x_700 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_700, 0, x_698);
lean_ctor_set(x_700, 1, x_699);
return x_700;
}
}
}
else
{
uint8_t x_701; 
lean_dec(x_617);
lean_dec(x_611);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_701 = !lean_is_exclusive(x_626);
if (x_701 == 0)
{
return x_626;
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_702 = lean_ctor_get(x_626, 0);
x_703 = lean_ctor_get(x_626, 1);
lean_inc(x_703);
lean_inc(x_702);
lean_dec(x_626);
x_704 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_704, 0, x_702);
lean_ctor_set(x_704, 1, x_703);
return x_704;
}
}
}
else
{
uint8_t x_705; 
lean_dec(x_611);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_705 = !lean_is_exclusive(x_612);
if (x_705 == 0)
{
return x_612;
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_706 = lean_ctor_get(x_612, 0);
x_707 = lean_ctor_get(x_612, 1);
lean_inc(x_707);
lean_inc(x_706);
lean_dec(x_612);
x_708 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_708, 0, x_706);
lean_ctor_set(x_708, 1, x_707);
return x_708;
}
}
}
case 8:
{
lean_object* x_709; lean_object* x_710; 
lean_dec(x_11);
lean_dec(x_9);
x_709 = lean_ctor_get(x_6, 5);
lean_inc(x_709);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_710 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_709, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_710) == 0)
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_711 = lean_ctor_get(x_710, 1);
lean_inc(x_711);
lean_dec(x_710);
x_712 = lean_st_ref_get(x_13, x_711);
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_712, 1);
lean_inc(x_714);
lean_dec(x_712);
x_715 = lean_ctor_get(x_713, 0);
lean_inc(x_715);
lean_dec(x_713);
x_716 = lean_ctor_get(x_6, 6);
lean_inc(x_716);
x_717 = l_List_redLength___main___rarg(x_716);
x_718 = lean_mk_empty_array_with_capacity(x_717);
lean_dec(x_717);
lean_inc(x_716);
x_719 = l_List_toArrayAux___main___rarg(x_716, x_718);
x_720 = x_719;
x_721 = lean_unsigned_to_nat(0u);
lean_inc(x_715);
lean_inc(x_5);
lean_inc(x_1);
x_722 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_722, 0, x_1);
lean_closure_set(x_722, 1, x_5);
lean_closure_set(x_722, 2, x_8);
lean_closure_set(x_722, 3, x_10);
lean_closure_set(x_722, 4, x_715);
lean_closure_set(x_722, 5, x_716);
lean_closure_set(x_722, 6, x_721);
lean_closure_set(x_722, 7, x_720);
x_723 = x_722;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_724 = lean_apply_5(x_723, x_12, x_13, x_14, x_15, x_714);
if (lean_obj_tag(x_724) == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_724, 1);
lean_inc(x_726);
lean_dec(x_724);
lean_inc(x_1);
x_727 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_726);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; lean_object* x_729; uint8_t x_730; lean_object* x_731; 
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_727, 1);
lean_inc(x_729);
lean_dec(x_727);
x_730 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_730 == 0)
{
lean_object* x_782; uint8_t x_783; 
x_782 = l_Lean_MetavarContext_exprDependsOn(x_715, x_728, x_2);
x_783 = lean_unbox(x_782);
lean_dec(x_782);
if (x_783 == 0)
{
x_731 = x_729;
goto block_781;
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; 
lean_dec(x_725);
lean_dec(x_709);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_784 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_784, 0, x_3);
x_785 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_786 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_786, 0, x_785);
lean_ctor_set(x_786, 1, x_784);
x_787 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_788 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_788, 0, x_786);
lean_ctor_set(x_788, 1, x_787);
x_789 = lean_box(0);
x_790 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_788, x_789, x_12, x_13, x_14, x_15, x_729);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_791 = !lean_is_exclusive(x_790);
if (x_791 == 0)
{
return x_790;
}
else
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_792 = lean_ctor_get(x_790, 0);
x_793 = lean_ctor_get(x_790, 1);
lean_inc(x_793);
lean_inc(x_792);
lean_dec(x_790);
x_794 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_794, 0, x_792);
lean_ctor_set(x_794, 1, x_793);
return x_794;
}
}
}
else
{
lean_dec(x_728);
lean_dec(x_715);
x_731 = x_729;
goto block_781;
}
block_781:
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; uint8_t x_736; lean_object* x_737; 
lean_inc(x_725);
x_732 = x_725;
x_733 = l_Array_umapMAux___main___at_Lean_Meta_introNCore___spec__4(x_721, x_732);
x_734 = x_733;
x_735 = lean_array_push(x_734, x_2);
x_736 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_737 = l_Lean_Meta_revert(x_1, x_735, x_736, x_12, x_13, x_14, x_15, x_731);
if (lean_obj_tag(x_737) == 0)
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_738 = lean_ctor_get(x_737, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_737, 1);
lean_inc(x_739);
lean_dec(x_737);
x_740 = lean_ctor_get(x_738, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_738, 1);
lean_inc(x_741);
lean_dec(x_738);
x_742 = lean_array_get_size(x_725);
x_743 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_744 = l_Lean_Meta_introNCore(x_741, x_742, x_743, x_736, x_12, x_13, x_14, x_15, x_739);
if (lean_obj_tag(x_744) == 0)
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
x_745 = lean_ctor_get(x_744, 0);
lean_inc(x_745);
x_746 = lean_ctor_get(x_744, 1);
lean_inc(x_746);
lean_dec(x_744);
x_747 = lean_ctor_get(x_745, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_745, 1);
lean_inc(x_748);
lean_dec(x_745);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_749 = l_Lean_Meta_intro1Core(x_748, x_736, x_12, x_13, x_14, x_15, x_746);
if (lean_obj_tag(x_749) == 0)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
x_750 = lean_ctor_get(x_749, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_749, 1);
lean_inc(x_751);
lean_dec(x_749);
x_752 = lean_ctor_get(x_750, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_750, 1);
lean_inc(x_753);
lean_dec(x_750);
x_754 = lean_box(0);
x_755 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_725, x_747, x_725, x_721, x_754);
lean_dec(x_725);
lean_inc(x_753);
x_756 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_756, 0, x_753);
x_757 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_758 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_757, x_756, x_12, x_13, x_14, x_15, x_751);
x_759 = lean_ctor_get(x_758, 1);
lean_inc(x_759);
lean_dec(x_758);
x_760 = x_747;
x_761 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_721, x_760);
x_762 = x_761;
lean_inc(x_752);
x_763 = l_Lean_mkFVar(x_752);
lean_inc(x_753);
x_764 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_764, 0, x_753);
x_765 = lean_box(x_730);
lean_inc(x_753);
x_766 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_766, 0, x_752);
lean_closure_set(x_766, 1, x_7);
lean_closure_set(x_766, 2, x_753);
lean_closure_set(x_766, 3, x_3);
lean_closure_set(x_766, 4, x_4);
lean_closure_set(x_766, 5, x_5);
lean_closure_set(x_766, 6, x_6);
lean_closure_set(x_766, 7, x_709);
lean_closure_set(x_766, 8, x_765);
lean_closure_set(x_766, 9, x_740);
lean_closure_set(x_766, 10, x_755);
lean_closure_set(x_766, 11, x_762);
lean_closure_set(x_766, 12, x_763);
x_767 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_767, 0, x_764);
lean_closure_set(x_767, 1, x_766);
x_768 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_753, x_767, x_12, x_13, x_14, x_15, x_759);
return x_768;
}
else
{
uint8_t x_769; 
lean_dec(x_747);
lean_dec(x_740);
lean_dec(x_725);
lean_dec(x_709);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_769 = !lean_is_exclusive(x_749);
if (x_769 == 0)
{
return x_749;
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; 
x_770 = lean_ctor_get(x_749, 0);
x_771 = lean_ctor_get(x_749, 1);
lean_inc(x_771);
lean_inc(x_770);
lean_dec(x_749);
x_772 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_772, 0, x_770);
lean_ctor_set(x_772, 1, x_771);
return x_772;
}
}
}
else
{
uint8_t x_773; 
lean_dec(x_740);
lean_dec(x_725);
lean_dec(x_709);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_773 = !lean_is_exclusive(x_744);
if (x_773 == 0)
{
return x_744;
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_774 = lean_ctor_get(x_744, 0);
x_775 = lean_ctor_get(x_744, 1);
lean_inc(x_775);
lean_inc(x_774);
lean_dec(x_744);
x_776 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_776, 0, x_774);
lean_ctor_set(x_776, 1, x_775);
return x_776;
}
}
}
else
{
uint8_t x_777; 
lean_dec(x_725);
lean_dec(x_709);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_777 = !lean_is_exclusive(x_737);
if (x_777 == 0)
{
return x_737;
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_778 = lean_ctor_get(x_737, 0);
x_779 = lean_ctor_get(x_737, 1);
lean_inc(x_779);
lean_inc(x_778);
lean_dec(x_737);
x_780 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_780, 0, x_778);
lean_ctor_set(x_780, 1, x_779);
return x_780;
}
}
}
}
else
{
uint8_t x_795; 
lean_dec(x_725);
lean_dec(x_715);
lean_dec(x_709);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_795 = !lean_is_exclusive(x_727);
if (x_795 == 0)
{
return x_727;
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_796 = lean_ctor_get(x_727, 0);
x_797 = lean_ctor_get(x_727, 1);
lean_inc(x_797);
lean_inc(x_796);
lean_dec(x_727);
x_798 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_798, 0, x_796);
lean_ctor_set(x_798, 1, x_797);
return x_798;
}
}
}
else
{
uint8_t x_799; 
lean_dec(x_715);
lean_dec(x_709);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_799 = !lean_is_exclusive(x_724);
if (x_799 == 0)
{
return x_724;
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; 
x_800 = lean_ctor_get(x_724, 0);
x_801 = lean_ctor_get(x_724, 1);
lean_inc(x_801);
lean_inc(x_800);
lean_dec(x_724);
x_802 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_802, 0, x_800);
lean_ctor_set(x_802, 1, x_801);
return x_802;
}
}
}
else
{
uint8_t x_803; 
lean_dec(x_709);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_803 = !lean_is_exclusive(x_710);
if (x_803 == 0)
{
return x_710;
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_804 = lean_ctor_get(x_710, 0);
x_805 = lean_ctor_get(x_710, 1);
lean_inc(x_805);
lean_inc(x_804);
lean_dec(x_710);
x_806 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_806, 0, x_804);
lean_ctor_set(x_806, 1, x_805);
return x_806;
}
}
}
case 9:
{
lean_object* x_807; lean_object* x_808; 
lean_dec(x_11);
lean_dec(x_9);
x_807 = lean_ctor_get(x_6, 5);
lean_inc(x_807);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_808 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_807, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_808) == 0)
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_809 = lean_ctor_get(x_808, 1);
lean_inc(x_809);
lean_dec(x_808);
x_810 = lean_st_ref_get(x_13, x_809);
x_811 = lean_ctor_get(x_810, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_810, 1);
lean_inc(x_812);
lean_dec(x_810);
x_813 = lean_ctor_get(x_811, 0);
lean_inc(x_813);
lean_dec(x_811);
x_814 = lean_ctor_get(x_6, 6);
lean_inc(x_814);
x_815 = l_List_redLength___main___rarg(x_814);
x_816 = lean_mk_empty_array_with_capacity(x_815);
lean_dec(x_815);
lean_inc(x_814);
x_817 = l_List_toArrayAux___main___rarg(x_814, x_816);
x_818 = x_817;
x_819 = lean_unsigned_to_nat(0u);
lean_inc(x_813);
lean_inc(x_5);
lean_inc(x_1);
x_820 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_820, 0, x_1);
lean_closure_set(x_820, 1, x_5);
lean_closure_set(x_820, 2, x_8);
lean_closure_set(x_820, 3, x_10);
lean_closure_set(x_820, 4, x_813);
lean_closure_set(x_820, 5, x_814);
lean_closure_set(x_820, 6, x_819);
lean_closure_set(x_820, 7, x_818);
x_821 = x_820;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_822 = lean_apply_5(x_821, x_12, x_13, x_14, x_15, x_812);
if (lean_obj_tag(x_822) == 0)
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_823 = lean_ctor_get(x_822, 0);
lean_inc(x_823);
x_824 = lean_ctor_get(x_822, 1);
lean_inc(x_824);
lean_dec(x_822);
lean_inc(x_1);
x_825 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_824);
if (lean_obj_tag(x_825) == 0)
{
lean_object* x_826; lean_object* x_827; uint8_t x_828; lean_object* x_829; 
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
lean_dec(x_825);
x_828 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_828 == 0)
{
lean_object* x_880; uint8_t x_881; 
x_880 = l_Lean_MetavarContext_exprDependsOn(x_813, x_826, x_2);
x_881 = lean_unbox(x_880);
lean_dec(x_880);
if (x_881 == 0)
{
x_829 = x_827;
goto block_879;
}
else
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; uint8_t x_889; 
lean_dec(x_823);
lean_dec(x_807);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_882 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_882, 0, x_3);
x_883 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_884 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_884, 0, x_883);
lean_ctor_set(x_884, 1, x_882);
x_885 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_886 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_886, 0, x_884);
lean_ctor_set(x_886, 1, x_885);
x_887 = lean_box(0);
x_888 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_886, x_887, x_12, x_13, x_14, x_15, x_827);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_889 = !lean_is_exclusive(x_888);
if (x_889 == 0)
{
return x_888;
}
else
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; 
x_890 = lean_ctor_get(x_888, 0);
x_891 = lean_ctor_get(x_888, 1);
lean_inc(x_891);
lean_inc(x_890);
lean_dec(x_888);
x_892 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_892, 0, x_890);
lean_ctor_set(x_892, 1, x_891);
return x_892;
}
}
}
else
{
lean_dec(x_826);
lean_dec(x_813);
x_829 = x_827;
goto block_879;
}
block_879:
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; uint8_t x_834; lean_object* x_835; 
lean_inc(x_823);
x_830 = x_823;
x_831 = l_Array_umapMAux___main___at_Lean_Meta_introNCore___spec__4(x_819, x_830);
x_832 = x_831;
x_833 = lean_array_push(x_832, x_2);
x_834 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_835 = l_Lean_Meta_revert(x_1, x_833, x_834, x_12, x_13, x_14, x_15, x_829);
if (lean_obj_tag(x_835) == 0)
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
x_836 = lean_ctor_get(x_835, 0);
lean_inc(x_836);
x_837 = lean_ctor_get(x_835, 1);
lean_inc(x_837);
lean_dec(x_835);
x_838 = lean_ctor_get(x_836, 0);
lean_inc(x_838);
x_839 = lean_ctor_get(x_836, 1);
lean_inc(x_839);
lean_dec(x_836);
x_840 = lean_array_get_size(x_823);
x_841 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_842 = l_Lean_Meta_introNCore(x_839, x_840, x_841, x_834, x_12, x_13, x_14, x_15, x_837);
if (lean_obj_tag(x_842) == 0)
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
x_843 = lean_ctor_get(x_842, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_842, 1);
lean_inc(x_844);
lean_dec(x_842);
x_845 = lean_ctor_get(x_843, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_843, 1);
lean_inc(x_846);
lean_dec(x_843);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_847 = l_Lean_Meta_intro1Core(x_846, x_834, x_12, x_13, x_14, x_15, x_844);
if (lean_obj_tag(x_847) == 0)
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; 
x_848 = lean_ctor_get(x_847, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_847, 1);
lean_inc(x_849);
lean_dec(x_847);
x_850 = lean_ctor_get(x_848, 0);
lean_inc(x_850);
x_851 = lean_ctor_get(x_848, 1);
lean_inc(x_851);
lean_dec(x_848);
x_852 = lean_box(0);
x_853 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_823, x_845, x_823, x_819, x_852);
lean_dec(x_823);
lean_inc(x_851);
x_854 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_854, 0, x_851);
x_855 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_856 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_855, x_854, x_12, x_13, x_14, x_15, x_849);
x_857 = lean_ctor_get(x_856, 1);
lean_inc(x_857);
lean_dec(x_856);
x_858 = x_845;
x_859 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_819, x_858);
x_860 = x_859;
lean_inc(x_850);
x_861 = l_Lean_mkFVar(x_850);
lean_inc(x_851);
x_862 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_862, 0, x_851);
x_863 = lean_box(x_828);
lean_inc(x_851);
x_864 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_864, 0, x_850);
lean_closure_set(x_864, 1, x_7);
lean_closure_set(x_864, 2, x_851);
lean_closure_set(x_864, 3, x_3);
lean_closure_set(x_864, 4, x_4);
lean_closure_set(x_864, 5, x_5);
lean_closure_set(x_864, 6, x_6);
lean_closure_set(x_864, 7, x_807);
lean_closure_set(x_864, 8, x_863);
lean_closure_set(x_864, 9, x_838);
lean_closure_set(x_864, 10, x_853);
lean_closure_set(x_864, 11, x_860);
lean_closure_set(x_864, 12, x_861);
x_865 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_865, 0, x_862);
lean_closure_set(x_865, 1, x_864);
x_866 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_851, x_865, x_12, x_13, x_14, x_15, x_857);
return x_866;
}
else
{
uint8_t x_867; 
lean_dec(x_845);
lean_dec(x_838);
lean_dec(x_823);
lean_dec(x_807);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_867 = !lean_is_exclusive(x_847);
if (x_867 == 0)
{
return x_847;
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_868 = lean_ctor_get(x_847, 0);
x_869 = lean_ctor_get(x_847, 1);
lean_inc(x_869);
lean_inc(x_868);
lean_dec(x_847);
x_870 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_870, 0, x_868);
lean_ctor_set(x_870, 1, x_869);
return x_870;
}
}
}
else
{
uint8_t x_871; 
lean_dec(x_838);
lean_dec(x_823);
lean_dec(x_807);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_871 = !lean_is_exclusive(x_842);
if (x_871 == 0)
{
return x_842;
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; 
x_872 = lean_ctor_get(x_842, 0);
x_873 = lean_ctor_get(x_842, 1);
lean_inc(x_873);
lean_inc(x_872);
lean_dec(x_842);
x_874 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_874, 0, x_872);
lean_ctor_set(x_874, 1, x_873);
return x_874;
}
}
}
else
{
uint8_t x_875; 
lean_dec(x_823);
lean_dec(x_807);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_875 = !lean_is_exclusive(x_835);
if (x_875 == 0)
{
return x_835;
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_876 = lean_ctor_get(x_835, 0);
x_877 = lean_ctor_get(x_835, 1);
lean_inc(x_877);
lean_inc(x_876);
lean_dec(x_835);
x_878 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_878, 0, x_876);
lean_ctor_set(x_878, 1, x_877);
return x_878;
}
}
}
}
else
{
uint8_t x_893; 
lean_dec(x_823);
lean_dec(x_813);
lean_dec(x_807);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_893 = !lean_is_exclusive(x_825);
if (x_893 == 0)
{
return x_825;
}
else
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; 
x_894 = lean_ctor_get(x_825, 0);
x_895 = lean_ctor_get(x_825, 1);
lean_inc(x_895);
lean_inc(x_894);
lean_dec(x_825);
x_896 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_896, 0, x_894);
lean_ctor_set(x_896, 1, x_895);
return x_896;
}
}
}
else
{
uint8_t x_897; 
lean_dec(x_813);
lean_dec(x_807);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_897 = !lean_is_exclusive(x_822);
if (x_897 == 0)
{
return x_822;
}
else
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; 
x_898 = lean_ctor_get(x_822, 0);
x_899 = lean_ctor_get(x_822, 1);
lean_inc(x_899);
lean_inc(x_898);
lean_dec(x_822);
x_900 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_900, 0, x_898);
lean_ctor_set(x_900, 1, x_899);
return x_900;
}
}
}
else
{
uint8_t x_901; 
lean_dec(x_807);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_901 = !lean_is_exclusive(x_808);
if (x_901 == 0)
{
return x_808;
}
else
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; 
x_902 = lean_ctor_get(x_808, 0);
x_903 = lean_ctor_get(x_808, 1);
lean_inc(x_903);
lean_inc(x_902);
lean_dec(x_808);
x_904 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_904, 0, x_902);
lean_ctor_set(x_904, 1, x_903);
return x_904;
}
}
}
case 10:
{
lean_object* x_905; lean_object* x_906; 
lean_dec(x_11);
lean_dec(x_9);
x_905 = lean_ctor_get(x_6, 5);
lean_inc(x_905);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_906 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_905, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_906) == 0)
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; 
x_907 = lean_ctor_get(x_906, 1);
lean_inc(x_907);
lean_dec(x_906);
x_908 = lean_st_ref_get(x_13, x_907);
x_909 = lean_ctor_get(x_908, 0);
lean_inc(x_909);
x_910 = lean_ctor_get(x_908, 1);
lean_inc(x_910);
lean_dec(x_908);
x_911 = lean_ctor_get(x_909, 0);
lean_inc(x_911);
lean_dec(x_909);
x_912 = lean_ctor_get(x_6, 6);
lean_inc(x_912);
x_913 = l_List_redLength___main___rarg(x_912);
x_914 = lean_mk_empty_array_with_capacity(x_913);
lean_dec(x_913);
lean_inc(x_912);
x_915 = l_List_toArrayAux___main___rarg(x_912, x_914);
x_916 = x_915;
x_917 = lean_unsigned_to_nat(0u);
lean_inc(x_911);
lean_inc(x_5);
lean_inc(x_1);
x_918 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_918, 0, x_1);
lean_closure_set(x_918, 1, x_5);
lean_closure_set(x_918, 2, x_8);
lean_closure_set(x_918, 3, x_10);
lean_closure_set(x_918, 4, x_911);
lean_closure_set(x_918, 5, x_912);
lean_closure_set(x_918, 6, x_917);
lean_closure_set(x_918, 7, x_916);
x_919 = x_918;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_920 = lean_apply_5(x_919, x_12, x_13, x_14, x_15, x_910);
if (lean_obj_tag(x_920) == 0)
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_921 = lean_ctor_get(x_920, 0);
lean_inc(x_921);
x_922 = lean_ctor_get(x_920, 1);
lean_inc(x_922);
lean_dec(x_920);
lean_inc(x_1);
x_923 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_922);
if (lean_obj_tag(x_923) == 0)
{
lean_object* x_924; lean_object* x_925; uint8_t x_926; lean_object* x_927; 
x_924 = lean_ctor_get(x_923, 0);
lean_inc(x_924);
x_925 = lean_ctor_get(x_923, 1);
lean_inc(x_925);
lean_dec(x_923);
x_926 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_926 == 0)
{
lean_object* x_978; uint8_t x_979; 
x_978 = l_Lean_MetavarContext_exprDependsOn(x_911, x_924, x_2);
x_979 = lean_unbox(x_978);
lean_dec(x_978);
if (x_979 == 0)
{
x_927 = x_925;
goto block_977;
}
else
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; uint8_t x_987; 
lean_dec(x_921);
lean_dec(x_905);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_980 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_980, 0, x_3);
x_981 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_982 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_982, 0, x_981);
lean_ctor_set(x_982, 1, x_980);
x_983 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_984 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_984, 0, x_982);
lean_ctor_set(x_984, 1, x_983);
x_985 = lean_box(0);
x_986 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_984, x_985, x_12, x_13, x_14, x_15, x_925);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_987 = !lean_is_exclusive(x_986);
if (x_987 == 0)
{
return x_986;
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; 
x_988 = lean_ctor_get(x_986, 0);
x_989 = lean_ctor_get(x_986, 1);
lean_inc(x_989);
lean_inc(x_988);
lean_dec(x_986);
x_990 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_990, 0, x_988);
lean_ctor_set(x_990, 1, x_989);
return x_990;
}
}
}
else
{
lean_dec(x_924);
lean_dec(x_911);
x_927 = x_925;
goto block_977;
}
block_977:
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; uint8_t x_932; lean_object* x_933; 
lean_inc(x_921);
x_928 = x_921;
x_929 = l_Array_umapMAux___main___at_Lean_Meta_introNCore___spec__4(x_917, x_928);
x_930 = x_929;
x_931 = lean_array_push(x_930, x_2);
x_932 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_933 = l_Lean_Meta_revert(x_1, x_931, x_932, x_12, x_13, x_14, x_15, x_927);
if (lean_obj_tag(x_933) == 0)
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_934 = lean_ctor_get(x_933, 0);
lean_inc(x_934);
x_935 = lean_ctor_get(x_933, 1);
lean_inc(x_935);
lean_dec(x_933);
x_936 = lean_ctor_get(x_934, 0);
lean_inc(x_936);
x_937 = lean_ctor_get(x_934, 1);
lean_inc(x_937);
lean_dec(x_934);
x_938 = lean_array_get_size(x_921);
x_939 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_940 = l_Lean_Meta_introNCore(x_937, x_938, x_939, x_932, x_12, x_13, x_14, x_15, x_935);
if (lean_obj_tag(x_940) == 0)
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; 
x_941 = lean_ctor_get(x_940, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_940, 1);
lean_inc(x_942);
lean_dec(x_940);
x_943 = lean_ctor_get(x_941, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_941, 1);
lean_inc(x_944);
lean_dec(x_941);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_945 = l_Lean_Meta_intro1Core(x_944, x_932, x_12, x_13, x_14, x_15, x_942);
if (lean_obj_tag(x_945) == 0)
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; 
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_945, 1);
lean_inc(x_947);
lean_dec(x_945);
x_948 = lean_ctor_get(x_946, 0);
lean_inc(x_948);
x_949 = lean_ctor_get(x_946, 1);
lean_inc(x_949);
lean_dec(x_946);
x_950 = lean_box(0);
x_951 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_921, x_943, x_921, x_917, x_950);
lean_dec(x_921);
lean_inc(x_949);
x_952 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_952, 0, x_949);
x_953 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_954 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_953, x_952, x_12, x_13, x_14, x_15, x_947);
x_955 = lean_ctor_get(x_954, 1);
lean_inc(x_955);
lean_dec(x_954);
x_956 = x_943;
x_957 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_917, x_956);
x_958 = x_957;
lean_inc(x_948);
x_959 = l_Lean_mkFVar(x_948);
lean_inc(x_949);
x_960 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_960, 0, x_949);
x_961 = lean_box(x_926);
lean_inc(x_949);
x_962 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_962, 0, x_948);
lean_closure_set(x_962, 1, x_7);
lean_closure_set(x_962, 2, x_949);
lean_closure_set(x_962, 3, x_3);
lean_closure_set(x_962, 4, x_4);
lean_closure_set(x_962, 5, x_5);
lean_closure_set(x_962, 6, x_6);
lean_closure_set(x_962, 7, x_905);
lean_closure_set(x_962, 8, x_961);
lean_closure_set(x_962, 9, x_936);
lean_closure_set(x_962, 10, x_951);
lean_closure_set(x_962, 11, x_958);
lean_closure_set(x_962, 12, x_959);
x_963 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_963, 0, x_960);
lean_closure_set(x_963, 1, x_962);
x_964 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_949, x_963, x_12, x_13, x_14, x_15, x_955);
return x_964;
}
else
{
uint8_t x_965; 
lean_dec(x_943);
lean_dec(x_936);
lean_dec(x_921);
lean_dec(x_905);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_965 = !lean_is_exclusive(x_945);
if (x_965 == 0)
{
return x_945;
}
else
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; 
x_966 = lean_ctor_get(x_945, 0);
x_967 = lean_ctor_get(x_945, 1);
lean_inc(x_967);
lean_inc(x_966);
lean_dec(x_945);
x_968 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_968, 0, x_966);
lean_ctor_set(x_968, 1, x_967);
return x_968;
}
}
}
else
{
uint8_t x_969; 
lean_dec(x_936);
lean_dec(x_921);
lean_dec(x_905);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_969 = !lean_is_exclusive(x_940);
if (x_969 == 0)
{
return x_940;
}
else
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; 
x_970 = lean_ctor_get(x_940, 0);
x_971 = lean_ctor_get(x_940, 1);
lean_inc(x_971);
lean_inc(x_970);
lean_dec(x_940);
x_972 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_972, 0, x_970);
lean_ctor_set(x_972, 1, x_971);
return x_972;
}
}
}
else
{
uint8_t x_973; 
lean_dec(x_921);
lean_dec(x_905);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_973 = !lean_is_exclusive(x_933);
if (x_973 == 0)
{
return x_933;
}
else
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; 
x_974 = lean_ctor_get(x_933, 0);
x_975 = lean_ctor_get(x_933, 1);
lean_inc(x_975);
lean_inc(x_974);
lean_dec(x_933);
x_976 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_976, 0, x_974);
lean_ctor_set(x_976, 1, x_975);
return x_976;
}
}
}
}
else
{
uint8_t x_991; 
lean_dec(x_921);
lean_dec(x_911);
lean_dec(x_905);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_991 = !lean_is_exclusive(x_923);
if (x_991 == 0)
{
return x_923;
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; 
x_992 = lean_ctor_get(x_923, 0);
x_993 = lean_ctor_get(x_923, 1);
lean_inc(x_993);
lean_inc(x_992);
lean_dec(x_923);
x_994 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_994, 0, x_992);
lean_ctor_set(x_994, 1, x_993);
return x_994;
}
}
}
else
{
uint8_t x_995; 
lean_dec(x_911);
lean_dec(x_905);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_995 = !lean_is_exclusive(x_920);
if (x_995 == 0)
{
return x_920;
}
else
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; 
x_996 = lean_ctor_get(x_920, 0);
x_997 = lean_ctor_get(x_920, 1);
lean_inc(x_997);
lean_inc(x_996);
lean_dec(x_920);
x_998 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_998, 0, x_996);
lean_ctor_set(x_998, 1, x_997);
return x_998;
}
}
}
else
{
uint8_t x_999; 
lean_dec(x_905);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_999 = !lean_is_exclusive(x_906);
if (x_999 == 0)
{
return x_906;
}
else
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
x_1000 = lean_ctor_get(x_906, 0);
x_1001 = lean_ctor_get(x_906, 1);
lean_inc(x_1001);
lean_inc(x_1000);
lean_dec(x_906);
x_1002 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1002, 0, x_1000);
lean_ctor_set(x_1002, 1, x_1001);
return x_1002;
}
}
}
case 11:
{
lean_object* x_1003; lean_object* x_1004; 
lean_dec(x_11);
lean_dec(x_9);
x_1003 = lean_ctor_get(x_6, 5);
lean_inc(x_1003);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_1004 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_1003, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_1004) == 0)
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
x_1005 = lean_ctor_get(x_1004, 1);
lean_inc(x_1005);
lean_dec(x_1004);
x_1006 = lean_st_ref_get(x_13, x_1005);
x_1007 = lean_ctor_get(x_1006, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_1006, 1);
lean_inc(x_1008);
lean_dec(x_1006);
x_1009 = lean_ctor_get(x_1007, 0);
lean_inc(x_1009);
lean_dec(x_1007);
x_1010 = lean_ctor_get(x_6, 6);
lean_inc(x_1010);
x_1011 = l_List_redLength___main___rarg(x_1010);
x_1012 = lean_mk_empty_array_with_capacity(x_1011);
lean_dec(x_1011);
lean_inc(x_1010);
x_1013 = l_List_toArrayAux___main___rarg(x_1010, x_1012);
x_1014 = x_1013;
x_1015 = lean_unsigned_to_nat(0u);
lean_inc(x_1009);
lean_inc(x_5);
lean_inc(x_1);
x_1016 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_1016, 0, x_1);
lean_closure_set(x_1016, 1, x_5);
lean_closure_set(x_1016, 2, x_8);
lean_closure_set(x_1016, 3, x_10);
lean_closure_set(x_1016, 4, x_1009);
lean_closure_set(x_1016, 5, x_1010);
lean_closure_set(x_1016, 6, x_1015);
lean_closure_set(x_1016, 7, x_1014);
x_1017 = x_1016;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_1018 = lean_apply_5(x_1017, x_12, x_13, x_14, x_15, x_1008);
if (lean_obj_tag(x_1018) == 0)
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1019 = lean_ctor_get(x_1018, 0);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_1018, 1);
lean_inc(x_1020);
lean_dec(x_1018);
lean_inc(x_1);
x_1021 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_1020);
if (lean_obj_tag(x_1021) == 0)
{
lean_object* x_1022; lean_object* x_1023; uint8_t x_1024; lean_object* x_1025; 
x_1022 = lean_ctor_get(x_1021, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1021, 1);
lean_inc(x_1023);
lean_dec(x_1021);
x_1024 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_1024 == 0)
{
lean_object* x_1076; uint8_t x_1077; 
x_1076 = l_Lean_MetavarContext_exprDependsOn(x_1009, x_1022, x_2);
x_1077 = lean_unbox(x_1076);
lean_dec(x_1076);
if (x_1077 == 0)
{
x_1025 = x_1023;
goto block_1075;
}
else
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; uint8_t x_1085; 
lean_dec(x_1019);
lean_dec(x_1003);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1078 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1078, 0, x_3);
x_1079 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_1080 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1080, 0, x_1079);
lean_ctor_set(x_1080, 1, x_1078);
x_1081 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_1082 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1082, 0, x_1080);
lean_ctor_set(x_1082, 1, x_1081);
x_1083 = lean_box(0);
x_1084 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_1082, x_1083, x_12, x_13, x_14, x_15, x_1023);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_1085 = !lean_is_exclusive(x_1084);
if (x_1085 == 0)
{
return x_1084;
}
else
{
lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; 
x_1086 = lean_ctor_get(x_1084, 0);
x_1087 = lean_ctor_get(x_1084, 1);
lean_inc(x_1087);
lean_inc(x_1086);
lean_dec(x_1084);
x_1088 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1088, 0, x_1086);
lean_ctor_set(x_1088, 1, x_1087);
return x_1088;
}
}
}
else
{
lean_dec(x_1022);
lean_dec(x_1009);
x_1025 = x_1023;
goto block_1075;
}
block_1075:
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; uint8_t x_1030; lean_object* x_1031; 
lean_inc(x_1019);
x_1026 = x_1019;
x_1027 = l_Array_umapMAux___main___at_Lean_Meta_introNCore___spec__4(x_1015, x_1026);
x_1028 = x_1027;
x_1029 = lean_array_push(x_1028, x_2);
x_1030 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_1031 = l_Lean_Meta_revert(x_1, x_1029, x_1030, x_12, x_13, x_14, x_15, x_1025);
if (lean_obj_tag(x_1031) == 0)
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
x_1033 = lean_ctor_get(x_1031, 1);
lean_inc(x_1033);
lean_dec(x_1031);
x_1034 = lean_ctor_get(x_1032, 0);
lean_inc(x_1034);
x_1035 = lean_ctor_get(x_1032, 1);
lean_inc(x_1035);
lean_dec(x_1032);
x_1036 = lean_array_get_size(x_1019);
x_1037 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_1038 = l_Lean_Meta_introNCore(x_1035, x_1036, x_1037, x_1030, x_12, x_13, x_14, x_15, x_1033);
if (lean_obj_tag(x_1038) == 0)
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
x_1039 = lean_ctor_get(x_1038, 0);
lean_inc(x_1039);
x_1040 = lean_ctor_get(x_1038, 1);
lean_inc(x_1040);
lean_dec(x_1038);
x_1041 = lean_ctor_get(x_1039, 0);
lean_inc(x_1041);
x_1042 = lean_ctor_get(x_1039, 1);
lean_inc(x_1042);
lean_dec(x_1039);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_1043 = l_Lean_Meta_intro1Core(x_1042, x_1030, x_12, x_13, x_14, x_15, x_1040);
if (lean_obj_tag(x_1043) == 0)
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; 
x_1044 = lean_ctor_get(x_1043, 0);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_1043, 1);
lean_inc(x_1045);
lean_dec(x_1043);
x_1046 = lean_ctor_get(x_1044, 0);
lean_inc(x_1046);
x_1047 = lean_ctor_get(x_1044, 1);
lean_inc(x_1047);
lean_dec(x_1044);
x_1048 = lean_box(0);
x_1049 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1019, x_1041, x_1019, x_1015, x_1048);
lean_dec(x_1019);
lean_inc(x_1047);
x_1050 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_1050, 0, x_1047);
x_1051 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1052 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_1051, x_1050, x_12, x_13, x_14, x_15, x_1045);
x_1053 = lean_ctor_get(x_1052, 1);
lean_inc(x_1053);
lean_dec(x_1052);
x_1054 = x_1041;
x_1055 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1015, x_1054);
x_1056 = x_1055;
lean_inc(x_1046);
x_1057 = l_Lean_mkFVar(x_1046);
lean_inc(x_1047);
x_1058 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1058, 0, x_1047);
x_1059 = lean_box(x_1024);
lean_inc(x_1047);
x_1060 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_1060, 0, x_1046);
lean_closure_set(x_1060, 1, x_7);
lean_closure_set(x_1060, 2, x_1047);
lean_closure_set(x_1060, 3, x_3);
lean_closure_set(x_1060, 4, x_4);
lean_closure_set(x_1060, 5, x_5);
lean_closure_set(x_1060, 6, x_6);
lean_closure_set(x_1060, 7, x_1003);
lean_closure_set(x_1060, 8, x_1059);
lean_closure_set(x_1060, 9, x_1034);
lean_closure_set(x_1060, 10, x_1049);
lean_closure_set(x_1060, 11, x_1056);
lean_closure_set(x_1060, 12, x_1057);
x_1061 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1061, 0, x_1058);
lean_closure_set(x_1061, 1, x_1060);
x_1062 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1047, x_1061, x_12, x_13, x_14, x_15, x_1053);
return x_1062;
}
else
{
uint8_t x_1063; 
lean_dec(x_1041);
lean_dec(x_1034);
lean_dec(x_1019);
lean_dec(x_1003);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1063 = !lean_is_exclusive(x_1043);
if (x_1063 == 0)
{
return x_1043;
}
else
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
x_1064 = lean_ctor_get(x_1043, 0);
x_1065 = lean_ctor_get(x_1043, 1);
lean_inc(x_1065);
lean_inc(x_1064);
lean_dec(x_1043);
x_1066 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1066, 0, x_1064);
lean_ctor_set(x_1066, 1, x_1065);
return x_1066;
}
}
}
else
{
uint8_t x_1067; 
lean_dec(x_1034);
lean_dec(x_1019);
lean_dec(x_1003);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1067 = !lean_is_exclusive(x_1038);
if (x_1067 == 0)
{
return x_1038;
}
else
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
x_1068 = lean_ctor_get(x_1038, 0);
x_1069 = lean_ctor_get(x_1038, 1);
lean_inc(x_1069);
lean_inc(x_1068);
lean_dec(x_1038);
x_1070 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1070, 0, x_1068);
lean_ctor_set(x_1070, 1, x_1069);
return x_1070;
}
}
}
else
{
uint8_t x_1071; 
lean_dec(x_1019);
lean_dec(x_1003);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1071 = !lean_is_exclusive(x_1031);
if (x_1071 == 0)
{
return x_1031;
}
else
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; 
x_1072 = lean_ctor_get(x_1031, 0);
x_1073 = lean_ctor_get(x_1031, 1);
lean_inc(x_1073);
lean_inc(x_1072);
lean_dec(x_1031);
x_1074 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1074, 0, x_1072);
lean_ctor_set(x_1074, 1, x_1073);
return x_1074;
}
}
}
}
else
{
uint8_t x_1089; 
lean_dec(x_1019);
lean_dec(x_1009);
lean_dec(x_1003);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1089 = !lean_is_exclusive(x_1021);
if (x_1089 == 0)
{
return x_1021;
}
else
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; 
x_1090 = lean_ctor_get(x_1021, 0);
x_1091 = lean_ctor_get(x_1021, 1);
lean_inc(x_1091);
lean_inc(x_1090);
lean_dec(x_1021);
x_1092 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1092, 0, x_1090);
lean_ctor_set(x_1092, 1, x_1091);
return x_1092;
}
}
}
else
{
uint8_t x_1093; 
lean_dec(x_1009);
lean_dec(x_1003);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1093 = !lean_is_exclusive(x_1018);
if (x_1093 == 0)
{
return x_1018;
}
else
{
lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
x_1094 = lean_ctor_get(x_1018, 0);
x_1095 = lean_ctor_get(x_1018, 1);
lean_inc(x_1095);
lean_inc(x_1094);
lean_dec(x_1018);
x_1096 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1096, 0, x_1094);
lean_ctor_set(x_1096, 1, x_1095);
return x_1096;
}
}
}
else
{
uint8_t x_1097; 
lean_dec(x_1003);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1097 = !lean_is_exclusive(x_1004);
if (x_1097 == 0)
{
return x_1004;
}
else
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
x_1098 = lean_ctor_get(x_1004, 0);
x_1099 = lean_ctor_get(x_1004, 1);
lean_inc(x_1099);
lean_inc(x_1098);
lean_dec(x_1004);
x_1100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1100, 0, x_1098);
lean_ctor_set(x_1100, 1, x_1099);
return x_1100;
}
}
}
default: 
{
lean_object* x_1101; lean_object* x_1102; 
lean_dec(x_11);
lean_dec(x_9);
x_1101 = lean_ctor_get(x_6, 5);
lean_inc(x_1101);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_1102 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_1101, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_1102) == 0)
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; 
x_1103 = lean_ctor_get(x_1102, 1);
lean_inc(x_1103);
lean_dec(x_1102);
x_1104 = lean_st_ref_get(x_13, x_1103);
x_1105 = lean_ctor_get(x_1104, 0);
lean_inc(x_1105);
x_1106 = lean_ctor_get(x_1104, 1);
lean_inc(x_1106);
lean_dec(x_1104);
x_1107 = lean_ctor_get(x_1105, 0);
lean_inc(x_1107);
lean_dec(x_1105);
x_1108 = lean_ctor_get(x_6, 6);
lean_inc(x_1108);
x_1109 = l_List_redLength___main___rarg(x_1108);
x_1110 = lean_mk_empty_array_with_capacity(x_1109);
lean_dec(x_1109);
lean_inc(x_1108);
x_1111 = l_List_toArrayAux___main___rarg(x_1108, x_1110);
x_1112 = x_1111;
x_1113 = lean_unsigned_to_nat(0u);
lean_inc(x_1107);
lean_inc(x_5);
lean_inc(x_1);
x_1114 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_1114, 0, x_1);
lean_closure_set(x_1114, 1, x_5);
lean_closure_set(x_1114, 2, x_8);
lean_closure_set(x_1114, 3, x_10);
lean_closure_set(x_1114, 4, x_1107);
lean_closure_set(x_1114, 5, x_1108);
lean_closure_set(x_1114, 6, x_1113);
lean_closure_set(x_1114, 7, x_1112);
x_1115 = x_1114;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_1116 = lean_apply_5(x_1115, x_12, x_13, x_14, x_15, x_1106);
if (lean_obj_tag(x_1116) == 0)
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; 
x_1117 = lean_ctor_get(x_1116, 0);
lean_inc(x_1117);
x_1118 = lean_ctor_get(x_1116, 1);
lean_inc(x_1118);
lean_dec(x_1116);
lean_inc(x_1);
x_1119 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_1118);
if (lean_obj_tag(x_1119) == 0)
{
lean_object* x_1120; lean_object* x_1121; uint8_t x_1122; lean_object* x_1123; 
x_1120 = lean_ctor_get(x_1119, 0);
lean_inc(x_1120);
x_1121 = lean_ctor_get(x_1119, 1);
lean_inc(x_1121);
lean_dec(x_1119);
x_1122 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_1122 == 0)
{
lean_object* x_1174; uint8_t x_1175; 
x_1174 = l_Lean_MetavarContext_exprDependsOn(x_1107, x_1120, x_2);
x_1175 = lean_unbox(x_1174);
lean_dec(x_1174);
if (x_1175 == 0)
{
x_1123 = x_1121;
goto block_1173;
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; uint8_t x_1183; 
lean_dec(x_1117);
lean_dec(x_1101);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1176 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1176, 0, x_3);
x_1177 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_1178 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1178, 0, x_1177);
lean_ctor_set(x_1178, 1, x_1176);
x_1179 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_1180 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1180, 0, x_1178);
lean_ctor_set(x_1180, 1, x_1179);
x_1181 = lean_box(0);
x_1182 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_1180, x_1181, x_12, x_13, x_14, x_15, x_1121);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_1183 = !lean_is_exclusive(x_1182);
if (x_1183 == 0)
{
return x_1182;
}
else
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1184 = lean_ctor_get(x_1182, 0);
x_1185 = lean_ctor_get(x_1182, 1);
lean_inc(x_1185);
lean_inc(x_1184);
lean_dec(x_1182);
x_1186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1186, 0, x_1184);
lean_ctor_set(x_1186, 1, x_1185);
return x_1186;
}
}
}
else
{
lean_dec(x_1120);
lean_dec(x_1107);
x_1123 = x_1121;
goto block_1173;
}
block_1173:
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; uint8_t x_1128; lean_object* x_1129; 
lean_inc(x_1117);
x_1124 = x_1117;
x_1125 = l_Array_umapMAux___main___at_Lean_Meta_introNCore___spec__4(x_1113, x_1124);
x_1126 = x_1125;
x_1127 = lean_array_push(x_1126, x_2);
x_1128 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_1129 = l_Lean_Meta_revert(x_1, x_1127, x_1128, x_12, x_13, x_14, x_15, x_1123);
if (lean_obj_tag(x_1129) == 0)
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; 
x_1130 = lean_ctor_get(x_1129, 0);
lean_inc(x_1130);
x_1131 = lean_ctor_get(x_1129, 1);
lean_inc(x_1131);
lean_dec(x_1129);
x_1132 = lean_ctor_get(x_1130, 0);
lean_inc(x_1132);
x_1133 = lean_ctor_get(x_1130, 1);
lean_inc(x_1133);
lean_dec(x_1130);
x_1134 = lean_array_get_size(x_1117);
x_1135 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_1136 = l_Lean_Meta_introNCore(x_1133, x_1134, x_1135, x_1128, x_12, x_13, x_14, x_15, x_1131);
if (lean_obj_tag(x_1136) == 0)
{
lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; 
x_1137 = lean_ctor_get(x_1136, 0);
lean_inc(x_1137);
x_1138 = lean_ctor_get(x_1136, 1);
lean_inc(x_1138);
lean_dec(x_1136);
x_1139 = lean_ctor_get(x_1137, 0);
lean_inc(x_1139);
x_1140 = lean_ctor_get(x_1137, 1);
lean_inc(x_1140);
lean_dec(x_1137);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_1141 = l_Lean_Meta_intro1Core(x_1140, x_1128, x_12, x_13, x_14, x_15, x_1138);
if (lean_obj_tag(x_1141) == 0)
{
lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; 
x_1142 = lean_ctor_get(x_1141, 0);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_1141, 1);
lean_inc(x_1143);
lean_dec(x_1141);
x_1144 = lean_ctor_get(x_1142, 0);
lean_inc(x_1144);
x_1145 = lean_ctor_get(x_1142, 1);
lean_inc(x_1145);
lean_dec(x_1142);
x_1146 = lean_box(0);
x_1147 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1117, x_1139, x_1117, x_1113, x_1146);
lean_dec(x_1117);
lean_inc(x_1145);
x_1148 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_1148, 0, x_1145);
x_1149 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1150 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_1149, x_1148, x_12, x_13, x_14, x_15, x_1143);
x_1151 = lean_ctor_get(x_1150, 1);
lean_inc(x_1151);
lean_dec(x_1150);
x_1152 = x_1139;
x_1153 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1113, x_1152);
x_1154 = x_1153;
lean_inc(x_1144);
x_1155 = l_Lean_mkFVar(x_1144);
lean_inc(x_1145);
x_1156 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1156, 0, x_1145);
x_1157 = lean_box(x_1122);
lean_inc(x_1145);
x_1158 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_1158, 0, x_1144);
lean_closure_set(x_1158, 1, x_7);
lean_closure_set(x_1158, 2, x_1145);
lean_closure_set(x_1158, 3, x_3);
lean_closure_set(x_1158, 4, x_4);
lean_closure_set(x_1158, 5, x_5);
lean_closure_set(x_1158, 6, x_6);
lean_closure_set(x_1158, 7, x_1101);
lean_closure_set(x_1158, 8, x_1157);
lean_closure_set(x_1158, 9, x_1132);
lean_closure_set(x_1158, 10, x_1147);
lean_closure_set(x_1158, 11, x_1154);
lean_closure_set(x_1158, 12, x_1155);
x_1159 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1159, 0, x_1156);
lean_closure_set(x_1159, 1, x_1158);
x_1160 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1145, x_1159, x_12, x_13, x_14, x_15, x_1151);
return x_1160;
}
else
{
uint8_t x_1161; 
lean_dec(x_1139);
lean_dec(x_1132);
lean_dec(x_1117);
lean_dec(x_1101);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1161 = !lean_is_exclusive(x_1141);
if (x_1161 == 0)
{
return x_1141;
}
else
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
x_1162 = lean_ctor_get(x_1141, 0);
x_1163 = lean_ctor_get(x_1141, 1);
lean_inc(x_1163);
lean_inc(x_1162);
lean_dec(x_1141);
x_1164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1164, 0, x_1162);
lean_ctor_set(x_1164, 1, x_1163);
return x_1164;
}
}
}
else
{
uint8_t x_1165; 
lean_dec(x_1132);
lean_dec(x_1117);
lean_dec(x_1101);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1165 = !lean_is_exclusive(x_1136);
if (x_1165 == 0)
{
return x_1136;
}
else
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; 
x_1166 = lean_ctor_get(x_1136, 0);
x_1167 = lean_ctor_get(x_1136, 1);
lean_inc(x_1167);
lean_inc(x_1166);
lean_dec(x_1136);
x_1168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1168, 0, x_1166);
lean_ctor_set(x_1168, 1, x_1167);
return x_1168;
}
}
}
else
{
uint8_t x_1169; 
lean_dec(x_1117);
lean_dec(x_1101);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1169 = !lean_is_exclusive(x_1129);
if (x_1169 == 0)
{
return x_1129;
}
else
{
lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
x_1170 = lean_ctor_get(x_1129, 0);
x_1171 = lean_ctor_get(x_1129, 1);
lean_inc(x_1171);
lean_inc(x_1170);
lean_dec(x_1129);
x_1172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1172, 0, x_1170);
lean_ctor_set(x_1172, 1, x_1171);
return x_1172;
}
}
}
}
else
{
uint8_t x_1187; 
lean_dec(x_1117);
lean_dec(x_1107);
lean_dec(x_1101);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1187 = !lean_is_exclusive(x_1119);
if (x_1187 == 0)
{
return x_1119;
}
else
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; 
x_1188 = lean_ctor_get(x_1119, 0);
x_1189 = lean_ctor_get(x_1119, 1);
lean_inc(x_1189);
lean_inc(x_1188);
lean_dec(x_1119);
x_1190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1190, 0, x_1188);
lean_ctor_set(x_1190, 1, x_1189);
return x_1190;
}
}
}
else
{
uint8_t x_1191; 
lean_dec(x_1107);
lean_dec(x_1101);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1191 = !lean_is_exclusive(x_1116);
if (x_1191 == 0)
{
return x_1116;
}
else
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; 
x_1192 = lean_ctor_get(x_1116, 0);
x_1193 = lean_ctor_get(x_1116, 1);
lean_inc(x_1193);
lean_inc(x_1192);
lean_dec(x_1116);
x_1194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1194, 0, x_1192);
lean_ctor_set(x_1194, 1, x_1193);
return x_1194;
}
}
}
else
{
uint8_t x_1195; 
lean_dec(x_1101);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1195 = !lean_is_exclusive(x_1102);
if (x_1195 == 0)
{
return x_1102;
}
else
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; 
x_1196 = lean_ctor_get(x_1102, 0);
x_1197 = lean_ctor_get(x_1102, 1);
lean_inc(x_1197);
lean_inc(x_1196);
lean_dec(x_1102);
x_1198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1198, 0, x_1196);
lean_ctor_set(x_1198, 1, x_1197);
return x_1198;
}
}
}
}
}
}
lean_object* l_Lean_Meta_induction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_7);
lean_inc(x_1);
x_12 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_16 = l_Lean_Meta_mkRecursorInfo(x_2, x_15, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_LocalDecl_type(x_13);
lean_dec(x_13);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_19);
x_21 = l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(x_19, x_20, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_3, x_19, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_19);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Expr_getAppNumArgsAux___main(x_26, x_27);
x_29 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_28);
x_30 = lean_mk_array(x_28, x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_sub(x_28, x_31);
lean_dec(x_28);
lean_inc(x_26);
x_33 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12(x_3, x_1, x_2, x_4, x_5, x_17, x_20, x_26, x_26, x_30, x_32, x_7, x_8, x_9, x_10, x_25);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_12);
if (x_42 == 0)
{
return x_12;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_12, 0);
x_44 = lean_ctor_get(x_12, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_12);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l_Lean_Meta_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_induction___lambda__1___boxed), 11, 5);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_11);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_14, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at_Lean_Meta_induction___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_List_elem___main___at_Lean_Meta_induction___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___main___at_Lean_Meta_induction___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_16;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
return x_14;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_foldlM___main___at_Lean_Meta_induction___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_unbox(x_6);
lean_dec(x_6);
x_23 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11(x_1, x_2, x_3, x_4, x_5, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_23;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_9);
lean_dec(x_9);
x_21 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_21;
}
}
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_induction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l_Lean_Meta_induction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_induction(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_RecursorInfo(lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Revert(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Induction(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_RecursorInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FVarSubst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8);
l_Lean_Meta_InductionSubgoal_inhabited___closed__1 = _init_l_Lean_Meta_InductionSubgoal_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_InductionSubgoal_inhabited___closed__1);
l_Lean_Meta_InductionSubgoal_inhabited = _init_l_Lean_Meta_InductionSubgoal_inhabited();
lean_mark_persistent(l_Lean_Meta_InductionSubgoal_inhabited);
l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1);
l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2);
l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3 = _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3);
l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1 = _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1();
lean_mark_persistent(l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1);
l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2 = _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2();
lean_mark_persistent(l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2);
l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3 = _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3();
lean_mark_persistent(l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__9 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__9();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__9);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__1 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__1);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__2 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__2);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__3 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__3);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__4 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__4);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__2 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__2);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__3 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__3);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4);
res = l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
