// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural
// Imports: Init Lean.Util.ForEachExpr Lean.Meta.ForEachExpr Lean.Meta.RecursorInfo Lean.Meta.Match.Match Lean.Meta.Transform Lean.Meta.IndPredBelow Lean.Elab.PreDefinition.Basic
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
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__10(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_shouldBetaReduce___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__6(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop_match__2(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__7___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__5;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___closed__1;
lean_object* l_Lean_Elab_addAsAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__1___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2___boxed__const__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow_match__3___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__4;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__3;
uint8_t l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_containsRecFn___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__4;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__7;
lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__5___boxed(lean_object**);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__3;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isInductivePredicate___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__16;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__11___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_recArgHasLooseBVarsAt___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_structuralRecursion___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___closed__2;
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__3;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_dependsOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5___closed__2;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop_match__1(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__5(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_containsRecFn___boxed(lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__3(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getElimInfo___spec__8(lean_object*, size_t, size_t);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__15;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2___closed__1;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Structural_instInhabitedM___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_containsRecFn___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__14;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__5;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop_match__1(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2___closed__2;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__11;
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_structuralRecursion_match__1___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__6;
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__13___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__9___closed__2;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__3;
extern lean_object* l_Lean_binductionOnSuffix;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__10;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__2;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_recArgHasLooseBVarsAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___closed__2;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix_match__2(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27___rarg___closed__1;
lean_object* l_Lean_mkMData(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict(lean_object*);
extern lean_object* l_Lean_Meta_smartUnfoldingSuffix;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow_match__2___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg(lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__11(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__12;
lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelow___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Structural_instInhabitedM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__13(lean_object*);
lean_object* l_Lean_Meta_forEachExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__2;
static lean_object* l_Lean_Elab_Structural_instInhabitedM___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__5;
lean_object* l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_225____spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___closed__1;
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__4(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__4;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_structuralRecursion___lambda__1(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_run(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__4___boxed__const__1;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__7;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__3;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__10;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__2;
lean_object* l_Lean_Meta_decLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1;
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_State_matcherBelowDep___default;
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___spec__1(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_structuralRecursion___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__1;
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__7(lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Structural_instInhabitedM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos_match__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__3;
uint8_t l_Lean_isInductivePredicate_visit(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_structuralRecursion___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__4;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_recArgHasLooseBVarsAt___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop_match__3(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg___closed__1;
lean_object* l_Lean_Meta_mapErrorImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__4;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__9;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__9;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3___boxed(lean_object**);
lean_object* l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__17;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow_match__1(lean_object*);
static lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_recArgHasLooseBVarsAt___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__1;
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__8;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3___closed__1;
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__14(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2;
lean_object* l_Lean_Elab_Structural_structuralRecursion_match__1(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__4;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__8;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_FindImpl_initCache;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix_match__1(lean_object*);
uint8_t l_Array_contains___at_Lean_Meta_addImplicitTargets_collect___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__3(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchMatcherApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___spec__1(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__4;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2___closed__1;
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__4___boxed(lean_object**);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__1(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__6;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__1;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1(lean_object*);
lean_object* l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*);
lean_object* l_Lean_Elab_Structural_State_addMatchers___default;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__4;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__3___boxed(lean_object**);
static lean_object* l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__3;
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_match__1(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__5___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__9___closed__1;
lean_object* l_Lean_Meta_mkIdRhs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__11;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__5___closed__2;
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow_match__2(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__5;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f_match__1(lean_object*);
lean_object* l_Lean_Elab_Structural_initFn____x40_Lean_Elab_PreDefinition_Structural___hyg_7232_(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__2___closed__2;
lean_object* l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_structuralRecursion___closed__4;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__4;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__4___boxed__const__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1;
static lean_object* l_Lean_Elab_Structural_structuralRecursion___closed__2;
lean_object* l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow_match__3(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__6___boxed__const__1;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__3;
uint8_t l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_shouldBetaReduce(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__2___boxed__const__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_forEachExpr_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__3___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_structuralRecursion___closed__1;
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop_match__2(lean_object*);
lean_object* l_Lean_isInductivePredicate___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__1;
lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__6;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object*, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg___closed__2;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6___boxed(lean_object**);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8___boxed__const__1;
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__8;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_containsRecFn(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_brecOnSuffix;
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__4;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__1;
lean_object* l_IO_mkRef___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__10;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__13___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__14___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__9;
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___boxed__const__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_Meta_getElimInfo___spec__5(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__2;
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__2;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__2;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos_match__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__1;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___closed__1;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___boxed__const__1;
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___closed__2;
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__4;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___boxed__const__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7___closed__2;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__7;
lean_object* l_Lean_Elab_Structural_instInhabitedM(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__1;
static lean_object* l_Lean_Elab_Structural_State_addMatchers___default___closed__1;
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__13;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__9(lean_object*);
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_4 < x_3;
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_23 = lean_ctor_get(x_15, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_array_fget(x_17, x_18);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_18, x_27);
lean_dec(x_18);
lean_ctor_set(x_15, 1, x_28);
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_6, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_6, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_6, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_6, 4);
lean_inc(x_33);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_35 = 2;
x_36 = 0;
lean_ctor_set_uint8(x_29, 5, x_35);
lean_ctor_set_uint8(x_29, 9, x_36);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_33);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_38 = l_Lean_Meta_isExprDefEq(x_13, x_26, x_37, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_dec(x_42);
x_43 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_43);
lean_ctor_set(x_38, 0, x_5);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_5);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; size_t x_48; size_t x_49; 
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_dec(x_38);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
x_48 = 1;
x_49 = x_4 + x_48;
x_4 = x_49;
x_10 = x_47;
goto _start;
}
}
else
{
uint8_t x_51; 
lean_dec(x_15);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
return x_38;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_38, 0);
x_53 = lean_ctor_get(x_38, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_38);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_55 = lean_ctor_get_uint8(x_29, 0);
x_56 = lean_ctor_get_uint8(x_29, 1);
x_57 = lean_ctor_get_uint8(x_29, 2);
x_58 = lean_ctor_get_uint8(x_29, 3);
x_59 = lean_ctor_get_uint8(x_29, 4);
x_60 = lean_ctor_get_uint8(x_29, 6);
x_61 = lean_ctor_get_uint8(x_29, 7);
x_62 = lean_ctor_get_uint8(x_29, 8);
x_63 = lean_ctor_get_uint8(x_29, 10);
lean_dec(x_29);
x_64 = 2;
x_65 = 0;
x_66 = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(x_66, 0, x_55);
lean_ctor_set_uint8(x_66, 1, x_56);
lean_ctor_set_uint8(x_66, 2, x_57);
lean_ctor_set_uint8(x_66, 3, x_58);
lean_ctor_set_uint8(x_66, 4, x_59);
lean_ctor_set_uint8(x_66, 5, x_64);
lean_ctor_set_uint8(x_66, 6, x_60);
lean_ctor_set_uint8(x_66, 7, x_61);
lean_ctor_set_uint8(x_66, 8, x_62);
lean_ctor_set_uint8(x_66, 9, x_65);
lean_ctor_set_uint8(x_66, 10, x_63);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_30);
lean_ctor_set(x_67, 2, x_31);
lean_ctor_set(x_67, 3, x_32);
lean_ctor_set(x_67, 4, x_33);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_68 = l_Lean_Meta_isExprDefEq(x_13, x_26, x_67, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_72 = x_68;
} else {
 lean_dec_ref(x_68);
 x_72 = lean_box(0);
}
x_73 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_73);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_5);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
lean_object* x_75; size_t x_76; size_t x_77; 
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_dec(x_68);
lean_inc(x_1);
lean_ctor_set(x_5, 0, x_1);
x_76 = 1;
x_77 = x_4 + x_76;
x_4 = x_77;
x_10 = x_75;
goto _start;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_15);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_79 = lean_ctor_get(x_68, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_68, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_81 = x_68;
} else {
 lean_dec_ref(x_68);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; lean_object* x_101; uint8_t x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_15);
x_83 = lean_array_fget(x_17, x_18);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_add(x_18, x_84);
lean_dec(x_18);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_17);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_19);
x_87 = lean_ctor_get(x_6, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_6, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_6, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_6, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_6, 4);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_87, 0);
x_93 = lean_ctor_get_uint8(x_87, 1);
x_94 = lean_ctor_get_uint8(x_87, 2);
x_95 = lean_ctor_get_uint8(x_87, 3);
x_96 = lean_ctor_get_uint8(x_87, 4);
x_97 = lean_ctor_get_uint8(x_87, 6);
x_98 = lean_ctor_get_uint8(x_87, 7);
x_99 = lean_ctor_get_uint8(x_87, 8);
x_100 = lean_ctor_get_uint8(x_87, 10);
if (lean_is_exclusive(x_87)) {
 x_101 = x_87;
} else {
 lean_dec_ref(x_87);
 x_101 = lean_box(0);
}
x_102 = 2;
x_103 = 0;
if (lean_is_scalar(x_101)) {
 x_104 = lean_alloc_ctor(0, 0, 11);
} else {
 x_104 = x_101;
}
lean_ctor_set_uint8(x_104, 0, x_92);
lean_ctor_set_uint8(x_104, 1, x_93);
lean_ctor_set_uint8(x_104, 2, x_94);
lean_ctor_set_uint8(x_104, 3, x_95);
lean_ctor_set_uint8(x_104, 4, x_96);
lean_ctor_set_uint8(x_104, 5, x_102);
lean_ctor_set_uint8(x_104, 6, x_97);
lean_ctor_set_uint8(x_104, 7, x_98);
lean_ctor_set_uint8(x_104, 8, x_99);
lean_ctor_set_uint8(x_104, 9, x_103);
lean_ctor_set_uint8(x_104, 10, x_100);
x_105 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_88);
lean_ctor_set(x_105, 2, x_89);
lean_ctor_set(x_105, 3, x_90);
lean_ctor_set(x_105, 4, x_91);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_106 = l_Lean_Meta_isExprDefEq(x_13, x_83, x_105, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_110 = x_106;
} else {
 lean_dec_ref(x_106);
 x_110 = lean_box(0);
}
x_111 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1;
lean_ctor_set(x_5, 1, x_86);
lean_ctor_set(x_5, 0, x_111);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_5);
lean_ctor_set(x_112, 1, x_109);
return x_112;
}
else
{
lean_object* x_113; size_t x_114; size_t x_115; 
x_113 = lean_ctor_get(x_106, 1);
lean_inc(x_113);
lean_dec(x_106);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_86);
lean_ctor_set(x_5, 0, x_1);
x_114 = 1;
x_115 = x_4 + x_114;
x_4 = x_115;
x_10 = x_113;
goto _start;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_86);
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_117 = lean_ctor_get(x_106, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_106, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_119 = x_106;
} else {
 lean_dec_ref(x_106);
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
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_121 = lean_ctor_get(x_5, 1);
lean_inc(x_121);
lean_dec(x_5);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 2);
lean_inc(x_124);
x_125 = lean_nat_dec_lt(x_123, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_1);
lean_ctor_set(x_126, 1, x_121);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_10);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 x_128 = x_121;
} else {
 lean_dec_ref(x_121);
 x_128 = lean_box(0);
}
x_129 = lean_array_fget(x_122, x_123);
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_nat_add(x_123, x_130);
lean_dec(x_123);
if (lean_is_scalar(x_128)) {
 x_132 = lean_alloc_ctor(0, 3, 0);
} else {
 x_132 = x_128;
}
lean_ctor_set(x_132, 0, x_122);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_132, 2, x_124);
x_133 = lean_ctor_get(x_6, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_6, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_6, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_6, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_6, 4);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_133, 0);
x_139 = lean_ctor_get_uint8(x_133, 1);
x_140 = lean_ctor_get_uint8(x_133, 2);
x_141 = lean_ctor_get_uint8(x_133, 3);
x_142 = lean_ctor_get_uint8(x_133, 4);
x_143 = lean_ctor_get_uint8(x_133, 6);
x_144 = lean_ctor_get_uint8(x_133, 7);
x_145 = lean_ctor_get_uint8(x_133, 8);
x_146 = lean_ctor_get_uint8(x_133, 10);
if (lean_is_exclusive(x_133)) {
 x_147 = x_133;
} else {
 lean_dec_ref(x_133);
 x_147 = lean_box(0);
}
x_148 = 2;
x_149 = 0;
if (lean_is_scalar(x_147)) {
 x_150 = lean_alloc_ctor(0, 0, 11);
} else {
 x_150 = x_147;
}
lean_ctor_set_uint8(x_150, 0, x_138);
lean_ctor_set_uint8(x_150, 1, x_139);
lean_ctor_set_uint8(x_150, 2, x_140);
lean_ctor_set_uint8(x_150, 3, x_141);
lean_ctor_set_uint8(x_150, 4, x_142);
lean_ctor_set_uint8(x_150, 5, x_148);
lean_ctor_set_uint8(x_150, 6, x_143);
lean_ctor_set_uint8(x_150, 7, x_144);
lean_ctor_set_uint8(x_150, 8, x_145);
lean_ctor_set_uint8(x_150, 9, x_149);
lean_ctor_set_uint8(x_150, 10, x_146);
x_151 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_134);
lean_ctor_set(x_151, 2, x_135);
lean_ctor_set(x_151, 3, x_136);
lean_ctor_set(x_151, 4, x_137);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_152 = l_Lean_Meta_isExprDefEq(x_13, x_129, x_151, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_unbox(x_153);
lean_dec(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_156 = x_152;
} else {
 lean_dec_ref(x_152);
 x_156 = lean_box(0);
}
x_157 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1;
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_132);
if (lean_is_scalar(x_156)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_156;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_155);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; size_t x_162; size_t x_163; 
x_160 = lean_ctor_get(x_152, 1);
lean_inc(x_160);
lean_dec(x_152);
lean_inc(x_1);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_1);
lean_ctor_set(x_161, 1, x_132);
x_162 = 1;
x_163 = x_4 + x_162;
x_4 = x_163;
x_5 = x_161;
x_10 = x_160;
goto _start;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_132);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_165 = lean_ctor_get(x_152, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_152, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_167 = x_152;
} else {
 lean_dec_ref(x_152);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isAppOf(x_5, x_1);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Expr_getAppNumArgsAux(x_5, x_15);
x_17 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1;
lean_inc(x_16);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_16, x_19);
lean_dec(x_16);
x_21 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_5, x_18, x_20);
x_47 = lean_st_ref_get(x_9, x_10);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_st_ref_take(x_4, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_array_get_size(x_21);
x_53 = lean_nat_dec_lt(x_52, x_50);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_52);
x_54 = lean_st_ref_set(x_4, x_50, x_51);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_22 = x_55;
goto block_46;
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_50);
x_56 = lean_st_ref_set(x_4, x_52, x_51);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_22 = x_57;
goto block_46;
}
block_46:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_23 = l_Array_toSubarray___rarg(x_2, x_15, x_3);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_array_get_size(x_21);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___spec__1(x_24, x_21, x_27, x_28, x_25, x_6, x_7, x_8, x_9, x_22);
lean_dec(x_21);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__2;
x_34 = lean_box(0);
x_35 = lean_apply_6(x_33, x_34, x_6, x_7, x_8, x_9, x_32);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_29, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_38);
return x_29;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_dec(x_29);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
return x_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_29, 0);
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_29);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_st_ref_get(x_7, x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_9);
x_12 = l_IO_mkRef___rarg(x_9, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___boxed), 10, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_9);
lean_closure_set(x_15, 3, x_13);
lean_inc(x_7);
x_16 = l_Lean_Meta_forEachExpr_x27(x_3, x_15, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_7, x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_13, x_19);
lean_dec(x_13);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_7);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos_match__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 < x_3;
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_uget(x_2, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_7, x_8);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = x_4 + x_10;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_nat_dec_lt(x_13, x_5);
if (x_14 == 0)
{
size_t x_15; size_t x_16; 
lean_dec(x_13);
x_15 = 1;
x_16 = x_4 + x_15;
x_4 = x_16;
goto _start;
}
else
{
size_t x_18; size_t x_19; 
lean_dec(x_5);
x_18 = 1;
x_19 = x_4 + x_18;
x_4 = x_19;
x_5 = x_13;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_array_get_size(x_2);
x_5 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_6 = 0;
x_7 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos___spec__1(x_1, x_2, x_5, x_6, x_3);
return x_7;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_7 < x_6;
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_8);
x_16 = lean_array_uget(x_5, x_7);
x_17 = l_Lean_Expr_fvarId_x21(x_16);
lean_inc(x_4);
x_18 = l_Lean_Meta_dependsOn(x_4, x_17, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = l_Array_contains___at_Lean_Meta_getElimInfo___spec__5(x_1, x_16);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = lean_unbox(x_20);
lean_dec(x_20);
if (x_23 == 0)
{
size_t x_24; size_t x_25; 
lean_free_object(x_18);
lean_dec(x_16);
x_24 = 1;
x_25 = x_7 + x_24;
lean_inc(x_2);
{
size_t _tmp_6 = x_25;
lean_object* _tmp_7 = x_2;
lean_object* _tmp_12 = x_21;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_13 = _tmp_12;
}
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_16);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_18, 0, x_31);
return x_18;
}
}
else
{
size_t x_32; size_t x_33; 
lean_free_object(x_18);
lean_dec(x_20);
lean_dec(x_16);
x_32 = 1;
x_33 = x_7 + x_32;
lean_inc(x_2);
{
size_t _tmp_6 = x_33;
lean_object* _tmp_7 = x_2;
lean_object* _tmp_12 = x_21;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_13 = _tmp_12;
}
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_18, 0);
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_18);
x_37 = l_Array_contains___at_Lean_Meta_getElimInfo___spec__5(x_1, x_16);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = lean_unbox(x_35);
lean_dec(x_35);
if (x_38 == 0)
{
size_t x_39; size_t x_40; 
lean_dec(x_16);
x_39 = 1;
x_40 = x_7 + x_39;
lean_inc(x_2);
{
size_t _tmp_6 = x_40;
lean_object* _tmp_7 = x_2;
lean_object* _tmp_12 = x_36;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_13 = _tmp_12;
}
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_4);
lean_dec(x_2);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_16);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_36);
return x_47;
}
}
else
{
size_t x_48; size_t x_49; 
lean_dec(x_35);
lean_dec(x_16);
x_48 = 1;
x_49 = x_7 + x_48;
lean_inc(x_2);
{
size_t _tmp_6 = x_49;
lean_object* _tmp_7 = x_2;
lean_object* _tmp_12 = x_36;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_13 = _tmp_12;
}
goto _start;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_6 < x_5;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_15 = lean_array_uget(x_4, x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_15);
x_16 = lean_infer_type(x_15, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_get_size(x_1);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 0;
lean_inc_n(x_3, 2);
x_22 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___spec__1(x_2, x_3, x_15, x_17, x_1, x_20, x_21, x_3, x_8, x_9, x_10, x_11, x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; size_t x_26; size_t x_27; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = 1;
x_27 = x_6 + x_26;
lean_inc(x_3);
{
size_t _tmp_5 = x_27;
lean_object* _tmp_6 = x_3;
lean_object* _tmp_11 = x_25;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_12 = _tmp_11;
}
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_22, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_22, 0, x_33);
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_22, 0, x_37);
return x_22;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_ctor_get(x_24, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_40 = x_24;
} else {
 lean_dec_ref(x_24);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_16);
if (x_45 == 0)
{
return x_16;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_16, 0);
x_47 = lean_ctor_get(x_16, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_16);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_box(0);
x_9 = lean_array_get_size(x_2);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___closed__1;
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___spec__2(x_1, x_2, x_12, x_2, x_10, x_11, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_8);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___spec__2(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_6 < x_5;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_7);
x_15 = lean_array_uget(x_4, x_6);
x_16 = l_Lean_Expr_fvarId_x21(x_15);
lean_inc(x_3);
x_17 = l_Lean_Meta_dependsOn(x_3, x_16, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; size_t x_21; size_t x_22; 
lean_dec(x_15);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = 1;
x_22 = x_6 + x_21;
lean_inc(x_1);
{
size_t _tmp_5 = x_22;
lean_object* _tmp_6 = x_1;
lean_object* _tmp_11 = x_20;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_12 = _tmp_11;
}
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_15);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_17, 0, x_30);
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_dec(x_17);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_15);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_5 < x_4;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_14);
x_15 = lean_infer_type(x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_get_size(x_1);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
lean_inc_n(x_2, 2);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f___spec__1(x_2, x_14, x_16, x_1, x_19, x_20, x_2, x_7, x_8, x_9, x_10, x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = x_5 + x_25;
lean_inc(x_2);
{
size_t _tmp_4 = x_26;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_10 = x_24;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_11 = _tmp_10;
}
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_21, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_21, 0, x_36);
return x_21;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_ctor_get(x_23, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_39 = x_23;
} else {
 lean_dec_ref(x_23);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_15);
if (x_44 == 0)
{
return x_15;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_15, 0);
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_15);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_box(0);
x_9 = lean_array_get_size(x_2);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___closed__1;
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f___spec__2(x_1, x_12, x_2, x_10, x_11, x_12, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_8);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f___spec__1(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
return x_15;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f___spec__2(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structural recursion cannot be used");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg___closed__2;
x_7 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___spec__1___rarg(x_6, x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Structural_State_matcherBelowDep___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_State_addMatchers___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_State_addMatchers___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Structural_State_addMatchers___default___closed__1;
return x_1;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Structural_instInhabitedM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Structural_instInhabitedM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Structural_instInhabitedM___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Structural_instInhabitedM___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Structural_instInhabitedM___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Structural_instInhabitedM___spec__1___rarg___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Structural_instInhabitedM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Structural_instInhabitedM___closed__3;
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Structural_instInhabitedM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at_Lean_Elab_Structural_instInhabitedM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_mk_ref(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_11);
x_13 = lean_apply_6(x_1, x_11, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_6, x_15);
lean_dec(x_6);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_11, x_17);
lean_dec(x_11);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_run___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_24 = lean_st_ref_get(x_7, x_13);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_7, x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_get(x_5, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_34 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = x_34;
goto block_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_27, x_4, x_5, x_6, x_7, x_36);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Meta_setMCtx(x_33, x_4, x_5, x_6, x_7, x_38);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_st_ref_get(x_7, x_40);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_st_ref_set(x_3, x_12, x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_dec(x_42);
lean_dec(x_41);
x_14 = x_47;
goto block_23;
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_48, 1);
x_53 = lean_ctor_get(x_48, 0);
lean_dec(x_53);
x_54 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27___rarg___closed__1;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_42);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
lean_ctor_set(x_48, 1, x_57);
lean_ctor_set(x_48, 0, x_41);
x_14 = x_47;
goto block_23;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_dec(x_48);
x_59 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27___rarg___closed__1;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_42);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_41);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_47, 0, x_63);
x_14 = x_47;
goto block_23;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_47, 1);
lean_inc(x_64);
lean_dec(x_47);
x_65 = lean_ctor_get(x_48, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_66 = x_48;
} else {
 lean_dec_ref(x_48);
 x_66 = lean_box(0);
}
x_67 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27___rarg___closed__1;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_42);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
if (lean_is_scalar(x_66)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_66;
}
lean_ctor_set(x_71, 0, x_41);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_64);
x_14 = x_72;
goto block_23;
}
}
else
{
uint8_t x_73; 
lean_dec(x_42);
lean_dec(x_41);
x_73 = !lean_is_exclusive(x_47);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_47, 0);
lean_dec(x_74);
x_14 = x_47;
goto block_23;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_47, 1);
lean_inc(x_75);
lean_dec(x_47);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_48);
lean_ctor_set(x_76, 1, x_75);
x_14 = x_76;
goto block_23;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_39);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_39, 0);
lean_dec(x_78);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_35);
x_14 = x_39;
goto block_23;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_39, 1);
lean_inc(x_79);
lean_dec(x_39);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_35);
lean_ctor_set(x_80, 1, x_79);
x_14 = x_80;
goto block_23;
}
}
}
block_23:
{
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop_match__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Environment_contains(x_11, x_1);
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Environment_contains(x_16, x_1);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.PreDefinition.Structural");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.PreDefinition.Structural.0.Lean.Elab.Structural.findRecArg.loop");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__1;
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__2;
x_3 = lean_unsigned_to_nat(174u);
x_4 = lean_unsigned_to_nat(119u);
x_5 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_10, x_8);
lean_dec(x_10);
x_12 = 1;
x_13 = x_3 + x_12;
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_instInhabitedNat;
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__4;
x_16 = lean_panic_fn(x_14, x_15);
x_17 = x_16;
x_18 = lean_array_uset(x_9, x_3, x_17);
x_3 = x_13;
x_4 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = x_20;
x_22 = lean_array_uset(x_9, x_3, x_21);
x_3 = x_13;
x_4 = x_22;
goto _start;
}
}
}
}
lean_object* l_Lean_isInductivePredicate___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_environment_find(x_11, x_1);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
x_14 = lean_box(x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 5)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_isInductivePredicate_visit(x_18);
lean_dec(x_18);
x_20 = lean_box(x_19);
lean_ctor_set(x_8, 0, x_20);
return x_8;
}
else
{
uint8_t x_21; lean_object* x_22; 
lean_dec(x_15);
x_21 = 0;
x_22 = lean_box(x_21);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_environment_find(x_25, x_1);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
if (lean_obj_tag(x_30) == 5)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_isInductivePredicate_visit(x_33);
lean_dec(x_33);
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
return x_36;
}
else
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_30);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_24);
return x_39;
}
}
}
}
}
lean_object* l_ReaderT_bind___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_7(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_ReaderT_bind___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__4___rarg), 8, 0);
return x_3;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__5___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__6___rarg___boxed), 7, 0);
return x_2;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget(x_1, x_8);
x_10 = lean_expr_eqv(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = 0;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = 1;
return x_13;
}
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_2);
lean_inc(x_2);
x_7 = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__8(x_1, x_6, x_2, lean_box(0));
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_2 = x_10;
goto _start;
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__9___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__10___rarg___boxed), 7, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("argument #");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" was not used for structural recursion");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_1, x_3);
x_5 = l_Nat_repr(x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__2;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__4;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_indentD(x_2);
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_2(x_1, x_2, x_4);
x_11 = l_Lean_Meta_mapErrorImp___rarg(x_10, x_3, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" was not used because its type is an inductive datatype");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nand parameter");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\ndepends on");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" was not used because its type is an inductive family");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nand index");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\ndepends on the non index");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" was not used because its type is an inductive family and indices are not pairwise distinct");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" was not used because its type is an inductive family and indices are not variables");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__16;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg(x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_inc(x_6);
x_15 = l_Lean_Meta_getFVarLocalDecl(x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_LocalDecl_isLet(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_LocalDecl_type(x_16);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Meta_whnfD(x_19, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_getAppFn(x_21);
if (lean_obj_tag(x_23) == 4)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_9, x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_environment_find(x_29, x_24);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_11);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_4, x_31);
lean_dec(x_4);
x_4 = x_32;
x_10 = x_28;
goto _start;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
if (lean_obj_tag(x_34) == 5)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_brecOnSuffix;
lean_inc(x_37);
x_39 = lean_name_mk_string(x_37, x_38);
x_40 = l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__1(x_39, x_5, x_6, x_7, x_8, x_9, x_28);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_11);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_4, x_44);
lean_dec(x_4);
x_4 = x_45;
x_10 = x_43;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_dec(x_40);
x_48 = l_Lean_binductionOnSuffix;
lean_inc(x_37);
x_49 = lean_name_mk_string(x_37, x_48);
x_50 = l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__1(x_49, x_5, x_6, x_7, x_8, x_9, x_47);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get_uint8(x_35, sizeof(void*)*5 + 2);
if (x_53 == 0)
{
lean_object* x_203; 
lean_dec(x_51);
x_203 = lean_box(0);
x_54 = x_203;
goto block_202;
}
else
{
uint8_t x_204; 
x_204 = lean_unbox(x_51);
lean_dec(x_51);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_11);
x_205 = lean_unsigned_to_nat(1u);
x_206 = lean_nat_add(x_4, x_205);
lean_dec(x_4);
x_4 = x_206;
x_10 = x_52;
goto _start;
}
else
{
lean_object* x_208; 
x_208 = lean_box(0);
x_54 = x_208;
goto block_202;
}
}
block_202:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_158; lean_object* x_178; uint8_t x_179; 
lean_dec(x_54);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_Expr_getAppNumArgsAux(x_21, x_55);
x_57 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1;
lean_inc(x_56);
x_58 = lean_mk_array(x_56, x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_sub(x_56, x_59);
lean_dec(x_56);
lean_inc(x_21);
x_61 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_21, x_58, x_60);
x_62 = lean_ctor_get(x_35, 1);
lean_inc(x_62);
lean_dec(x_35);
lean_inc(x_62);
lean_inc(x_61);
x_63 = l_Array_extract___rarg(x_61, x_55, x_62);
x_64 = lean_array_get_size(x_61);
x_65 = l_Array_extract___rarg(x_61, x_62, x_64);
x_178 = lean_array_get_size(x_65);
x_179 = lean_nat_dec_lt(x_55, x_178);
if (x_179 == 0)
{
lean_object* x_180; 
lean_dec(x_178);
x_180 = lean_box(0);
x_158 = x_180;
goto block_177;
}
else
{
uint8_t x_181; 
x_181 = lean_nat_dec_le(x_178, x_178);
if (x_181 == 0)
{
lean_object* x_182; 
lean_dec(x_178);
x_182 = lean_box(0);
x_158 = x_182;
goto block_177;
}
else
{
size_t x_183; size_t x_184; uint8_t x_185; 
x_183 = 0;
x_184 = lean_usize_of_nat(x_178);
lean_dec(x_178);
x_185 = l_Array_anyMUnsafe_any___at_Lean_Meta_getElimInfo___spec__8(x_65, x_183, x_184);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_box(0);
x_158 = x_186;
goto block_177;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
x_187 = lean_nat_add(x_4, x_59);
lean_dec(x_4);
lean_inc(x_187);
x_188 = l_Nat_repr(x_187);
x_189 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_191 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__2;
x_192 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
x_193 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__17;
x_194 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = l_Lean_indentExpr(x_21);
x_196 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_198 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__10___rarg___boxed), 7, 1);
lean_closure_set(x_199, 0, x_198);
x_200 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg), 10, 4);
lean_closure_set(x_200, 0, x_1);
lean_closure_set(x_200, 1, x_2);
lean_closure_set(x_200, 2, x_3);
lean_closure_set(x_200, 3, x_187);
x_201 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27___rarg(x_199, x_200, x_5, x_6, x_7, x_8, x_9, x_52);
return x_201;
}
}
}
block_157:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_inc(x_66);
lean_inc(x_2);
x_67 = l_Array_extract___rarg(x_2, x_55, x_66);
lean_inc(x_2);
x_68 = l_Array_extract___rarg(x_2, x_66, x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_69 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f(x_68, x_65, x_6, x_7, x_8, x_9, x_52);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_72 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadParamDep_x3f(x_68, x_63, x_6, x_7, x_8, x_9, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_21);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_array_get_size(x_65);
x_76 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_77 = 0;
lean_inc(x_65);
x_78 = x_65;
x_79 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2(x_68, x_76, x_77, x_78);
x_80 = x_79;
lean_inc(x_37);
x_81 = l_Lean_isInductivePredicate___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__3(x_37, x_5, x_6, x_7, x_8, x_9, x_74);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_array_get_size(x_67);
x_85 = lean_nat_sub(x_4, x_84);
lean_dec(x_84);
x_86 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_86, 0, x_67);
lean_ctor_set(x_86, 1, x_68);
lean_ctor_set(x_86, 2, x_85);
lean_ctor_set(x_86, 3, x_80);
lean_ctor_set(x_86, 4, x_37);
lean_ctor_set(x_86, 5, x_25);
lean_ctor_set(x_86, 6, x_63);
lean_ctor_set(x_86, 7, x_65);
lean_ctor_set_uint8(x_86, sizeof(void*)*8, x_53);
x_87 = lean_unbox(x_82);
lean_dec(x_82);
lean_ctor_set_uint8(x_86, sizeof(void*)*8 + 1, x_87);
lean_inc(x_4);
x_88 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_88, 0, x_4);
lean_inc(x_3);
x_89 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__2), 9, 3);
lean_closure_set(x_89, 0, x_3);
lean_closure_set(x_89, 1, x_86);
lean_closure_set(x_89, 2, x_88);
x_90 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__1;
x_91 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__4___rarg), 8, 2);
lean_closure_set(x_91, 0, x_89);
lean_closure_set(x_91, 1, x_90);
x_92 = lean_nat_add(x_4, x_59);
lean_dec(x_4);
x_93 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg), 10, 4);
lean_closure_set(x_93, 0, x_1);
lean_closure_set(x_93, 1, x_2);
lean_closure_set(x_93, 2, x_3);
lean_closure_set(x_93, 3, x_92);
x_94 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27___rarg(x_91, x_93, x_5, x_6, x_7, x_8, x_9, x_83);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_37);
lean_dec(x_25);
x_95 = lean_ctor_get(x_73, 0);
lean_inc(x_95);
lean_dec(x_73);
x_96 = lean_ctor_get(x_72, 1);
lean_inc(x_96);
lean_dec(x_72);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_nat_add(x_4, x_59);
lean_dec(x_4);
lean_inc(x_99);
x_100 = l_Nat_repr(x_99);
x_101 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__2;
x_104 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
x_105 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__3;
x_106 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_indentExpr(x_21);
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__5;
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_indentExpr(x_97);
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__7;
x_114 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_indentExpr(x_98);
x_116 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_118 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__5___rarg___boxed), 7, 1);
lean_closure_set(x_119, 0, x_118);
x_120 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg), 10, 4);
lean_closure_set(x_120, 0, x_1);
lean_closure_set(x_120, 1, x_2);
lean_closure_set(x_120, 2, x_3);
lean_closure_set(x_120, 3, x_99);
x_121 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27___rarg(x_119, x_120, x_5, x_6, x_7, x_8, x_9, x_96);
return x_121;
}
}
else
{
uint8_t x_122; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_72);
if (x_122 == 0)
{
return x_72;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_72, 0);
x_124 = lean_ctor_get(x_72, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_72);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_37);
lean_dec(x_25);
x_126 = lean_ctor_get(x_70, 0);
lean_inc(x_126);
lean_dec(x_70);
x_127 = lean_ctor_get(x_69, 1);
lean_inc(x_127);
lean_dec(x_69);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_nat_add(x_4, x_59);
lean_dec(x_4);
lean_inc(x_130);
x_131 = l_Nat_repr(x_130);
x_132 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__2;
x_135 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__9;
x_137 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_indentExpr(x_21);
x_139 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__11;
x_141 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_indentExpr(x_128);
x_143 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__13;
x_145 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_indentExpr(x_129);
x_147 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_149 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__6___rarg___boxed), 7, 1);
lean_closure_set(x_150, 0, x_149);
x_151 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg), 10, 4);
lean_closure_set(x_151, 0, x_1);
lean_closure_set(x_151, 1, x_2);
lean_closure_set(x_151, 2, x_3);
lean_closure_set(x_151, 3, x_130);
x_152 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27___rarg(x_150, x_151, x_5, x_6, x_7, x_8, x_9, x_127);
return x_152;
}
}
else
{
uint8_t x_153; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_69);
if (x_153 == 0)
{
return x_69;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_69, 0);
x_155 = lean_ctor_get(x_69, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_69);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
block_177:
{
uint8_t x_159; 
lean_dec(x_158);
x_159 = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__7(x_65, x_55);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_11);
x_160 = lean_nat_add(x_4, x_59);
lean_dec(x_4);
lean_inc(x_160);
x_161 = l_Nat_repr(x_160);
x_162 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_162, 0, x_161);
x_163 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__2;
x_165 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
x_166 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__15;
x_167 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_indentExpr(x_21);
x_169 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_171 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__9___rarg___boxed), 7, 1);
lean_closure_set(x_172, 0, x_171);
x_173 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg), 10, 4);
lean_closure_set(x_173, 0, x_1);
lean_closure_set(x_173, 1, x_2);
lean_closure_set(x_173, 2, x_3);
lean_closure_set(x_173, 3, x_160);
x_174 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27___rarg(x_172, x_173, x_5, x_6, x_7, x_8, x_9, x_52);
return x_174;
}
else
{
lean_object* x_175; uint8_t x_176; 
x_175 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getIndexMinPos(x_2, x_65);
x_176 = lean_nat_dec_lt(x_175, x_1);
if (x_176 == 0)
{
lean_dec(x_175);
lean_inc(x_1);
x_66 = x_1;
goto block_157;
}
else
{
x_66 = x_175;
goto block_157;
}
}
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_11);
x_209 = lean_unsigned_to_nat(1u);
x_210 = lean_nat_add(x_4, x_209);
lean_dec(x_4);
x_4 = x_210;
x_10 = x_28;
goto _start;
}
}
}
else
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_11);
x_212 = lean_unsigned_to_nat(1u);
x_213 = lean_nat_add(x_4, x_212);
lean_dec(x_4);
x_4 = x_213;
x_10 = x_22;
goto _start;
}
}
else
{
uint8_t x_215; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_215 = !lean_is_exclusive(x_20);
if (x_215 == 0)
{
return x_20;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_20, 0);
x_217 = lean_ctor_get(x_20, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_20);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
lean_object* x_219; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_219 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg(x_6, x_7, x_8, x_9, x_17);
return x_219;
}
}
else
{
uint8_t x_220; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_220 = !lean_is_exclusive(x_15);
if (x_220 == 0)
{
return x_15;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_15, 0);
x_222 = lean_ctor_get(x_15, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_15);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg), 10, 0);
return x_2;
}
}
lean_object* l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_hasConst___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_isInductivePredicate___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isInductivePredicate___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__7(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__9___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__10___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg(x_1, x_2, x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg___rarg), 9, 0);
return x_2;
}
}
uint8_t l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_containsRecFn___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isConstOf(x_2, x_1);
return x_3;
}
}
uint8_t l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_containsRecFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_containsRecFn___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = 8192;
x_5 = l_Lean_Expr_FindImpl_initCache;
x_6 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_3, x_4, x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 1;
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_containsRecFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_containsRecFn___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_containsRecFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_containsRecFn(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected occurrence of recursive application");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isAppOf(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_indentExpr(x_2);
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_15, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_containsRecFn(x_1, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1___boxed), 7, 1);
lean_closure_set(x_10, 0, x_1);
lean_inc(x_2);
x_11 = l_Lean_Meta_forEachExpr(x_2, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("toBelow failed");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg___closed__2;
x_7 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___spec__1___rarg(x_6, x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PProd");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("And");
return x_1;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; uint8_t x_18; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_dec(x_5);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_6, sizeof(void*)*2);
lean_dec(x_6);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_7, sizeof(void*)*2);
lean_dec(x_7);
x_17 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg___closed__1;
x_18 = lean_string_dec_eq(x_15, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_2);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg___closed__2;
x_20 = lean_string_dec_eq(x_15, x_19);
lean_dec(x_15);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
x_21 = lean_apply_1(x_4, x_1);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
lean_dec(x_1);
x_22 = lean_box_uint64(x_14);
x_23 = lean_box_uint64(x_12);
x_24 = lean_box_uint64(x_10);
x_25 = lean_box_uint64(x_16);
x_26 = lean_apply_7(x_3, x_13, x_22, x_11, x_23, x_9, x_24, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_box_uint64(x_14);
x_28 = lean_box_uint64(x_12);
x_29 = lean_box_uint64(x_10);
x_30 = lean_box_uint64(x_16);
x_31 = lean_apply_7(x_2, x_13, x_27, x_11, x_28, x_9, x_29, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_apply_1(x_4, x_1);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_apply_1(x_4, x_1);
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_apply_1(x_4, x_1);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_apply_1(x_4, x_1);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_apply_1(x_4, x_1);
return x_36;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__3___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_mkAppN(x_1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg(x_6, x_7, x_8, x_9, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_box(0);
x_22 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__1(x_3, x_4, x_21, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_13 = lean_array_get_size(x_1);
x_14 = lean_array_get_size(x_2);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_14);
x_16 = l_Array_extract___rarg(x_1, x_15, x_13);
x_17 = l_Lean_Expr_replaceFVars(x_3, x_2, x_16);
lean_dec(x_2);
lean_dec(x_3);
if (lean_obj_tag(x_17) == 5)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_getAppFn(x_18);
lean_dec(x_18);
x_21 = lean_expr_eqv(x_20, x_6);
lean_dec(x_6);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
x_22 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg(x_8, x_9, x_10, x_11, x_12);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__2(x_19, x_4, x_5, x_16, x_27, x_8, x_9, x_10, x_11, x_12);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg(x_8, x_9, x_10, x_11, x_12);
return x_29;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux(x_1, x_11);
x_13 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
lean_inc(x_1);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = lean_array_get_size(x_4);
x_19 = lean_array_get_size(x_17);
x_20 = lean_nat_dec_le(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg(x_6, x_7, x_8, x_9, x_10);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__3(x_17, x_4, x_5, x_1, x_2, x_3, x_26, x_6, x_7, x_8, x_9, x_10);
return x_27;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("left");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("right");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fst");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__7;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("snd");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__7;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_dec(x_5);
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 5)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg___closed__1;
x_19 = lean_string_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg___closed__2;
x_21 = lean_string_dec_eq(x_17, x_20);
lean_dec(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_15);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__4), 10, 3);
lean_closure_set(x_22, 0, x_2);
lean_closure_set(x_22, 1, x_3);
lean_closure_set(x_22, 2, x_4);
x_23 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_22, x_6, x_7, x_8, x_9, x_10);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_24 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__4;
x_25 = lean_array_push(x_24, x_3);
x_26 = lean_st_ref_get(x_9, x_10);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_9, x_28);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_st_ref_get(x_7, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_25);
x_37 = l_Lean_Meta_mkAppM(x_36, x_25, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_4);
x_40 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux(x_4, x_16, x_2, x_38, x_6, x_7, x_8, x_9, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_29, x_6, x_7, x_8, x_9, x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Meta_setMCtx(x_35, x_6, x_7, x_8, x_9, x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__6;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Meta_mkAppM(x_46, x_25, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux(x_4, x_15, x_2, x_48, x_6, x_7, x_8, x_9, x_49);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_16);
x_55 = lean_ctor_get(x_37, 1);
lean_inc(x_55);
lean_dec(x_37);
x_56 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_29, x_6, x_7, x_8, x_9, x_55);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Lean_Meta_setMCtx(x_35, x_6, x_7, x_8, x_9, x_57);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__6;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_61 = l_Lean_Meta_mkAppM(x_60, x_25, x_6, x_7, x_8, x_9, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux(x_4, x_15, x_2, x_62, x_6, x_7, x_8, x_9, x_63);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_61);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_17);
lean_dec(x_1);
x_69 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__4;
x_70 = lean_array_push(x_69, x_3);
x_71 = lean_st_ref_get(x_9, x_10);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_st_ref_get(x_9, x_73);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_st_ref_get(x_7, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__9;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_70);
x_82 = l_Lean_Meta_mkAppM(x_81, x_70, x_6, x_7, x_8, x_9, x_79);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_4);
x_85 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux(x_4, x_16, x_2, x_83, x_6, x_7, x_8, x_9, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_dec(x_80);
lean_dec(x_74);
lean_dec(x_70);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_74, x_6, x_7, x_8, x_9, x_86);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l_Lean_Meta_setMCtx(x_80, x_6, x_7, x_8, x_9, x_88);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__11;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_92 = l_Lean_Meta_mkAppM(x_91, x_70, x_6, x_7, x_8, x_9, x_90);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux(x_4, x_15, x_2, x_93, x_6, x_7, x_8, x_9, x_94);
return x_95;
}
else
{
uint8_t x_96; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_92);
if (x_96 == 0)
{
return x_92;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_92, 0);
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_92);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_16);
x_100 = lean_ctor_get(x_82, 1);
lean_inc(x_100);
lean_dec(x_82);
x_101 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_74, x_6, x_7, x_8, x_9, x_100);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_Lean_Meta_setMCtx(x_80, x_6, x_7, x_8, x_9, x_102);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__11;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_106 = l_Lean_Meta_mkAppM(x_105, x_70, x_6, x_7, x_8, x_9, x_104);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux(x_4, x_15, x_2, x_107, x_6, x_7, x_8, x_9, x_108);
return x_109;
}
else
{
uint8_t x_110; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_106);
if (x_110 == 0)
{
return x_106;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_106, 0);
x_112 = lean_ctor_get(x_106, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_106);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_114 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__4), 10, 3);
lean_closure_set(x_114, 0, x_2);
lean_closure_set(x_114, 1, x_3);
lean_closure_set(x_114, 2, x_4);
x_115 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_114, x_6, x_7, x_8, x_9, x_10);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_13);
lean_dec(x_11);
x_116 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__4), 10, 3);
lean_closure_set(x_116, 0, x_2);
lean_closure_set(x_116, 1, x_3);
lean_closure_set(x_116, 2, x_4);
x_117 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_116, x_6, x_7, x_8, x_9, x_10);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_12);
lean_dec(x_11);
x_118 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__4), 10, 3);
lean_closure_set(x_118, 0, x_2);
lean_closure_set(x_118, 1, x_3);
lean_closure_set(x_118, 2, x_4);
x_119 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_118, x_6, x_7, x_8, x_9, x_10);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_11);
x_120 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__4), 10, 3);
lean_closure_set(x_120, 0, x_2);
lean_closure_set(x_120, 1, x_3);
lean_closure_set(x_120, 2, x_4);
x_121 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_120, x_6, x_7, x_8, x_9, x_10);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__4), 10, 3);
lean_closure_set(x_122, 0, x_2);
lean_closure_set(x_122, 1, x_3);
lean_closure_set(x_122, 2, x_4);
x_123 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_122, x_6, x_7, x_8, x_9, x_10);
return x_123;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("definition");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structural");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__4;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("belowDict: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", arg: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_whnf(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__6;
x_32 = lean_st_ref_get(x_8, x_12);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 3);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get_uint8(x_34, sizeof(void*)*1);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = 0;
x_14 = x_37;
x_15 = x_36;
goto block_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_13, x_5, x_6, x_7, x_8, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_unbox(x_40);
lean_dec(x_40);
x_14 = x_42;
x_15 = x_41;
goto block_31;
}
block_31:
{
if (x_14 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5(x_11, x_3, x_4, x_1, x_16, x_5, x_6, x_7, x_8, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc(x_11);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_11);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__8;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__10;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_3);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_3);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_13, x_26, x_5, x_6, x_7, x_8, x_15);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5(x_11, x_3, x_4, x_1, x_28, x_5, x_6, x_7, x_8, x_29);
return x_30;
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
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_10);
if (x_43 == 0)
{
return x_10;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_10, 0);
x_45 = lean_ctor_get(x_10, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_10);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_5);
x_11 = l_Lean_mkApp(x_1, x_5);
x_12 = lean_array_get_size(x_2);
x_13 = l_Array_extract___rarg(x_2, x_3, x_12);
x_14 = l_Lean_mkAppN(x_11, x_13);
x_15 = lean_apply_7(x_4, x_5, x_14, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("C");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_instInhabitedExpr;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get(x_12, x_5, x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = lean_infer_type(x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2___closed__2;
x_19 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_18, x_9, x_10, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__1), 10, 4);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_3);
lean_closure_set(x_22, 3, x_4);
x_23 = 0;
x_24 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_20, x_23, x_16, x_22, x_7, x_8, x_9, x_10, x_21);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_13 = l_Array_extract___rarg(x_1, x_12, x_2);
x_14 = l_Lean_mkAppN(x_3, x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_14);
x_15 = lean_infer_type(x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2___boxed), 11, 4);
lean_closure_set(x_18, 0, x_14);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_5);
x_19 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__3___closed__1;
x_20 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2___rarg(x_16, x_19, x_18, x_7, x_8, x_9, x_10, x_17);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected 'below' type");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_array_set(x_5, x_6, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_6, x_15);
lean_dec(x_6);
x_4 = x_12;
x_5 = x_14;
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_1, x_18);
x_20 = lean_array_get_size(x_5);
x_21 = lean_nat_dec_lt(x_19, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_indentExpr(x_3);
x_23 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_26, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
x_32 = lean_box(0);
x_33 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__3(x_5, x_1, x_4, x_19, x_2, x_32, x_7, x_8, x_9, x_10, x_11);
return x_33;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Expr_getAppNumArgsAux(x_1, x_10);
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1;
lean_inc(x_11);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_11, x_14);
lean_dec(x_11);
lean_inc(x_1);
x_16 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg(x_2, x_3, x_1, x_1, x_13, x_15, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("belowType: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__6;
x_27 = lean_st_ref_get(x_7, x_11);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 3);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get_uint8(x_29, sizeof(void*)*1);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = 0;
x_13 = x_32;
x_14 = x_31;
goto block_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_12, x_4, x_5, x_6, x_7, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_13 = x_37;
x_14 = x_36;
goto block_26;
}
block_26:
{
if (x_13 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg___lambda__1(x_10, x_2, x_3, x_15, x_4, x_5, x_6, x_7, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_10);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_10);
x_18 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_12, x_21, x_4, x_5, x_6, x_7, x_14);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg___lambda__1(x_10, x_2, x_3, x_23, x_4, x_5, x_6, x_7, x_24);
return x_25;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
return x_9;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelow___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux(x_3, x_4, x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelow___lambda__1), 9, 2);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_1);
x_10 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
uint8_t l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_recArgHasLooseBVarsAt___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_isAppOf(x_3, x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Expr_getAppNumArgsAux(x_3, x_6);
x_8 = lean_nat_dec_lt(x_2, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_nat_sub(x_7, x_2);
lean_dec(x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_13 = l_Lean_Expr_getRevArg_x21(x_3, x_12);
x_14 = l_Lean_Expr_hasLooseBVars(x_13);
lean_dec(x_13);
return x_14;
}
}
}
}
uint8_t l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_recArgHasLooseBVarsAt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_recArgHasLooseBVarsAt___lambda__1___boxed), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = 8192;
x_10 = l_Lean_Expr_FindImpl_initCache;
x_11 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_8, x_9, x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_12);
x_14 = 1;
return x_14;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_recArgHasLooseBVarsAt___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_recArgHasLooseBVarsAt___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_recArgHasLooseBVarsAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_recArgHasLooseBVarsAt(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_12 = lean_box_uint64(x_11);
x_13 = lean_apply_3(x_7, x_9, x_10, x_12);
return x_13;
}
case 6:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_4(x_2, x_14, x_15, x_16, x_18);
return x_19;
}
case 7:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_24 = lean_box_uint64(x_23);
x_25 = lean_apply_4(x_3, x_20, x_21, x_22, x_24);
return x_25;
}
case 8:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_31 = lean_box_uint64(x_30);
x_32 = lean_apply_5(x_4, x_26, x_27, x_28, x_29, x_31);
return x_32;
}
case 10:
{
lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_36 = lean_box_uint64(x_35);
x_37 = lean_apply_3(x_5, x_33, x_34, x_36);
return x_37;
}
case 11:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 2);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_42 = lean_box_uint64(x_41);
x_43 = lean_apply_4(x_6, x_38, x_39, x_40, x_42);
return x_43;
}
default: 
{
lean_object* x_44; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_apply_1(x_8, x_1);
return x_44;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop_match__3___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_5 < x_4;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = x_6;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_uget(x_6, x_5);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_6, x_5, x_17);
x_19 = x_16;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_1, x_2, x_3, x_19, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = x_5 + x_23;
x_25 = x_21;
x_26 = lean_array_uset(x_18, x_5, x_25);
x_5 = x_24;
x_6 = x_26;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_6, 1);
x_17 = lean_nat_dec_le(x_16, x_8);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_7, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_7, x_20);
lean_dec(x_7);
x_22 = lean_nat_dec_eq(x_4, x_8);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
x_24 = l_Array_contains___at_Lean_Meta_addImplicitTargets_collect___spec__1(x_23, x_8);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = l_Lean_instInhabitedExpr;
x_26 = lean_array_get(x_25, x_5, x_8);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_1, x_2, x_3, x_26, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_array_push(x_9, x_28);
x_31 = lean_ctor_get(x_6, 2);
x_32 = lean_nat_add(x_8, x_31);
lean_dec(x_8);
x_7 = x_21;
x_8 = x_32;
x_9 = x_30;
x_15 = x_29;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_6, 2);
x_39 = lean_nat_add(x_8, x_38);
lean_dec(x_8);
x_7 = x_21;
x_8 = x_39;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_6, 2);
x_42 = lean_nat_add(x_8, x_41);
lean_dec(x_8);
x_7 = x_21;
x_8 = x_42;
goto _start;
}
}
else
{
lean_object* x_44; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_9);
lean_ctor_set(x_44, 1, x_15);
return x_44;
}
}
else
{
lean_object* x_45; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_9);
lean_ctor_set(x_45, 1, x_15);
return x_45;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_array_get_size(x_1);
x_15 = l_Array_extract___rarg(x_1, x_2, x_14);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(1u);
lean_inc(x_16);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
x_20 = l_Lean_Elab_Structural_State_addMatchers___default___closed__1;
x_21 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__2(x_3, x_4, x_5, x_6, x_15, x_19, x_16, x_17, x_20, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_19);
lean_dec(x_15);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_mkAppN(x_7, x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = l_Lean_mkAppN(x_7, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to eliminate recursive application");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_16 = l_Lean_instInhabitedExpr;
x_17 = lean_array_get(x_16, x_1, x_2);
lean_dec(x_2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_3, x_4, x_5, x_17, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_4, 6);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
x_23 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelow(x_5, x_22, x_19, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__1(x_1, x_6, x_3, x_4, x_5, x_7, x_24, x_10, x_11, x_12, x_13, x_14, x_25);
lean_dec(x_7);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_indentExpr(x_8);
x_29 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__2___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__3(x_32, x_10, x_11, x_12, x_13, x_14, x_27);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
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
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
return x_18;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_18, 0);
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_18);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("insufficient number of parameters at recursive application ");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_array_set(x_6, x_7, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_7, x_17);
lean_dec(x_7);
x_5 = x_14;
x_6 = x_16;
x_7 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
x_20 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_get_size(x_6);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = x_6;
x_27 = lean_box_usize(x_25);
x_28 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___boxed__const__1;
x_29 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__1___boxed), 12, 6);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_2);
lean_closure_set(x_29, 2, x_3);
lean_closure_set(x_29, 3, x_27);
lean_closure_set(x_29, 4, x_28);
lean_closure_set(x_29, 5, x_26);
x_30 = x_29;
x_31 = lean_apply_6(x_30, x_8, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_Lean_mkAppN(x_22, x_33);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = l_Lean_mkAppN(x_22, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_22);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
return x_31;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_21);
if (x_43 == 0)
{
return x_21;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_21, 0);
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_21);
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
lean_dec(x_5);
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
x_48 = lean_array_get_size(x_47);
lean_dec(x_47);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
x_50 = lean_nat_add(x_48, x_49);
x_51 = lean_array_get_size(x_6);
x_52 = lean_nat_dec_le(x_51, x_50);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_box(0);
x_54 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__2(x_6, x_50, x_1, x_2, x_3, x_48, x_49, x_4, x_53, x_8, x_9, x_10, x_11, x_12, x_13);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = l_Lean_indentExpr(x_4);
x_56 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___closed__2;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__4(x_59, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
return x_60;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_5 < x_4;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = x_6;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_uget(x_6, x_5);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_6, x_5, x_17);
x_19 = x_16;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_1, x_2, x_3, x_19, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = x_5 + x_23;
x_25 = x_21;
x_26 = lean_array_uset(x_18, x_5, x_25);
x_5 = x_24;
x_6 = x_26;
x_12 = x_22;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_6, 1);
x_17 = lean_nat_dec_le(x_16, x_8);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_7, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_7, x_20);
lean_dec(x_7);
x_22 = lean_nat_dec_eq(x_4, x_8);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
x_24 = l_Array_contains___at_Lean_Meta_addImplicitTargets_collect___spec__1(x_23, x_8);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = l_Lean_instInhabitedExpr;
x_26 = lean_array_get(x_25, x_5, x_8);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_1, x_2, x_3, x_26, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_array_push(x_9, x_28);
x_31 = lean_ctor_get(x_6, 2);
x_32 = lean_nat_add(x_8, x_31);
lean_dec(x_8);
x_7 = x_21;
x_8 = x_32;
x_9 = x_30;
x_15 = x_29;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_6, 2);
x_39 = lean_nat_add(x_8, x_38);
lean_dec(x_8);
x_7 = x_21;
x_8 = x_39;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_6, 2);
x_42 = lean_nat_add(x_8, x_41);
lean_dec(x_8);
x_7 = x_21;
x_8 = x_42;
goto _start;
}
}
else
{
lean_object* x_44; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_9);
lean_ctor_set(x_44, 1, x_15);
return x_44;
}
}
else
{
lean_object* x_45; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_9);
lean_ctor_set(x_45, 1, x_15);
return x_45;
}
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_array_get_size(x_1);
x_15 = l_Array_extract___rarg(x_1, x_2, x_14);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(1u);
lean_inc(x_16);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
x_20 = l_Lean_Elab_Structural_State_addMatchers___default___closed__1;
x_21 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__7(x_3, x_4, x_5, x_6, x_15, x_19, x_16, x_17, x_20, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_19);
lean_dec(x_15);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_mkAppN(x_7, x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = l_Lean_mkAppN(x_7, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_16 = l_Lean_instInhabitedExpr;
x_17 = lean_array_get(x_16, x_1, x_2);
lean_dec(x_2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_3, x_4, x_5, x_17, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_4, 6);
lean_inc(x_21);
x_22 = lean_array_get_size(x_21);
lean_dec(x_21);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
x_23 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelow(x_5, x_22, x_19, x_11, x_12, x_13, x_14, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8___lambda__1(x_1, x_6, x_3, x_4, x_5, x_7, x_24, x_10, x_11, x_12, x_13, x_14, x_25);
lean_dec(x_7);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_indentExpr(x_8);
x_29 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__2___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__3(x_32, x_10, x_11, x_12, x_13, x_14, x_27);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
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
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
return x_18;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_18, 0);
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_18);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_array_set(x_6, x_7, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_7, x_17);
lean_dec(x_7);
x_5 = x_14;
x_6 = x_16;
x_7 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
x_20 = l_Lean_Expr_isConstOf(x_5, x_1);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_get_size(x_6);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = x_6;
x_27 = lean_box_usize(x_25);
x_28 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8___boxed__const__1;
x_29 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__6___boxed), 12, 6);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_2);
lean_closure_set(x_29, 2, x_3);
lean_closure_set(x_29, 3, x_27);
lean_closure_set(x_29, 4, x_28);
lean_closure_set(x_29, 5, x_26);
x_30 = x_29;
x_31 = lean_apply_6(x_30, x_8, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_Lean_mkAppN(x_22, x_33);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = l_Lean_mkAppN(x_22, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_22);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
return x_31;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_21);
if (x_43 == 0)
{
return x_21;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_21, 0);
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_21);
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
lean_dec(x_5);
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
x_48 = lean_array_get_size(x_47);
lean_dec(x_47);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
x_50 = lean_nat_add(x_48, x_49);
x_51 = lean_array_get_size(x_6);
x_52 = lean_nat_dec_le(x_51, x_50);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_box(0);
x_54 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8___lambda__2(x_6, x_50, x_1, x_2, x_3, x_48, x_49, x_4, x_53, x_8, x_9, x_10, x_11, x_12, x_13);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = l_Lean_indentExpr(x_4);
x_56 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___closed__2;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__4(x_59, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
return x_60;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 3);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_1);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_11);
x_27 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_9);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Std_PersistentArray_push___rarg(x_20, x_30);
lean_ctor_set(x_15, 0, x_31);
x_32 = lean_st_ref_set(x_7, x_14, x_16);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_39 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
lean_inc(x_1);
x_41 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_41, 0, x_1);
x_42 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__2;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__4;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_11);
x_47 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_9);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_9);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Std_PersistentArray_push___rarg(x_40, x_50);
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_39);
lean_ctor_set(x_14, 3, x_52);
x_53 = lean_st_ref_set(x_7, x_14, x_16);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_58 = lean_ctor_get(x_14, 0);
x_59 = lean_ctor_get(x_14, 1);
x_60 = lean_ctor_get(x_14, 2);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_14);
x_61 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_62 = lean_ctor_get(x_15, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_63 = x_15;
} else {
 lean_dec_ref(x_15);
 x_63 = lean_box(0);
}
lean_inc(x_1);
x_64 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_64, 0, x_1);
x_65 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__2;
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__4;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_11);
x_70 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_71);
lean_inc(x_9);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_9);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Std_PersistentArray_push___rarg(x_62, x_73);
if (lean_is_scalar(x_63)) {
 x_75 = lean_alloc_ctor(0, 1, 1);
} else {
 x_75 = x_63;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_61);
x_76 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_76, 0, x_58);
lean_ctor_set(x_76, 1, x_59);
lean_ctor_set(x_76, 2, x_60);
lean_ctor_set(x_76, 3, x_75);
x_77 = lean_st_ref_set(x_7, x_76, x_16);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_box(0);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_Lean_checkTraceOption(x_8, x_1);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__11___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_3, x_4, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__11___rarg___lambda__1), 9, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
x_10 = 0;
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_10, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__11___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_1, x_13);
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_array_get(x_15, x_2, x_14);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_3, x_4, x_16, x_5, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 0;
x_21 = 1;
x_22 = l_Lean_Meta_mkLambdaFVars(x_2, x_18, x_20, x_21, x_8, x_9, x_10, x_11, x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected matcher application alternative");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nat application");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_8);
x_15 = lean_array_get_size(x_2);
x_16 = lean_nat_dec_le(x_1, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = l_Lean_indentExpr(x_6);
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_indentExpr(x_7);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__4(x_25, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_6);
x_31 = lean_box(0);
x_32 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__1(x_1, x_2, x_3, x_4, x_5, x_31, x_9, x_10, x_11, x_12, x_13, x_14);
return x_32;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("altNumParams: ");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", xs: ");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_st_ref_get(x_13, x_14);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*1);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = 0;
x_15 = x_42;
x_16 = x_41;
goto block_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
lean_inc(x_6);
x_44 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_6, x_9, x_10, x_11, x_12, x_13, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unbox(x_45);
lean_dec(x_45);
x_15 = x_47;
x_16 = x_46;
goto block_36;
}
block_36:
{
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_17 = lean_box(0);
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2(x_1, x_7, x_2, x_3, x_8, x_4, x_5, x_17, x_9, x_10, x_11, x_12, x_13, x_16);
lean_dec(x_1);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_1);
x_19 = l_Nat_repr(x_1);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_7);
x_26 = lean_array_to_list(lean_box(0), x_7);
x_27 = l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_26);
x_28 = l_Lean_MessageData_ofList(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_6, x_31, x_9, x_10, x_11, x_12, x_13, x_16);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2(x_1, x_7, x_2, x_3, x_8, x_4, x_5, x_33, x_9, x_10, x_11, x_12, x_13, x_34);
lean_dec(x_1);
return x_35;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_6 < x_5;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = x_7;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_array_uget(x_7, x_6);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_7, x_6, x_18);
x_20 = x_17;
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_21);
lean_inc(x_2);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3), 14, 6);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_21);
lean_closure_set(x_23, 4, x_3);
lean_closure_set(x_23, 5, x_4);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_24 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__11___rarg(x_21, x_23, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 1;
x_28 = x_6 + x_27;
x_29 = x_25;
x_30 = lean_array_uset(x_19, x_6, x_29);
x_6 = x_28;
x_7 = x_30;
x_13 = x_26;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__13___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__13___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__13___rarg___lambda__1), 8, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__13___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__14___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__13___rarg___lambda__1), 8, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__14___rarg), 10, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to add `below` argument to 'matcher' application");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_indentD(x_1);
x_3 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__3;
x_4 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg), 7, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
x_15 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l_Lean_Meta_mapErrorImp___rarg(x_14, x_15, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_12, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_take(x_8, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
x_29 = lean_ctor_get(x_17, 2);
x_30 = lean_ctor_get(x_17, 3);
x_31 = lean_ctor_get(x_17, 4);
x_32 = lean_ctor_get(x_17, 5);
x_33 = lean_ctor_get(x_17, 6);
x_34 = lean_ctor_get(x_17, 7);
x_35 = lean_ctor_get(x_17, 8);
x_36 = lean_box(0);
lean_inc(x_27);
x_37 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_26, x_27, x_36);
lean_ctor_set(x_22, 0, x_37);
x_38 = lean_st_ref_set(x_8, x_22, x_23);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Array_zip___rarg(x_34, x_33);
lean_dec(x_34);
x_41 = lean_array_get_size(x_40);
x_42 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_43 = x_40;
x_44 = lean_box_usize(x_42);
x_45 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2___boxed__const__1;
x_46 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___boxed), 13, 7);
lean_closure_set(x_46, 0, x_3);
lean_closure_set(x_46, 1, x_4);
lean_closure_set(x_46, 2, x_5);
lean_closure_set(x_46, 3, x_6);
lean_closure_set(x_46, 4, x_44);
lean_closure_set(x_46, 5, x_45);
lean_closure_set(x_46, 6, x_43);
x_47 = x_46;
x_48 = lean_apply_6(x_47, x_8, x_9, x_10, x_11, x_12, x_39);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_ctor_set(x_17, 7, x_50);
x_51 = l_Lean_Meta_MatcherApp_toExpr(x_17);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
lean_ctor_set(x_17, 7, x_52);
x_54 = l_Lean_Meta_MatcherApp_toExpr(x_17);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_free_object(x_17);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_56 = !lean_is_exclusive(x_48);
if (x_56 == 0)
{
return x_48;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_48);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; size_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_60 = lean_ctor_get(x_22, 0);
x_61 = lean_ctor_get(x_17, 0);
x_62 = lean_ctor_get(x_17, 1);
x_63 = lean_ctor_get(x_17, 2);
x_64 = lean_ctor_get(x_17, 3);
x_65 = lean_ctor_get(x_17, 4);
x_66 = lean_ctor_get(x_17, 5);
x_67 = lean_ctor_get(x_17, 6);
x_68 = lean_ctor_get(x_17, 7);
x_69 = lean_ctor_get(x_17, 8);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_17);
x_70 = lean_box(0);
lean_inc(x_61);
x_71 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_60, x_61, x_70);
lean_ctor_set(x_22, 0, x_71);
x_72 = lean_st_ref_set(x_8, x_22, x_23);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Array_zip___rarg(x_68, x_67);
lean_dec(x_68);
x_75 = lean_array_get_size(x_74);
x_76 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_77 = x_74;
x_78 = lean_box_usize(x_76);
x_79 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2___boxed__const__1;
x_80 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___boxed), 13, 7);
lean_closure_set(x_80, 0, x_3);
lean_closure_set(x_80, 1, x_4);
lean_closure_set(x_80, 2, x_5);
lean_closure_set(x_80, 3, x_6);
lean_closure_set(x_80, 4, x_78);
lean_closure_set(x_80, 5, x_79);
lean_closure_set(x_80, 6, x_77);
x_81 = x_80;
x_82 = lean_apply_6(x_81, x_8, x_9, x_10, x_11, x_12, x_73);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_86, 0, x_61);
lean_ctor_set(x_86, 1, x_62);
lean_ctor_set(x_86, 2, x_63);
lean_ctor_set(x_86, 3, x_64);
lean_ctor_set(x_86, 4, x_65);
lean_ctor_set(x_86, 5, x_66);
lean_ctor_set(x_86, 6, x_67);
lean_ctor_set(x_86, 7, x_83);
lean_ctor_set(x_86, 8, x_69);
x_87 = l_Lean_Meta_MatcherApp_toExpr(x_86);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_85;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_84);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_82, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_91 = x_82;
} else {
 lean_dec_ref(x_82);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; size_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_93 = lean_ctor_get(x_22, 0);
x_94 = lean_ctor_get(x_22, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_22);
x_95 = lean_ctor_get(x_17, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_17, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_17, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_17, 3);
lean_inc(x_98);
x_99 = lean_ctor_get(x_17, 4);
lean_inc(x_99);
x_100 = lean_ctor_get(x_17, 5);
lean_inc(x_100);
x_101 = lean_ctor_get(x_17, 6);
lean_inc(x_101);
x_102 = lean_ctor_get(x_17, 7);
lean_inc(x_102);
x_103 = lean_ctor_get(x_17, 8);
lean_inc(x_103);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 lean_ctor_release(x_17, 6);
 lean_ctor_release(x_17, 7);
 lean_ctor_release(x_17, 8);
 x_104 = x_17;
} else {
 lean_dec_ref(x_17);
 x_104 = lean_box(0);
}
x_105 = lean_box(0);
lean_inc(x_95);
x_106 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_93, x_95, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_94);
x_108 = lean_st_ref_set(x_8, x_107, x_23);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = l_Array_zip___rarg(x_102, x_101);
lean_dec(x_102);
x_111 = lean_array_get_size(x_110);
x_112 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_113 = x_110;
x_114 = lean_box_usize(x_112);
x_115 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2___boxed__const__1;
x_116 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___boxed), 13, 7);
lean_closure_set(x_116, 0, x_3);
lean_closure_set(x_116, 1, x_4);
lean_closure_set(x_116, 2, x_5);
lean_closure_set(x_116, 3, x_6);
lean_closure_set(x_116, 4, x_114);
lean_closure_set(x_116, 5, x_115);
lean_closure_set(x_116, 6, x_113);
x_117 = x_116;
x_118 = lean_apply_6(x_117, x_8, x_9, x_10, x_11, x_12, x_109);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_122 = lean_alloc_ctor(0, 9, 0);
} else {
 x_122 = x_104;
}
lean_ctor_set(x_122, 0, x_95);
lean_ctor_set(x_122, 1, x_96);
lean_ctor_set(x_122, 2, x_97);
lean_ctor_set(x_122, 3, x_98);
lean_ctor_set(x_122, 4, x_99);
lean_ctor_set(x_122, 5, x_100);
lean_ctor_set(x_122, 6, x_101);
lean_ctor_set(x_122, 7, x_119);
lean_ctor_set(x_122, 8, x_103);
x_123 = l_Lean_Meta_MatcherApp_toExpr(x_122);
if (lean_is_scalar(x_121)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_121;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_120);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
x_125 = lean_ctor_get(x_118, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_118, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_127 = x_118;
} else {
 lean_dec_ref(x_118);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_129 = !lean_is_exclusive(x_16);
if (x_129 == 0)
{
return x_16;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_16, 0);
x_131 = lean_ctor_get(x_16, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_16);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_expr_instantiate1(x_1, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__4;
x_17 = lean_array_push(x_16, x_5);
x_18 = 0;
x_19 = 1;
x_20 = l_Lean_Meta_mkLambdaFVars(x_17, x_14, x_18, x_19, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_expr_instantiate1(x_1, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__4;
x_17 = lean_array_push(x_16, x_5);
x_18 = 0;
x_19 = 1;
x_20 = l_Lean_Meta_mkForallFVars(x_17, x_14, x_18, x_19, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_10);
lean_dec(x_9);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("below before matcherApp.addArg: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" : ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 5:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_4);
x_11 = l_Lean_Meta_matchMatcherApp_x3f(x_4, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Expr_getAppNumArgsAux(x_4, x_14);
x_16 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1;
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
lean_inc(x_4);
x_20 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5(x_1, x_2, x_3, x_4, x_4, x_17, x_19, x_5, x_6, x_7, x_8, x_9, x_13);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
lean_inc(x_4);
lean_inc(x_1);
x_23 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_recArgHasLooseBVarsAt(x_1, x_2, x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Expr_getAppNumArgsAux(x_4, x_24);
x_26 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1;
lean_inc(x_25);
x_27 = lean_mk_array(x_25, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_25, x_28);
lean_dec(x_25);
lean_inc(x_4);
x_30 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8(x_1, x_2, x_3, x_4, x_4, x_27, x_29, x_5, x_6, x_7, x_8, x_9, x_21);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_31 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__6;
x_57 = lean_st_ref_get(x_9, x_21);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 3);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get_uint8(x_59, sizeof(void*)*1);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = 0;
x_32 = x_62;
x_33 = x_61;
goto block_56;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_64 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_31, x_5, x_6, x_7, x_8, x_9, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unbox(x_65);
lean_dec(x_65);
x_32 = x_67;
x_33 = x_66;
goto block_56;
}
block_56:
{
if (x_32 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2(x_22, x_3, x_1, x_2, x_4, x_31, x_34, x_5, x_6, x_7, x_8, x_9, x_33);
return x_35;
}
else
{
lean_object* x_36; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_36 = lean_infer_type(x_3, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_3);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_3);
x_40 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_37);
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_31, x_47, x_5, x_6, x_7, x_8, x_9, x_38);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2(x_22, x_3, x_1, x_2, x_4, x_31, x_49, x_5, x_6, x_7, x_8, x_9, x_50);
lean_dec(x_49);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_36);
if (x_52 == 0)
{
return x_36;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_36, 0);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_36);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
}
}
case 6:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint64_t x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_4, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_4, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_4, 2);
lean_inc(x_70);
x_71 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_72 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_1, x_2, x_3, x_69, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = (uint8_t)((x_71 << 24) >> 61);
x_76 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__3___boxed), 11, 4);
lean_closure_set(x_76, 0, x_70);
lean_closure_set(x_76, 1, x_1);
lean_closure_set(x_76, 2, x_2);
lean_closure_set(x_76, 3, x_3);
x_77 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__13___rarg(x_68, x_75, x_73, x_76, x_5, x_6, x_7, x_8, x_9, x_74);
return x_77;
}
else
{
uint8_t x_78; 
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_72);
if (x_78 == 0)
{
return x_72;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_72, 0);
x_80 = lean_ctor_get(x_72, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_72);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
case 7:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint64_t x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_4, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_4, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_4, 2);
lean_inc(x_84);
x_85 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_86 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_1, x_2, x_3, x_83, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = (uint8_t)((x_85 << 24) >> 61);
x_90 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__4___boxed), 11, 4);
lean_closure_set(x_90, 0, x_84);
lean_closure_set(x_90, 1, x_1);
lean_closure_set(x_90, 2, x_2);
lean_closure_set(x_90, 3, x_3);
x_91 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__13___rarg(x_82, x_89, x_87, x_90, x_5, x_6, x_7, x_8, x_9, x_88);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_86);
if (x_92 == 0)
{
return x_86;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_86, 0);
x_94 = lean_ctor_get(x_86, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_86);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
case 8:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_4, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_4, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_4, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_4, 3);
lean_inc(x_99);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_100 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_1, x_2, x_3, x_97, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_103 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_1, x_2, x_3, x_98, x_5, x_6, x_7, x_8, x_9, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__3___boxed), 11, 4);
lean_closure_set(x_106, 0, x_99);
lean_closure_set(x_106, 1, x_1);
lean_closure_set(x_106, 2, x_2);
lean_closure_set(x_106, 3, x_3);
x_107 = l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__14___rarg(x_96, x_101, x_104, x_106, x_5, x_6, x_7, x_8, x_9, x_105);
return x_107;
}
else
{
uint8_t x_108; 
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_96);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_103);
if (x_108 == 0)
{
return x_103;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_103, 0);
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_103);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_100);
if (x_112 == 0)
{
return x_100;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_100, 0);
x_114 = lean_ctor_get(x_100, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_100);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
case 10:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_4, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_4, 1);
lean_inc(x_117);
lean_dec(x_4);
x_118 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_1, x_2, x_3, x_117, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = l_Lean_mkMData(x_116, x_120);
lean_ctor_set(x_118, 0, x_121);
return x_118;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_118, 0);
x_123 = lean_ctor_get(x_118, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_118);
x_124 = l_Lean_mkMData(x_116, x_122);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
uint8_t x_126; 
lean_dec(x_116);
x_126 = !lean_is_exclusive(x_118);
if (x_126 == 0)
{
return x_118;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_118, 0);
x_128 = lean_ctor_get(x_118, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_118);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
case 11:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_4, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_4, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_4, 2);
lean_inc(x_132);
lean_dec(x_4);
x_133 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_1, x_2, x_3, x_132, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 0);
x_136 = l_Lean_mkProj(x_130, x_131, x_135);
lean_ctor_set(x_133, 0, x_136);
return x_133;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_133, 0);
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_133);
x_139 = l_Lean_mkProj(x_130, x_131, x_137);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
uint8_t x_141; 
lean_dec(x_131);
lean_dec(x_130);
x_141 = !lean_is_exclusive(x_133);
if (x_141 == 0)
{
return x_133;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_133, 0);
x_143 = lean_ctor_get(x_133, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_133);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
default: 
{
lean_object* x_145; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_145 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn(x_1, x_4, x_6, x_7, x_8, x_9, x_10);
return x_145;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__1(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__6(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__13___rarg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
return x_14;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow_match__3___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not a matcherApp: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 5);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l_Lean_Meta_IndPredBelow_findBelowIdx(x_9, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = l_Lean_Meta_MatcherApp_toExpr(x_2);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_Meta_MatcherApp_toExpr(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_22 = l_Lean_Meta_IndPredBelow_mkBelowMatcher(x_2, x_1, x_20, x_21, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_st_ref_get(x_7, x_24);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_take(x_3, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_30, 1);
x_34 = lean_array_push(x_33, x_26);
lean_ctor_set(x_30, 1, x_34);
x_35 = lean_st_ref_set(x_3, x_30, x_31);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_25);
x_37 = l_Lean_Meta_matchMatcherApp_x3f(x_25, x_4, x_5, x_6, x_7, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_1);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_25);
x_41 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___closed__2;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__3(x_44, x_3, x_4, x_5, x_6, x_7, x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_25);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_ctor_get(x_38, 0);
lean_inc(x_47);
lean_dec(x_38);
x_2 = x_47;
x_8 = x_46;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_30, 0);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_30);
x_51 = lean_array_push(x_50, x_26);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_st_ref_set(x_3, x_52, x_31);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
lean_inc(x_25);
x_55 = l_Lean_Meta_matchMatcherApp_x3f(x_25, x_4, x_5, x_6, x_7, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_1);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_58, 0, x_25);
x_59 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___closed__2;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__3(x_62, x_3, x_4, x_5, x_6, x_7, x_57);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_25);
x_64 = lean_ctor_get(x_55, 1);
lean_inc(x_64);
lean_dec(x_55);
x_65 = lean_ctor_get(x_56, 0);
lean_inc(x_65);
lean_dec(x_56);
x_2 = x_65;
x_8 = x_64;
goto _start;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_22);
if (x_67 == 0)
{
return x_22;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_22, 0);
x_69 = lean_ctor_get(x_22, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_22);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_10);
if (x_71 == 0)
{
return x_10;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_10, 0);
x_73 = lean_ctor_get(x_10, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_10);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_6 < x_5;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = x_7;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_uget(x_7, x_6);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_7, x_6, x_18);
x_20 = x_17;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(x_1, x_2, x_3, x_4, x_20, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = x_6 + x_24;
x_26 = x_22;
x_27 = lean_array_uset(x_19, x_6, x_26);
x_6 = x_25;
x_7 = x_27;
x_13 = x_23;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("could not solve using backwards chaining ");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_array_set(x_7, x_8, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_8, x_18);
lean_dec(x_8);
x_6 = x_15;
x_7 = x_17;
x_8 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_8);
x_21 = l_Lean_Expr_isConstOf(x_6, x_1);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(x_1, x_2, x_3, x_4, x_6, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_7);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = x_7;
x_28 = lean_box_usize(x_26);
x_29 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___boxed__const__1;
x_30 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__1___boxed), 13, 7);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_2);
lean_closure_set(x_30, 2, x_3);
lean_closure_set(x_30, 3, x_4);
lean_closure_set(x_30, 4, x_28);
lean_closure_set(x_30, 5, x_29);
lean_closure_set(x_30, 6, x_27);
x_31 = x_30;
x_32 = lean_apply_6(x_31, x_9, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = l_Lean_mkAppN(x_23, x_34);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = l_Lean_mkAppN(x_23, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_23);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_22);
if (x_44 == 0)
{
return x_22;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_22, 0);
x_46 = lean_ctor_get(x_22, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_22);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_48 = lean_infer_type(x_5, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_box(0);
lean_inc(x_10);
x_52 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_49, x_51, x_10, x_11, x_12, x_13, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Expr_mvarId_x21(x_53);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_55);
x_56 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_55, x_4, x_10, x_11, x_12, x_13, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_53);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_61 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___closed__2;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__3(x_64, x_9, x_10, x_11, x_12, x_13, x_59);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_55);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_66 = !lean_is_exclusive(x_56);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_56, 0);
lean_dec(x_67);
lean_ctor_set(x_56, 0, x_53);
return x_56;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
lean_dec(x_56);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_53);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_70 = !lean_is_exclusive(x_56);
if (x_70 == 0)
{
return x_56;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_56, 0);
x_72 = lean_ctor_get(x_56, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_56);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_48);
if (x_74 == 0)
{
return x_48;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_48, 0);
x_76 = lean_ctor_get(x_48, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_48);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_6 < x_5;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = x_7;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_uget(x_7, x_6);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_7, x_6, x_18);
x_20 = x_17;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(x_1, x_2, x_3, x_4, x_20, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = x_6 + x_24;
x_26 = x_22;
x_27 = lean_array_uset(x_19, x_6, x_26);
x_6 = x_25;
x_7 = x_27;
x_13 = x_23;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__4___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_array_set(x_7, x_8, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_8, x_18);
lean_dec(x_8);
x_6 = x_15;
x_7 = x_17;
x_8 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_8);
x_21 = l_Lean_Expr_isConstOf(x_6, x_1);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(x_1, x_2, x_3, x_4, x_6, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_7);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = x_7;
x_28 = lean_box_usize(x_26);
x_29 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__4___boxed__const__1;
x_30 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__3___boxed), 13, 7);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_2);
lean_closure_set(x_30, 2, x_3);
lean_closure_set(x_30, 3, x_4);
lean_closure_set(x_30, 4, x_28);
lean_closure_set(x_30, 5, x_29);
lean_closure_set(x_30, 6, x_27);
x_31 = x_30;
x_32 = lean_apply_6(x_31, x_9, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = l_Lean_mkAppN(x_23, x_34);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = l_Lean_mkAppN(x_23, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_23);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_22);
if (x_44 == 0)
{
return x_22;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_22, 0);
x_46 = lean_ctor_get(x_22, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_22);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_48 = lean_infer_type(x_5, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_box(0);
lean_inc(x_10);
x_52 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_49, x_51, x_10, x_11, x_12, x_13, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Expr_mvarId_x21(x_53);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_55);
x_56 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_55, x_4, x_10, x_11, x_12, x_13, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_53);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_61 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___closed__2;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__3(x_64, x_9, x_10, x_11, x_12, x_13, x_59);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_55);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_66 = !lean_is_exclusive(x_56);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_56, 0);
lean_dec(x_67);
lean_ctor_set(x_56, 0, x_53);
return x_56;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
lean_dec(x_56);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_53);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_70 = !lean_is_exclusive(x_56);
if (x_70 == 0)
{
return x_56;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_56, 0);
x_72 = lean_ctor_get(x_56, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_56);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_48);
if (x_74 == 0)
{
return x_48;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_48, 0);
x_76 = lean_ctor_get(x_48, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_48);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_6 < x_5;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = x_7;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_uget(x_7, x_6);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_7, x_6, x_18);
x_20 = x_17;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(x_1, x_2, x_3, x_4, x_20, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = x_6 + x_24;
x_26 = x_22;
x_27 = lean_array_uset(x_19, x_6, x_26);
x_6 = x_25;
x_7 = x_27;
x_13 = x_23;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__6___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_array_set(x_7, x_8, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_8, x_18);
lean_dec(x_8);
x_6 = x_15;
x_7 = x_17;
x_8 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_8);
x_21 = l_Lean_Expr_isConstOf(x_6, x_1);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(x_1, x_2, x_3, x_4, x_6, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_7);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = x_7;
x_28 = lean_box_usize(x_26);
x_29 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__6___boxed__const__1;
x_30 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__5___boxed), 13, 7);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_2);
lean_closure_set(x_30, 2, x_3);
lean_closure_set(x_30, 3, x_4);
lean_closure_set(x_30, 4, x_28);
lean_closure_set(x_30, 5, x_29);
lean_closure_set(x_30, 6, x_27);
x_31 = x_30;
x_32 = lean_apply_6(x_31, x_9, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = l_Lean_mkAppN(x_23, x_34);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = l_Lean_mkAppN(x_23, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_23);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_22);
if (x_44 == 0)
{
return x_22;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_22, 0);
x_46 = lean_ctor_get(x_22, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_22);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_48 = lean_infer_type(x_5, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_box(0);
lean_inc(x_10);
x_52 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_49, x_51, x_10, x_11, x_12, x_13, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Expr_mvarId_x21(x_53);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_55);
x_56 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_55, x_4, x_10, x_11, x_12, x_13, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_53);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_61 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___closed__2;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__3(x_64, x_9, x_10, x_11, x_12, x_13, x_59);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_55);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_66 = !lean_is_exclusive(x_56);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_56, 0);
lean_dec(x_67);
lean_ctor_set(x_56, 0, x_53);
return x_56;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_56, 1);
lean_inc(x_68);
lean_dec(x_56);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_53);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_70 = !lean_is_exclusive(x_56);
if (x_70 == 0)
{
return x_56;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_56, 0);
x_72 = lean_ctor_get(x_56, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_56);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_48);
if (x_74 == 0)
{
return x_48;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_48, 0);
x_76 = lean_ctor_get(x_48, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_48);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_getAppNumArgsAux(x_1, x_13);
x_15 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
lean_inc(x_1);
x_19 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__6(x_2, x_3, x_4, x_5, x_1, x_1, x_16, x_18, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("modified matcher:\n");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("could not add below discriminant");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_dec(x_7);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow(x_1, x_2, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_MatcherApp_toExpr(x_2);
x_18 = lean_expr_eqv(x_15, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_st_ref_get(x_12, x_16);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 3);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get_uint8(x_35, sizeof(void*)*1);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = 0;
x_19 = x_38;
x_20 = x_37;
goto block_32;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
lean_inc(x_6);
x_40 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_6, x_8, x_9, x_10, x_11, x_12, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_unbox(x_41);
lean_dec(x_41);
x_19 = x_43;
x_20 = x_42;
goto block_32;
}
block_32:
{
if (x_19 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_21 = lean_box(0);
x_22 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__1(x_15, x_3, x_4, x_1, x_5, x_21, x_8, x_9, x_10, x_11, x_12, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc(x_15);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_15);
x_24 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_6, x_27, x_8, x_9, x_10, x_11, x_12, x_20);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__1(x_15, x_3, x_4, x_1, x_5, x_29, x_8, x_9, x_10, x_11, x_12, x_30);
return x_31;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__4;
x_45 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__3(x_44, x_8, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_14);
if (x_46 == 0)
{
return x_14;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_14, 0);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_14);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_expr_instantiate1(x_1, x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_14 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__4;
x_18 = lean_array_push(x_17, x_6);
x_19 = 0;
x_20 = 1;
x_21 = l_Lean_Meta_mkLambdaFVars(x_18, x_15, x_19, x_20, x_8, x_9, x_10, x_11, x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_expr_instantiate1(x_1, x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_14 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__4;
x_18 = lean_array_push(x_17, x_6);
x_19 = 0;
x_20 = 1;
x_21 = l_Lean_Meta_mkForallFVars(x_18, x_15, x_19, x_20, x_8, x_9, x_10, x_11, x_16);
lean_dec(x_11);
lean_dec(x_10);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matcherApp before adding below transformation:\n");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_5);
x_12 = l_Lean_Meta_matchMatcherApp_x3f(x_5, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Expr_getAppNumArgsAux(x_5, x_15);
x_17 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1;
lean_inc(x_16);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_16, x_19);
lean_dec(x_16);
lean_inc(x_5);
x_21 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2(x_1, x_2, x_3, x_4, x_5, x_5, x_18, x_20, x_6, x_7, x_8, x_9, x_10, x_14);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
lean_inc(x_5);
lean_inc(x_1);
x_24 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_recArgHasLooseBVarsAt(x_1, x_2, x_5);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Expr_getAppNumArgsAux(x_5, x_25);
x_27 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1;
lean_inc(x_26);
x_28 = lean_mk_array(x_26, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_26, x_29);
lean_dec(x_26);
lean_inc(x_5);
x_31 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__4(x_1, x_2, x_3, x_4, x_5, x_5, x_28, x_30, x_6, x_7, x_8, x_9, x_10, x_22);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_5);
x_32 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__6;
x_48 = lean_st_ref_get(x_10, x_22);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 3);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get_uint8(x_50, sizeof(void*)*1);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = 0;
x_33 = x_53;
x_34 = x_52;
goto block_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_32, x_6, x_7, x_8, x_9, x_10, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_unbox(x_56);
lean_dec(x_56);
x_33 = x_58;
x_34 = x_57;
goto block_47;
}
block_47:
{
if (x_33 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box(0);
x_36 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2(x_3, x_23, x_1, x_2, x_4, x_32, x_35, x_6, x_7, x_8, x_9, x_10, x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_inc(x_23);
x_37 = l_Lean_Meta_MatcherApp_toExpr(x_23);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__2;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_32, x_42, x_6, x_7, x_8, x_9, x_10, x_34);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2(x_3, x_23, x_1, x_2, x_4, x_32, x_44, x_6, x_7, x_8, x_9, x_10, x_45);
return x_46;
}
}
}
}
}
case 6:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint64_t x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_5, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_5, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_5, 2);
lean_inc(x_61);
x_62 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_63 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(x_1, x_2, x_3, x_4, x_60, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = (uint8_t)((x_62 << 24) >> 61);
x_67 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__3___boxed), 12, 5);
lean_closure_set(x_67, 0, x_61);
lean_closure_set(x_67, 1, x_1);
lean_closure_set(x_67, 2, x_2);
lean_closure_set(x_67, 3, x_3);
lean_closure_set(x_67, 4, x_4);
x_68 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__13___rarg(x_59, x_66, x_64, x_67, x_6, x_7, x_8, x_9, x_10, x_65);
return x_68;
}
else
{
uint8_t x_69; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_63);
if (x_69 == 0)
{
return x_63;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_63, 0);
x_71 = lean_ctor_get(x_63, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_63);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
case 7:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_5, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_5, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_5, 2);
lean_inc(x_75);
x_76 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_77 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(x_1, x_2, x_3, x_4, x_74, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = (uint8_t)((x_76 << 24) >> 61);
x_81 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__4___boxed), 12, 5);
lean_closure_set(x_81, 0, x_75);
lean_closure_set(x_81, 1, x_1);
lean_closure_set(x_81, 2, x_2);
lean_closure_set(x_81, 3, x_3);
lean_closure_set(x_81, 4, x_4);
x_82 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__13___rarg(x_73, x_80, x_78, x_81, x_6, x_7, x_8, x_9, x_10, x_79);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_77);
if (x_83 == 0)
{
return x_77;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_77, 0);
x_85 = lean_ctor_get(x_77, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_77);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
case 8:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_5, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_5, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_5, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_5, 3);
lean_inc(x_90);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_91 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(x_1, x_2, x_3, x_4, x_88, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_94 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(x_1, x_2, x_3, x_4, x_89, x_6, x_7, x_8, x_9, x_10, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__3___boxed), 12, 5);
lean_closure_set(x_97, 0, x_90);
lean_closure_set(x_97, 1, x_1);
lean_closure_set(x_97, 2, x_2);
lean_closure_set(x_97, 3, x_3);
lean_closure_set(x_97, 4, x_4);
x_98 = l_Lean_Meta_withLetDecl___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__14___rarg(x_87, x_92, x_95, x_97, x_6, x_7, x_8, x_9, x_10, x_96);
return x_98;
}
else
{
uint8_t x_99; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_94);
if (x_99 == 0)
{
return x_94;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_94, 0);
x_101 = lean_ctor_get(x_94, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_94);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_91);
if (x_103 == 0)
{
return x_91;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_91, 0);
x_105 = lean_ctor_get(x_91, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_91);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
case 10:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_5, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_5, 1);
lean_inc(x_108);
lean_dec(x_5);
x_109 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(x_1, x_2, x_3, x_4, x_108, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_109) == 0)
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = l_Lean_mkMData(x_107, x_111);
lean_ctor_set(x_109, 0, x_112);
return x_109;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_109, 0);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_109);
x_115 = l_Lean_mkMData(x_107, x_113);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec(x_107);
x_117 = !lean_is_exclusive(x_109);
if (x_117 == 0)
{
return x_109;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_109, 0);
x_119 = lean_ctor_get(x_109, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_109);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
case 11:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_5, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_5, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_5, 2);
lean_inc(x_123);
lean_dec(x_5);
x_124 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(x_1, x_2, x_3, x_4, x_123, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = l_Lean_mkProj(x_121, x_122, x_126);
lean_ctor_set(x_124, 0, x_127);
return x_124;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_124, 0);
x_129 = lean_ctor_get(x_124, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_124);
x_130 = l_Lean_mkProj(x_121, x_122, x_128);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
else
{
uint8_t x_132; 
lean_dec(x_122);
lean_dec(x_121);
x_132 = !lean_is_exclusive(x_124);
if (x_132 == 0)
{
return x_124;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_124, 0);
x_134 = lean_ctor_get(x_124, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_124);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
default: 
{
lean_object* x_136; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_136 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn(x_1, x_5, x_7, x_8, x_9, x_10, x_11);
return x_136;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__1(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__3(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__5(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth;
x_13 = l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_225____spec__1(x_11, x_12);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(x_1, x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__11___rarg___lambda__1), 9, 2);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___rarg(x_1, x_2, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___spec__1___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_4 == x_5;
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; size_t x_10; size_t x_11; 
x_8 = lean_array_uget(x_3, x_4);
x_9 = lean_expr_eqv(x_8, x_2);
x_10 = 1;
x_11 = x_4 + x_10;
if (x_9 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_1, 7);
x_13 = l_Array_contains___at_Lean_Meta_getElimInfo___spec__5(x_12, x_8);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_push(x_6, x_8);
x_4 = x_11;
x_6 = x_14;
goto _start;
}
else
{
lean_dec(x_8);
x_4 = x_11;
goto _start;
}
}
else
{
lean_dec(x_8);
x_4 = x_11;
goto _start;
}
}
else
{
return x_6;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_instInhabitedExpr;
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get(x_16, x_8, x_17);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_18);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop(x_1, x_2, x_18, x_3, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__1___closed__1;
x_23 = lean_array_push(x_22, x_4);
x_24 = lean_array_push(x_23, x_18);
x_25 = l_Array_append___rarg(x_5, x_24);
lean_inc(x_6);
x_26 = l_Array_append___rarg(x_25, x_6);
x_27 = 0;
x_28 = 1;
x_29 = l_Lean_Meta_mkLambdaFVars(x_26, x_20, x_27, x_28, x_11, x_12, x_13, x_14, x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = l_Lean_mkApp(x_7, x_31);
x_33 = l_Lean_mkAppN(x_32, x_6);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = l_Lean_mkApp(x_7, x_34);
x_37 = l_Lean_mkAppN(x_36, x_6);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_7);
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
return x_29;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_29, 0);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_29);
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
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_1, x_17, x_2, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__4;
lean_inc(x_3);
x_22 = lean_array_push(x_21, x_3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_23 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_22, x_17, x_19, x_12, x_13, x_14, x_15, x_20);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__1___boxed), 15, 7);
lean_closure_set(x_26, 0, x_4);
lean_closure_set(x_26, 1, x_5);
lean_closure_set(x_26, 2, x_6);
lean_closure_set(x_26, 3, x_3);
lean_closure_set(x_26, 4, x_1);
lean_closure_set(x_26, 5, x_7);
lean_closure_set(x_26, 6, x_8);
x_27 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___spec__1___rarg(x_24, x_9, x_26, x_11, x_12, x_13, x_14, x_15, x_25);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("FType: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
x_18 = l_Lean_instInhabitedExpr;
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get(x_18, x_10, x_19);
lean_dec(x_10);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_21 = lean_infer_type(x_20, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_38 = lean_st_ref_get(x_16, x_23);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 3);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get_uint8(x_40, sizeof(void*)*1);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = 0;
x_24 = x_43;
x_25 = x_42;
goto block_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
lean_inc(x_9);
x_45 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_9, x_12, x_13, x_14, x_15, x_16, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_unbox(x_46);
lean_dec(x_46);
x_24 = x_48;
x_25 = x_47;
goto block_37;
}
block_37:
{
if (x_24 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
x_26 = lean_box(0);
x_27 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__2(x_1, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_26, x_12, x_13, x_14, x_15, x_16, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc(x_22);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_22);
x_29 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_9, x_32, x_12, x_13, x_14, x_15, x_16, x_25);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__2(x_1, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_34, x_12, x_13, x_14, x_15, x_16, x_35);
lean_dec(x_34);
return x_36;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_21);
if (x_49 == 0)
{
return x_21;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_21, 0);
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_21);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__3___closed__1;
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3___boxed), 17, 9);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_5);
lean_closure_set(x_18, 5, x_6);
lean_closure_set(x_18, 6, x_7);
lean_closure_set(x_18, 7, x_17);
lean_closure_set(x_18, 8, x_8);
x_19 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___spec__1___rarg(x_9, x_17, x_18, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("brecOnType ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_10);
x_31 = lean_st_ref_get(x_15, x_16);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*1);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = 0;
x_17 = x_36;
x_18 = x_35;
goto block_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
lean_inc(x_8);
x_38 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_8, x_11, x_12, x_13, x_14, x_15, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unbox(x_39);
lean_dec(x_39);
x_17 = x_41;
x_18 = x_40;
goto block_30;
}
block_30:
{
if (x_17 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19, x_11, x_12, x_13, x_14, x_15, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_9);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_9);
x_22 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_8);
x_26 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_8, x_25, x_11, x_12, x_13, x_14, x_15, x_18);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27, x_11, x_12, x_13, x_14, x_15, x_28);
lean_dec(x_27);
return x_29;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("brecOn     ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
x_18 = lean_ctor_get(x_1, 6);
lean_inc(x_18);
if (x_9 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_1, 4);
lean_inc(x_63);
x_64 = l_Lean_brecOnSuffix;
x_65 = lean_name_mk_string(x_63, x_64);
x_66 = lean_ctor_get(x_1, 5);
lean_inc(x_66);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_10);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_mkConst(x_65, x_67);
x_19 = x_68;
goto block_62;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_10);
x_69 = lean_ctor_get(x_1, 4);
lean_inc(x_69);
x_70 = l_Lean_binductionOnSuffix;
x_71 = lean_name_mk_string(x_69, x_70);
x_72 = lean_ctor_get(x_1, 5);
lean_inc(x_72);
x_73 = l_Lean_mkConst(x_71, x_72);
x_19 = x_73;
goto block_62;
}
block_62:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l_Lean_mkAppN(x_19, x_18);
x_21 = l_Lean_mkApp(x_20, x_2);
lean_inc(x_3);
x_22 = l_Lean_mkAppN(x_21, x_3);
lean_inc(x_4);
x_23 = l_Lean_mkApp(x_22, x_4);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_23);
x_24 = l_Lean_Meta_check(x_23, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_23);
x_26 = lean_infer_type(x_23, x_13, x_14, x_15, x_16, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_43 = lean_st_ref_get(x_16, x_28);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 3);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = 0;
x_29 = x_48;
x_30 = x_47;
goto block_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
lean_inc(x_8);
x_50 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_8, x_12, x_13, x_14, x_15, x_16, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unbox(x_51);
lean_dec(x_51);
x_29 = x_53;
x_30 = x_52;
goto block_42;
}
block_42:
{
if (x_29 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5(x_3, x_4, x_5, x_1, x_6, x_7, x_23, x_8, x_27, x_31, x_12, x_13, x_14, x_15, x_16, x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc(x_23);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_23);
x_34 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_8);
x_38 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_8, x_37, x_12, x_13, x_14, x_15, x_16, x_30);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5(x_3, x_4, x_5, x_1, x_6, x_7, x_23, x_8, x_27, x_39, x_12, x_13, x_14, x_15, x_16, x_40);
return x_41;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_26);
if (x_54 == 0)
{
return x_26;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_26, 0);
x_56 = lean_ctor_get(x_26, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_26);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_24);
if (x_58 == 0)
{
return x_24;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_24, 0);
x_60 = lean_ctor_get(x_24, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_24);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("brecOn motive: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
lean_dec(x_10);
x_17 = lean_ctor_get(x_1, 7);
lean_inc(x_17);
lean_inc(x_2);
lean_inc(x_17);
x_18 = lean_array_push(x_17, x_2);
x_19 = 0;
x_20 = 1;
lean_inc(x_12);
x_21 = l_Lean_Meta_mkLambdaFVars(x_18, x_3, x_19, x_20, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_38 = lean_st_ref_get(x_15, x_23);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 3);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get_uint8(x_40, sizeof(void*)*1);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_24 = x_19;
x_25 = x_42;
goto block_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
lean_inc(x_7);
x_44 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_7, x_11, x_12, x_13, x_14, x_15, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unbox(x_45);
lean_dec(x_45);
x_24 = x_47;
x_25 = x_46;
goto block_37;
}
block_37:
{
if (x_24 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6(x_1, x_22, x_17, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_26, x_11, x_12, x_13, x_14, x_15, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc(x_22);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_22);
x_29 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_7);
x_33 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_7, x_32, x_11, x_12, x_13, x_14, x_15, x_25);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6(x_1, x_22, x_17, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_34, x_11, x_12, x_13, x_14, x_15, x_35);
return x_36;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_21);
if (x_48 == 0)
{
return x_21;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_21, 0);
x_50 = lean_ctor_get(x_21, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_21);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; 
lean_dec(x_9);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
if (x_16 == 0)
{
uint8_t x_34; 
x_34 = 0;
x_17 = x_34;
goto block_33;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_levelZero;
x_36 = lean_level_eq(x_8, x_35);
x_17 = x_36;
goto block_33;
}
block_33:
{
if (x_16 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_8, x_18, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_levelZero;
x_21 = lean_level_eq(x_8, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l_Lean_Meta_decLevel(x_8, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_23, x_25, x_10, x_11, x_12, x_13, x_14, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_8, x_31, x_10, x_11, x_12, x_13, x_14, x_15);
return x_32;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("brecOn univ: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__9___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
lean_dec(x_8);
x_15 = 0;
x_16 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_17 = l_Lean_Meta_mkForallFVars(x_1, x_2, x_15, x_16, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_18);
x_20 = l_Lean_Meta_getLevel(x_18, x_10, x_11, x_12, x_13, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_37 = lean_st_ref_get(x_13, x_22);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*1);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_23 = x_15;
x_24 = x_41;
goto block_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
lean_inc(x_7);
x_43 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_7, x_9, x_10, x_11, x_12, x_13, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unbox(x_44);
lean_dec(x_44);
x_23 = x_46;
x_24 = x_45;
goto block_36;
}
block_36:
{
if (x_23 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__8(x_3, x_4, x_18, x_5, x_6, x_1, x_7, x_21, x_25, x_9, x_10, x_11, x_12, x_13, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_21);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_21);
x_28 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__9___closed__2;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_inc(x_7);
x_32 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_7, x_31, x_9, x_10, x_11, x_12, x_13, x_24);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__8(x_3, x_4, x_18, x_5, x_6, x_1, x_7, x_21, x_33, x_9, x_10, x_11, x_12, x_13, x_34);
return x_35;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_20);
if (x_47 == 0)
{
return x_20;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_20, 0);
x_49 = lean_ctor_get(x_20, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_20);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_17);
if (x_51 == 0)
{
return x_17;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_17, 0);
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_17);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fixedParams: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", otherArgs: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_10 = lean_infer_type(x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_headBeta(x_11);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = l_Lean_instInhabitedExpr;
x_17 = lean_array_get(x_16, x_14, x_15);
lean_dec(x_15);
x_18 = lean_array_get_size(x_14);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__6;
x_22 = lean_st_ref_get(x_8, x_12);
if (x_20 == 0)
{
lean_object* x_58; 
lean_dec(x_18);
lean_dec(x_14);
x_58 = l_Lean_Elab_Structural_State_addMatchers___default___closed__1;
x_23 = x_58;
goto block_57;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_le(x_18, x_18);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_18);
lean_dec(x_14);
x_60 = l_Lean_Elab_Structural_State_addMatchers___default___closed__1;
x_23 = x_60;
goto block_57;
}
else
{
size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; 
x_61 = 0;
x_62 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_63 = l_Lean_Elab_Structural_State_addMatchers___default___closed__1;
x_64 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___spec__2(x_2, x_17, x_14, x_61, x_62, x_63);
lean_dec(x_14);
x_23 = x_64;
goto block_57;
}
}
block_57:
{
uint8_t x_24; lean_object* x_25; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_22, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 3);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*1);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_22, 1);
lean_inc(x_50);
lean_dec(x_22);
x_51 = 0;
x_24 = x_51;
x_25 = x_50;
goto block_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_22, 1);
lean_inc(x_52);
lean_dec(x_22);
x_53 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_21, x_4, x_5, x_6, x_7, x_8, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_unbox(x_54);
lean_dec(x_54);
x_24 = x_56;
x_25 = x_55;
goto block_46;
}
block_46:
{
if (x_24 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__9(x_23, x_13, x_2, x_17, x_1, x_3, x_21, x_26, x_4, x_5, x_6, x_7, x_8, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_array_to_list(lean_box(0), x_28);
x_30 = l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_29);
x_31 = l_Lean_MessageData_ofList(x_30);
lean_dec(x_30);
x_32 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__2;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__4;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_23);
x_36 = lean_array_to_list(lean_box(0), x_23);
x_37 = l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_36);
x_38 = l_Lean_MessageData_ofList(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_21, x_41, x_4, x_5, x_6, x_7, x_8, x_25);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__9(x_23, x_13, x_2, x_17, x_1, x_3, x_21, x_43, x_4, x_5, x_6, x_7, x_8, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_10);
if (x_65 == 0)
{
return x_10;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_10, 0);
x_67 = lean_ctor_get(x_10, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_10);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___spec__2(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_8);
return x_16;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_10);
return x_17;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_10);
return x_17;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_9);
lean_dec(x_9);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_19;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_8);
lean_dec(x_8);
x_18 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_4 == x_5;
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; size_t x_10; size_t x_11; 
x_8 = lean_array_uget(x_3, x_4);
x_9 = lean_expr_eqv(x_8, x_2);
x_10 = 1;
x_11 = x_4 + x_10;
if (x_9 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_1, 7);
x_13 = l_Array_contains___at_Lean_Meta_getElimInfo___spec__5(x_12, x_8);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_push(x_6, x_8);
x_4 = x_11;
x_6 = x_14;
goto _start;
}
else
{
lean_dec(x_8);
x_4 = x_11;
goto _start;
}
}
else
{
lean_dec(x_8);
x_4 = x_11;
goto _start;
}
}
else
{
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_1, x_11, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__4;
x_16 = lean_array_push(x_15, x_3);
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_16, x_11, x_13, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_12 = l_Lean_instInhabitedExpr;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get(x_12, x_4, x_13);
lean_dec(x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = lean_infer_type(x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_32 = lean_st_ref_get(x_10, x_17);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 3);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get_uint8(x_34, sizeof(void*)*1);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = 0;
x_18 = x_37;
x_19 = x_36;
goto block_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
lean_inc(x_3);
x_39 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_3, x_6, x_7, x_8, x_9, x_10, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_unbox(x_40);
lean_dec(x_40);
x_18 = x_42;
x_19 = x_41;
goto block_31;
}
block_31:
{
if (x_18 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
x_20 = lean_box(0);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__1(x_1, x_16, x_2, x_20, x_6, x_7, x_8, x_9, x_10, x_19);
lean_dec(x_6);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc(x_16);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_16);
x_23 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_3, x_26, x_6, x_7, x_8, x_9, x_10, x_19);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__1(x_1, x_16, x_2, x_28, x_6, x_7, x_8, x_9, x_10, x_29);
lean_dec(x_6);
lean_dec(x_28);
return x_30;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_15);
if (x_43 == 0)
{
return x_15;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_15, 0);
x_45 = lean_ctor_get(x_15, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_15);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_box(0);
lean_inc(x_13);
x_19 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_18, x_13, x_14, x_15, x_16, x_17);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_instInhabitedExpr;
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get(x_21, x_10, x_22);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_24 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps(x_2, x_3, x_4, x_5, x_12, x_13, x_14, x_15, x_16, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__1___closed__1;
x_28 = lean_array_push(x_27, x_6);
x_29 = lean_array_push(x_28, x_23);
x_30 = l_Array_append___rarg(x_7, x_29);
lean_inc(x_8);
x_31 = l_Array_append___rarg(x_30, x_8);
x_32 = 0;
x_33 = 1;
x_34 = l_Lean_Meta_mkLambdaFVars(x_31, x_25, x_32, x_33, x_13, x_14, x_15, x_16, x_26);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = l_Lean_mkApp(x_9, x_36);
x_38 = l_Lean_mkAppN(x_37, x_8);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = l_Lean_mkApp(x_9, x_39);
x_42 = l_Lean_mkAppN(x_41, x_8);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_9);
lean_dec(x_8);
x_44 = !lean_is_exclusive(x_34);
if (x_44 == 0)
{
return x_34;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_34, 0);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_34);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_48 = !lean_is_exclusive(x_24);
if (x_48 == 0)
{
return x_24;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_24, 0);
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_24);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_2);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__2___boxed), 11, 3);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_3);
x_19 = l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__3___closed__1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_20 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___spec__1___rarg(x_4, x_19, x_18, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_21);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__3___boxed), 17, 9);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_5);
lean_closure_set(x_23, 2, x_6);
lean_closure_set(x_23, 3, x_7);
lean_closure_set(x_23, 4, x_8);
lean_closure_set(x_23, 5, x_2);
lean_closure_set(x_23, 6, x_1);
lean_closure_set(x_23, 7, x_9);
lean_closure_set(x_23, 8, x_10);
x_24 = l_Lean_Meta_forallBoundedTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___spec__1___rarg(x_21, x_19, x_23, x_12, x_13, x_14, x_15, x_16, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; lean_object* x_19; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_11);
x_32 = lean_st_ref_get(x_16, x_17);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 3);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get_uint8(x_34, sizeof(void*)*1);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = 0;
x_18 = x_37;
x_19 = x_36;
goto block_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
lean_inc(x_3);
x_39 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_3, x_12, x_13, x_14, x_15, x_16, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_unbox(x_40);
lean_dec(x_40);
x_18 = x_42;
x_19 = x_41;
goto block_31;
}
block_31:
{
if (x_18 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20, x_12, x_13, x_14, x_15, x_16, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc(x_4);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_4);
x_23 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_3);
x_27 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_3, x_26, x_12, x_13, x_14, x_15, x_16, x_19);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_28, x_12, x_13, x_14, x_15, x_16, x_29);
lean_dec(x_28);
return x_30;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
x_17 = l_Lean_brecOnSuffix;
x_18 = lean_name_mk_string(x_16, x_17);
x_19 = lean_ctor_get(x_1, 5);
lean_inc(x_19);
x_20 = l_Lean_mkConst(x_18, x_19);
x_21 = lean_ctor_get(x_1, 6);
lean_inc(x_21);
x_22 = l_Lean_mkAppN(x_20, x_21);
lean_inc(x_2);
x_23 = l_Lean_mkApp(x_22, x_2);
lean_inc(x_3);
x_24 = l_Lean_mkAppN(x_23, x_3);
lean_inc(x_4);
x_25 = l_Lean_mkApp(x_24, x_4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_25);
x_26 = l_Lean_Meta_check(x_25, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_25);
x_28 = lean_infer_type(x_25, x_11, x_12, x_13, x_14, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_45 = lean_st_ref_get(x_14, x_30);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 3);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = 0;
x_31 = x_50;
x_32 = x_49;
goto block_44;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_dec(x_45);
lean_inc(x_5);
x_52 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_5, x_10, x_11, x_12, x_13, x_14, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_unbox(x_53);
lean_dec(x_53);
x_31 = x_55;
x_32 = x_54;
goto block_44;
}
block_44:
{
if (x_31 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__5(x_3, x_4, x_5, x_29, x_6, x_1, x_2, x_7, x_8, x_25, x_33, x_10, x_11, x_12, x_13, x_14, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc(x_25);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_25);
x_36 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6___closed__2;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_5);
x_40 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_5, x_39, x_10, x_11, x_12, x_13, x_14, x_32);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__5(x_3, x_4, x_5, x_29, x_6, x_1, x_2, x_7, x_8, x_25, x_41, x_10, x_11, x_12, x_13, x_14, x_42);
return x_43;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_28);
if (x_56 == 0)
{
return x_28;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_28, 0);
x_58 = lean_ctor_get(x_28, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_28);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_26);
if (x_60 == 0)
{
return x_26;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_26, 0);
x_62 = lean_ctor_get(x_26, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_26);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
lean_dec(x_8);
x_15 = 0;
x_16 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_17 = l_Lean_Meta_mkForallFVars(x_1, x_2, x_15, x_16, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_3, 7);
lean_inc(x_20);
lean_inc(x_4);
lean_inc(x_20);
x_21 = lean_array_push(x_20, x_4);
lean_inc(x_10);
x_22 = l_Lean_Meta_mkLambdaFVars(x_21, x_18, x_15, x_16, x_10, x_11, x_12, x_13, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_39 = lean_st_ref_get(x_13, x_24);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_25 = x_15;
x_26 = x_43;
goto block_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
lean_inc(x_5);
x_45 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_5, x_9, x_10, x_11, x_12, x_13, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_unbox(x_46);
lean_dec(x_46);
x_25 = x_48;
x_26 = x_47;
goto block_38;
}
block_38:
{
if (x_25 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__6(x_3, x_23, x_20, x_4, x_5, x_6, x_7, x_1, x_27, x_9, x_10, x_11, x_12, x_13, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_23);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_23);
x_30 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_5);
x_34 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_5, x_33, x_9, x_10, x_11, x_12, x_13, x_26);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__6(x_3, x_23, x_20, x_4, x_5, x_6, x_7, x_1, x_35, x_9, x_10, x_11, x_12, x_13, x_36);
return x_37;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_22);
if (x_49 == 0)
{
return x_22;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_22, 0);
x_51 = lean_ctor_get(x_22, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_22);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_17);
if (x_53 == 0)
{
return x_17;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_17, 0);
x_55 = lean_ctor_get(x_17, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_17);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_10 = lean_infer_type(x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_headBeta(x_11);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = l_Lean_instInhabitedExpr;
x_17 = lean_array_get(x_16, x_14, x_15);
lean_dec(x_15);
x_18 = lean_array_get_size(x_14);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__6;
x_22 = lean_st_ref_get(x_8, x_12);
if (x_20 == 0)
{
lean_object* x_58; 
lean_dec(x_18);
lean_dec(x_14);
x_58 = l_Lean_Elab_Structural_State_addMatchers___default___closed__1;
x_23 = x_58;
goto block_57;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_le(x_18, x_18);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_18);
lean_dec(x_14);
x_60 = l_Lean_Elab_Structural_State_addMatchers___default___closed__1;
x_23 = x_60;
goto block_57;
}
else
{
size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; 
x_61 = 0;
x_62 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_63 = l_Lean_Elab_Structural_State_addMatchers___default___closed__1;
x_64 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___spec__1(x_2, x_17, x_14, x_61, x_62, x_63);
lean_dec(x_14);
x_23 = x_64;
goto block_57;
}
}
block_57:
{
uint8_t x_24; lean_object* x_25; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_22, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 3);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*1);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_22, 1);
lean_inc(x_50);
lean_dec(x_22);
x_51 = 0;
x_24 = x_51;
x_25 = x_50;
goto block_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_22, 1);
lean_inc(x_52);
lean_dec(x_22);
x_53 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_21, x_4, x_5, x_6, x_7, x_8, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_unbox(x_54);
lean_dec(x_54);
x_24 = x_56;
x_25 = x_55;
goto block_46;
}
block_46:
{
if (x_24 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__7(x_23, x_13, x_2, x_17, x_21, x_1, x_3, x_26, x_4, x_5, x_6, x_7, x_8, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_array_to_list(lean_box(0), x_28);
x_30 = l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_29);
x_31 = l_Lean_MessageData_ofList(x_30);
lean_dec(x_30);
x_32 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__2;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__4;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_23);
x_36 = lean_array_to_list(lean_box(0), x_23);
x_37 = l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_36);
x_38 = l_Lean_MessageData_ofList(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_21, x_41, x_4, x_5, x_6, x_7, x_8, x_25);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__7(x_23, x_13, x_2, x_17, x_21, x_1, x_3, x_43, x_4, x_5, x_6, x_7, x_8, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_10);
if (x_65 == 0)
{
return x_10;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_10, 0);
x_67 = lean_ctor_get(x_10, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_10);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__3___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_11);
lean_dec(x_10);
return x_18;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__4___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_11);
return x_18;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__5___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
uint8_t l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_shouldBetaReduce(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isHeadBetaTarget(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_containsRecFn___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_Lean_Expr_getAppFn(x_1);
x_7 = 8192;
x_8 = l_Lean_Expr_FindImpl_initCache;
x_9 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_5, x_7, x_6, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_10);
x_12 = 1;
return x_12;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_shouldBetaReduce___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_shouldBetaReduce(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_shouldBetaReduce(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Expr_headBeta(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___lambda__2___boxed), 4, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___lambda__1___boxed), 5, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___closed__1;
x_8 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_1, x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_1);
x_13 = lean_st_ref_set(x_6, x_9, x_10);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_9, 1);
x_21 = lean_ctor_get(x_9, 2);
x_22 = lean_ctor_get(x_9, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_23, 3, x_22);
x_24 = lean_st_ref_set(x_6, x_23, x_10);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
x_18 = lean_ctor_get(x_3, 4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
x_19 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_1);
lean_ctor_set(x_19, 4, x_18);
lean_ctor_set(x_19, 5, x_13);
lean_ctor_set_uint8(x_19, sizeof(void*)*6, x_15);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*6);
x_24 = lean_ctor_get(x_3, 1);
x_25 = lean_ctor_get(x_3, 2);
x_26 = lean_ctor_get(x_3, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
x_27 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_1);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set(x_27, 5, x_20);
lean_ctor_set_uint8(x_27, sizeof(void*)*6, x_23);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = 0;
x_13 = 1;
lean_inc(x_7);
x_14 = l_Lean_Meta_mkLambdaFVars(x_1, x_5, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_31 = lean_st_ref_get(x_10, x_16);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*1);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_17 = x_12;
x_18 = x_35;
goto block_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
lean_inc(x_4);
x_37 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_4, x_6, x_7, x_8, x_9, x_10, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_unbox(x_38);
lean_dec(x_38);
x_17 = x_40;
x_18 = x_39;
goto block_30;
}
block_30:
{
if (x_17 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_19 = lean_box(0);
x_20 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__1(x_2, x_15, x_3, x_19, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_15);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_15);
x_22 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_4, x_25, x_6, x_7, x_8, x_9, x_10, x_18);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__1(x_2, x_15, x_3, x_27, x_6, x_7, x_8, x_9, x_10, x_28);
lean_dec(x_6);
lean_dec(x_27);
return x_29;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
return x_14;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_14, 0);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_14);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_14 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn(x_2, x_6, x_5, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2(x_1, x_2, x_3, x_4, x_15, x_7, x_8, x_9, x_10, x_11, x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_22 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkIndPredBRecOn(x_2, x_6, x_5, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2(x_1, x_2, x_3, x_4, x_23, x_7, x_8, x_9, x_10, x_11, x_24);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__3___boxed), 12, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_5);
lean_inc(x_6);
x_15 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg(x_6, x_1, x_14, x_6, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("numFixed: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_dec(x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix(x_1, x_2, x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_32 = lean_st_ref_get(x_11, x_15);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 3);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get_uint8(x_34, sizeof(void*)*1);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = 0;
x_16 = x_37;
x_17 = x_36;
goto block_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
lean_inc(x_5);
x_39 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_5, x_7, x_8, x_9, x_10, x_11, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_unbox(x_40);
lean_dec(x_40);
x_16 = x_42;
x_17 = x_41;
goto block_31;
}
block_31:
{
if (x_16 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__4(x_2, x_1, x_4, x_5, x_3, x_14, x_18, x_7, x_8, x_9, x_10, x_11, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc(x_14);
x_20 = l_Nat_repr(x_14);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__5___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_5);
x_27 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_5, x_26, x_7, x_8, x_9, x_10, x_11, x_17);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__4(x_2, x_1, x_4, x_5, x_3, x_14, x_28, x_7, x_8, x_9, x_10, x_11, x_29);
lean_dec(x_28);
return x_30;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" :=\n");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = l_Lean_Elab_addAsAxiom(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_12);
x_13 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess(x_3, x_12, x_7, x_8, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__6;
x_40 = lean_st_ref_get(x_8, x_15);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*1);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = 0;
x_17 = x_45;
x_18 = x_44;
goto block_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec(x_40);
x_47 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__10(x_16, x_4, x_5, x_6, x_7, x_8, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_unbox(x_48);
lean_dec(x_48);
x_17 = x_50;
x_18 = x_49;
goto block_39;
}
block_39:
{
if (x_17 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__5(x_12, x_2, x_14, x_1, x_16, x_19, x_4, x_5, x_6, x_7, x_8, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc(x_12);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_12);
x_22 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_2);
x_26 = lean_array_to_list(lean_box(0), x_2);
x_27 = l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_26);
x_28 = l_Lean_MessageData_ofList(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__4;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_inc(x_14);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_14);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_22);
x_35 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9(x_16, x_34, x_4, x_5, x_6, x_7, x_8, x_18);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__5(x_12, x_2, x_14, x_1, x_16, x_36, x_4, x_5, x_6, x_7, x_8, x_37);
return x_38;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
return x_13;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_13, 0);
x_53 = lean_ctor_get(x_13, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_13);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_10);
if (x_55 == 0)
{
return x_10;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_10, 0);
x_57 = lean_ctor_get(x_10, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_10);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 5);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6), 9, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_st_ref_get(x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__11___rarg(x_8, x_9, x_2, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___spec__1(x_13, x_2, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___spec__1(x_13, x_2, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
return x_14;
}
}
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(x_1);
x_6 = lean_apply_2(x_4, x_5, x_2);
return x_6;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(x_1);
x_8 = lean_apply_2(x_4, x_7, x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_4 < x_3;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = x_5;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_5, x_4);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_5, x_4, x_15);
x_17 = x_14;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = x_4 + x_21;
x_23 = x_19;
x_24 = lean_array_uset(x_16, x_4, x_23);
x_4 = x_22;
x_5 = x_24;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__2___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_array_set(x_4, x_5, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
lean_dec(x_5);
x_3 = x_11;
x_4 = x_13;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_4);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = x_4;
x_23 = lean_box_usize(x_21);
x_24 = l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__2___boxed__const__1;
x_25 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__1___boxed), 10, 5);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_23);
lean_closure_set(x_25, 3, x_24);
lean_closure_set(x_25, 4, x_22);
x_26 = x_25;
x_27 = lean_apply_5(x_26, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l_Lean_mkAppN(x_18, x_29);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = l_Lean_mkAppN(x_18, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_18);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_17);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_4 < x_3;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = x_5;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_5, x_4);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_5, x_4, x_15);
x_17 = x_14;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = x_4 + x_21;
x_23 = x_19;
x_24 = lean_array_uset(x_16, x_4, x_23);
x_4 = x_22;
x_5 = x_24;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__4___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_array_set(x_4, x_5, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
lean_dec(x_5);
x_3 = x_11;
x_4 = x_13;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_4);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = x_4;
x_23 = lean_box_usize(x_21);
x_24 = l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__4___boxed__const__1;
x_25 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__3___boxed), 10, 5);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_23);
lean_closure_set(x_25, 3, x_24);
lean_closure_set(x_25, 4, x_22);
x_26 = x_25;
x_27 = lean_apply_5(x_26, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l_Lean_mkAppN(x_18, x_29);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = l_Lean_mkAppN(x_18, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_18);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_17);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
lean_inc(x_2);
x_12 = lean_apply_1(x_1, x_2);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_array_get_size(x_3);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Array_toSubarray___rarg(x_3, x_4, x_14);
x_16 = l_Array_ofSubarray___rarg(x_15);
x_17 = 0;
x_18 = 1;
lean_inc(x_7);
x_19 = l_Lean_Meta_mkLambdaFVars(x_16, x_2, x_17, x_18, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_mkIdRhs(x_20, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_toSubarray___rarg(x_3, x_25, x_4);
x_27 = l_Array_ofSubarray___rarg(x_26);
x_28 = l_Lean_Meta_mkLambdaFVars(x_27, x_23, x_17, x_18, x_7, x_8, x_9, x_10, x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_37 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_5, x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = 0;
x_41 = 1;
x_42 = l_Lean_Meta_mkLambdaFVars(x_3, x_38, x_40, x_41, x_7, x_8, x_9, x_10, x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
return x_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_37, 0);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_37);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_6);
x_14 = lean_nat_dec_le(x_2, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_indentExpr(x_4);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_indentExpr(x_5);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_23, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_5);
lean_dec(x_4);
x_29 = lean_box(0);
x_30 = l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__5___lambda__1(x_1, x_7, x_6, x_2, x_3, x_29, x_8, x_9, x_10, x_11, x_12);
return x_30;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_5 < x_4;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_6;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_array_uget(x_6, x_5);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_6, x_5, x_16);
x_18 = x_15;
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
lean_inc(x_19);
lean_inc(x_1);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__5___lambda__2), 12, 5);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, x_1);
lean_closure_set(x_21, 3, x_19);
lean_closure_set(x_21, 4, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__2___rarg(x_19, x_21, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = x_5 + x_25;
x_27 = x_23;
x_28 = lean_array_uset(x_17, x_5, x_27);
x_5 = x_26;
x_6 = x_28;
x_11 = x_24;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 0;
x_14 = 1;
x_15 = l_Lean_Meta_mkLambdaFVars(x_3, x_11, x_13, x_14, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 0;
x_14 = 1;
x_15 = l_Lean_Meta_mkForallFVars(x_3, x_11, x_13, x_14, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_expr_instantiate1(x_1, x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__4;
x_15 = lean_array_push(x_14, x_4);
x_16 = 0;
x_17 = 1;
x_18 = l_Lean_Meta_mkLambdaFVars(x_15, x_12, x_16, x_17, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_3);
x_9 = l_Lean_Meta_matchMatcherApp_x3f(x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
lean_inc(x_3);
x_12 = lean_apply_1(x_1, x_3);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Expr_getAppNumArgsAux(x_3, x_14);
x_16 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1;
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
x_20 = l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__2(x_1, x_2, x_3, x_17, x_19, x_4, x_5, x_6, x_7, x_11);
return x_20;
}
else
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Expr_getAppNumArgsAux(x_3, x_21);
x_23 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1;
lean_inc(x_22);
x_24 = lean_mk_array(x_22, x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_22, x_25);
lean_dec(x_22);
x_27 = l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__4(x_1, x_2, x_3, x_24, x_26, x_4, x_5, x_6, x_7, x_11);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_10, 0);
lean_inc(x_28);
lean_dec(x_10);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_ctor_get(x_28, 2);
x_33 = lean_ctor_get(x_28, 3);
x_34 = lean_ctor_get(x_28, 4);
x_35 = lean_ctor_get(x_28, 5);
x_36 = lean_ctor_get(x_28, 6);
x_37 = lean_ctor_get(x_28, 7);
x_38 = lean_ctor_get(x_28, 8);
x_39 = l_Array_zip___rarg(x_37, x_36);
lean_dec(x_37);
x_40 = lean_array_get_size(x_39);
x_41 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_42 = x_39;
x_43 = lean_box_usize(x_41);
x_44 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___boxed__const__1;
x_45 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__5___boxed), 11, 6);
lean_closure_set(x_45, 0, x_1);
lean_closure_set(x_45, 1, x_2);
lean_closure_set(x_45, 2, x_3);
lean_closure_set(x_45, 3, x_43);
lean_closure_set(x_45, 4, x_44);
lean_closure_set(x_45, 5, x_42);
x_46 = x_45;
x_47 = lean_apply_5(x_46, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_ctor_set(x_28, 7, x_49);
x_50 = l_Lean_Meta_MatcherApp_toExpr(x_28);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_47);
lean_ctor_set(x_28, 7, x_51);
x_53 = l_Lean_Meta_MatcherApp_toExpr(x_28);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_free_object(x_28);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_55 = !lean_is_exclusive(x_47);
if (x_55 == 0)
{
return x_47;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_47, 0);
x_57 = lean_ctor_get(x_47, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_47);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_59 = lean_ctor_get(x_28, 0);
x_60 = lean_ctor_get(x_28, 1);
x_61 = lean_ctor_get(x_28, 2);
x_62 = lean_ctor_get(x_28, 3);
x_63 = lean_ctor_get(x_28, 4);
x_64 = lean_ctor_get(x_28, 5);
x_65 = lean_ctor_get(x_28, 6);
x_66 = lean_ctor_get(x_28, 7);
x_67 = lean_ctor_get(x_28, 8);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_28);
x_68 = l_Array_zip___rarg(x_66, x_65);
lean_dec(x_66);
x_69 = lean_array_get_size(x_68);
x_70 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_71 = x_68;
x_72 = lean_box_usize(x_70);
x_73 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___boxed__const__1;
x_74 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__5___boxed), 11, 6);
lean_closure_set(x_74, 0, x_1);
lean_closure_set(x_74, 1, x_2);
lean_closure_set(x_74, 2, x_3);
lean_closure_set(x_74, 3, x_72);
lean_closure_set(x_74, 4, x_73);
lean_closure_set(x_74, 5, x_71);
x_75 = x_74;
x_76 = lean_apply_5(x_75, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_80, 0, x_59);
lean_ctor_set(x_80, 1, x_60);
lean_ctor_set(x_80, 2, x_61);
lean_ctor_set(x_80, 3, x_62);
lean_ctor_set(x_80, 4, x_63);
lean_ctor_set(x_80, 5, x_64);
lean_ctor_set(x_80, 6, x_65);
lean_ctor_set(x_80, 7, x_77);
lean_ctor_set(x_80, 8, x_67);
x_81 = l_Lean_Meta_MatcherApp_toExpr(x_80);
if (lean_is_scalar(x_79)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_79;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
x_83 = lean_ctor_get(x_76, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_76, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_85 = x_76;
} else {
 lean_dec_ref(x_76);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
}
}
case 6:
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lambda__1), 9, 2);
lean_closure_set(x_87, 0, x_1);
lean_closure_set(x_87, 1, x_2);
x_88 = l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__2___rarg(x_3, x_87, x_4, x_5, x_6, x_7, x_8);
return x_88;
}
case 7:
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lambda__2), 9, 2);
lean_closure_set(x_89, 0, x_1);
lean_closure_set(x_89, 1, x_2);
x_90 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_3, x_89, x_4, x_5, x_6, x_7, x_8);
return x_90;
}
case 8:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_3, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_3, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_3, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_3, 3);
lean_inc(x_94);
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_95 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_93, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lambda__3___boxed), 9, 3);
lean_closure_set(x_98, 0, x_94);
lean_closure_set(x_98, 1, x_1);
lean_closure_set(x_98, 2, x_2);
x_99 = l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__2___rarg(x_91, x_92, x_96, x_98, x_4, x_5, x_6, x_7, x_97);
return x_99;
}
else
{
uint8_t x_100; 
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_95);
if (x_100 == 0)
{
return x_95;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_95, 0);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_95);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
case 10:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_3, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_3, 1);
lean_inc(x_105);
lean_dec(x_3);
x_106 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_105, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_106) == 0)
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = l_Lean_mkMData(x_104, x_108);
lean_ctor_set(x_106, 0, x_109);
return x_106;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_106, 0);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_106);
x_112 = l_Lean_mkMData(x_104, x_110);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_104);
x_114 = !lean_is_exclusive(x_106);
if (x_114 == 0)
{
return x_106;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_106, 0);
x_116 = lean_ctor_get(x_106, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_106);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
case 11:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_3, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_3, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_3, 2);
lean_inc(x_120);
lean_dec(x_3);
x_121 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_1, x_2, x_120, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = l_Lean_mkProj(x_118, x_119, x_123);
lean_ctor_set(x_121, 0, x_124);
return x_121;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_121, 0);
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_121);
x_127 = l_Lean_mkProj(x_118, x_119, x_125);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
uint8_t x_129; 
lean_dec(x_119);
lean_dec(x_118);
x_129 = !lean_is_exclusive(x_121);
if (x_129 == 0)
{
return x_121;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_121, 0);
x_131 = lean_ctor_get(x_121, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_121);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
default: 
{
lean_object* x_133; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_3);
lean_ctor_set(x_133, 1, x_8);
return x_133;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__3(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__5(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
uint8_t l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isConst(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Expr_constName_x21(x_2);
x_6 = l_Lean_NameSet_contains(x_1, x_5);
lean_dec(x_5);
return x_6;
}
}
}
uint8_t l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Expr_getAppFn(x_2);
x_4 = l_Lean_Expr_isConst(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Expr_constName_x21(x_3);
lean_dec(x_3);
x_7 = l_Lean_NameSet_contains(x_1, x_6);
lean_dec(x_6);
return x_7;
}
}
}
uint8_t l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8192;
x_4 = l_Lean_Expr_FindImpl_initCache;
x_5 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 1;
return x_8;
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_addSmartUnfoldingDefAux___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 0;
x_4 = l_Lean_Elab_Structural_State_addMatchers___default___closed__1;
x_5 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 3, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__2___boxed), 2, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__3___boxed), 2, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 4);
x_16 = lean_ctor_get(x_1, 5);
x_17 = lean_ctor_get(x_1, 2);
lean_dec(x_17);
x_18 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_9, x_10, x_16, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lean_Meta_smartUnfoldingSuffix;
x_22 = lean_name_mk_string(x_14, x_21);
x_23 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux___closed__1;
lean_ctor_set(x_1, 5, x_20);
lean_ctor_set(x_1, 3, x_22);
lean_ctor_set(x_1, 2, x_23);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = l_Lean_Meta_smartUnfoldingSuffix;
x_27 = lean_name_mk_string(x_14, x_26);
x_28 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux___closed__1;
lean_ctor_set(x_1, 5, x_24);
lean_ctor_set(x_1, 3, x_27);
lean_ctor_set(x_1, 2, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_free_object(x_1);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 3);
x_38 = lean_ctor_get(x_1, 4);
x_39 = lean_ctor_get(x_1, 5);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_34);
lean_dec(x_1);
x_40 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit(x_9, x_10, x_39, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = l_Lean_Meta_smartUnfoldingSuffix;
x_45 = lean_name_mk_string(x_37, x_44);
x_46 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux___closed__1;
x_47 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_47, 3, x_45);
lean_ctor_set(x_47, 4, x_38);
lean_ctor_set(x_47, 5, x_41);
lean_ctor_set_uint8(x_47, sizeof(void*)*6, x_35);
if (lean_is_scalar(x_43)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_43;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_34);
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
}
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux___lambda__3(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Meta_isProp(x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Elab_Structural_addSmartUnfoldingDefAux(x_1, x_15, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 0;
x_20 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_17, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_11, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_11, 0, x_27);
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_dec(x_11);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
return x_11;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_11);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* l_Lean_Elab_Structural_structuralRecursion_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Structural_structuralRecursion_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_structuralRecursion_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 == x_3;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = lean_apply_5(x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = x_2 + x_17;
x_2 = x_18;
x_4 = x_15;
x_11 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_structuralRecursion___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structural recursion failed, produced type incorrect term");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_structuralRecursion___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Structural_structuralRecursion___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Structural_structuralRecursion___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_indentD(x_1);
x_3 = l_Lean_Elab_Structural_structuralRecursion___lambda__1___closed__2;
x_4 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6;
x_6 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Structural_structuralRecursion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structural recursion does not handle mutually recursive functions");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_structuralRecursion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Structural_structuralRecursion___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Structural_structuralRecursion___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = l_Lean_Elab_Structural_State_addMatchers___default___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Structural_structuralRecursion___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_structuralRecursion___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = l_Lean_Elab_Structural_structuralRecursion___closed__2;
x_13 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = l_Lean_Elab_instInhabitedPreDefinition;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get(x_14, x_1, x_15);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion), 7, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = l_Lean_Elab_Structural_structuralRecursion___closed__3;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_run___rarg(x_17, x_18, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_array_get_size(x_24);
x_26 = lean_nat_dec_lt(x_15, x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
x_27 = x_21;
goto block_43;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_25, x_25);
if (x_44 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
x_27 = x_21;
goto block_43;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = 0;
x_46 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_47 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_48 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__1(x_24, x_45, x_46, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_24);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_27 = x_49;
goto block_43;
}
else
{
uint8_t x_50; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_48);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
block_43:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc(x_3);
lean_inc(x_2);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_addNonRec), 8, 3);
lean_closure_set(x_28, 0, x_22);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_3);
x_29 = l_Lean_Elab_Structural_structuralRecursion___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_30 = l_Lean_Meta_mapErrorImp___rarg(x_28, x_29, x_4, x_5, x_6, x_7, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_32 = l_Lean_Elab_addAndCompilePartialRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Elab_Structural_addSmartUnfoldingDef(x_16, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_33);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_30, 0);
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_30);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_19);
if (x_54 == 0)
{
return x_19;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_19, 0);
x_56 = lean_ctor_get(x_19, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_19);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Lean_Elab_Structural_initFn____x40_Lean_Elab_PreDefinition_Structural___hyg_7232_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__6;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_ForEachExpr(lean_object*);
lean_object* initialize_Lean_Meta_ForEachExpr(lean_object*);
lean_object* initialize_Lean_Meta_RecursorInfo(lean_object*);
lean_object* initialize_Lean_Meta_Match_Match(lean_object*);
lean_object* initialize_Lean_Meta_Transform(lean_object*);
lean_object* initialize_Lean_Meta_IndPredBelow(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_PreDefinition_Structural(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ForEachExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ForEachExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_RecursorInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Match(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IndPredBelow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_hasBadIndexDep_x3f___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwStructuralFailed___rarg___closed__2);
l_Lean_Elab_Structural_State_matcherBelowDep___default = _init_l_Lean_Elab_Structural_State_matcherBelowDep___default();
lean_mark_persistent(l_Lean_Elab_Structural_State_matcherBelowDep___default);
l_Lean_Elab_Structural_State_addMatchers___default___closed__1 = _init_l_Lean_Elab_Structural_State_addMatchers___default___closed__1();
lean_mark_persistent(l_Lean_Elab_Structural_State_addMatchers___default___closed__1);
l_Lean_Elab_Structural_State_addMatchers___default = _init_l_Lean_Elab_Structural_State_addMatchers___default();
lean_mark_persistent(l_Lean_Elab_Structural_State_addMatchers___default);
l_Lean_Elab_Structural_instInhabitedM___closed__1 = _init_l_Lean_Elab_Structural_instInhabitedM___closed__1();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedM___closed__1);
l_Lean_Elab_Structural_instInhabitedM___closed__2 = _init_l_Lean_Elab_Structural_instInhabitedM___closed__2();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedM___closed__2);
l_Lean_Elab_Structural_instInhabitedM___closed__3 = _init_l_Lean_Elab_Structural_instInhabitedM___closed__3();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedM___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27___rarg___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_orelse_x27___rarg___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__3 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__3);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__4 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___spec__2___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__5);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___lambda__1___closed__6);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__5);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__6);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__7 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__7);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__8 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__8);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__9 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__9);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__10 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__10);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__11 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__11);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__12 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__12();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__12);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__13 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__13();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__13);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__14 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__14();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__14);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__15 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__15();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__15);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__16 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__16();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__16);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__17 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__17();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_findRecArg_loop___rarg___closed__17);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_ensureNoRecFn___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_throwToBelowFailed___rarg___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux_match__2___rarg___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__5);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__6);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__7 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__7);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__8 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__8);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__9 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__9);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__10 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__10);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__11 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___lambda__5___closed__11);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__5);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__6);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__7 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__7);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__8 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__8);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__9 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__9);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__10 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_toBelowAux___closed__10);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2___closed__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2___closed__1);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2___closed__2 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__2___closed__2);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__3___closed__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___lambda__3___closed__1);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___closed__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___closed__1);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___closed__2 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___spec__1___rarg___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_withBelowDict___rarg___closed__2);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__2___closed__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__2___closed__1);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__2___closed__2 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___lambda__2___closed__2);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___closed__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___closed__1);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___closed__2 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___closed__2);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__5___boxed__const__1);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__8___boxed__const__1);
l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__1 = _init_l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__1);
l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__2 = _init_l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__2);
l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__3 = _init_l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__3();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__3);
l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__4 = _init_l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__4();
lean_mark_persistent(l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__9___closed__4);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__3 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__3);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__4 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__2___closed__4);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__3 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__3);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__4 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___spec__12___lambda__3___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__1___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2___boxed__const__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___lambda__2___boxed__const__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___closed__2);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___closed__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___closed__1);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___closed__2 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___closed__2);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__2___boxed__const__1);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__4___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__4___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__4___boxed__const__1);
l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__6___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__6___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__6___boxed__const__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lambda__2___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__3___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__5___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__6___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__7___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__9___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__9___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__9___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__9___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__9___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___lambda__9___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_mkBRecOn___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_preprocess___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__5___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__5___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__5___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__5___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__5___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__5___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__6___closed__4);
l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__2___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__2___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__2___boxed__const__1);
l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__4___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__4___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___spec__4___boxed__const__1);
l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___boxed__const__1 = _init_l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Structural_addSmartUnfoldingDefAux_visit___boxed__const__1);
l_Lean_Elab_Structural_addSmartUnfoldingDefAux___closed__1 = _init_l_Lean_Elab_Structural_addSmartUnfoldingDefAux___closed__1();
lean_mark_persistent(l_Lean_Elab_Structural_addSmartUnfoldingDefAux___closed__1);
l_Lean_Elab_Structural_structuralRecursion___lambda__1___closed__1 = _init_l_Lean_Elab_Structural_structuralRecursion___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Structural_structuralRecursion___lambda__1___closed__1);
l_Lean_Elab_Structural_structuralRecursion___lambda__1___closed__2 = _init_l_Lean_Elab_Structural_structuralRecursion___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Structural_structuralRecursion___lambda__1___closed__2);
l_Lean_Elab_Structural_structuralRecursion___closed__1 = _init_l_Lean_Elab_Structural_structuralRecursion___closed__1();
lean_mark_persistent(l_Lean_Elab_Structural_structuralRecursion___closed__1);
l_Lean_Elab_Structural_structuralRecursion___closed__2 = _init_l_Lean_Elab_Structural_structuralRecursion___closed__2();
lean_mark_persistent(l_Lean_Elab_Structural_structuralRecursion___closed__2);
l_Lean_Elab_Structural_structuralRecursion___closed__3 = _init_l_Lean_Elab_Structural_structuralRecursion___closed__3();
lean_mark_persistent(l_Lean_Elab_Structural_structuralRecursion___closed__3);
l_Lean_Elab_Structural_structuralRecursion___closed__4 = _init_l_Lean_Elab_Structural_structuralRecursion___closed__4();
lean_mark_persistent(l_Lean_Elab_Structural_structuralRecursion___closed__4);
res = l_Lean_Elab_Structural_initFn____x40_Lean_Elab_PreDefinition_Structural___hyg_7232_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
