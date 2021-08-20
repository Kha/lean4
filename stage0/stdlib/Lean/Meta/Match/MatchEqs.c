// Lean compiler output
// Module: Lean.Meta.Match.MatchEqs
// Imports: Init Lean.Meta.Match.Match Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Delta Lean.Meta.Tactic.SplitIf
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
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__1;
lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__1;
lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq_match__1(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_Expr_isCharLit(lean_object*);
uint8_t l_Lean_Expr_isNatLit(lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_match__3(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__3;
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__5;
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__3;
lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3___boxed(lean_object**);
lean_object* l_Lean_Meta_trySubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Meta_Match_mkEquationsFor_simpEq___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_dependsOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_proveLoop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq_match__2(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___closed__2;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_match__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor___closed__4;
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__7;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_prove___closed__6;
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2___closed__2;
static lean_object* l_Lean_Meta_Match_mkEquationsFor___closed__2;
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___closed__1;
lean_object* l_Lean_throwError___at_Lean_Meta_Match_mkEquationsFor_proveLoop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMapM___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___boxed(lean_object**);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Meta_Match_mkEquationsFor_prove___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor___closed__1;
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__1;
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__4;
lean_object* l_Lean_throwError___at_Lean_Meta_Match_mkEquationsFor_proveLoop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__3;
lean_object* l_Lean_Meta_Match_mkEquationsFor_match__4___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_prove___closed__4;
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_match__1(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__11;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__2;
static lean_object* l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__5;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Meta_Match_mkEquationsFor_simpEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop_match__1(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq_match__3(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_match__4(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxLemma___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applyRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1;
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1___closed__1;
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__6;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_proveLoop___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__2;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__4;
lean_object* l_Lean_Meta_Match_mkEquationsFor_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpHs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCtorIfLit(lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2___boxed(lean_object**);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq_match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__6;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__9;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq_match__2___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__4;
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq_match__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2___closed__1;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__8;
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__2;
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___spec__1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__10;
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchValue(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_contradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_match__2(lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__6;
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__1;
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__7;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__5;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_prove___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq_match__4(lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__1;
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__5___boxed(lean_object**);
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__1;
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg___closed__2;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__2;
lean_object* l_Lean_Meta_getMatcherInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_prove(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__4;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__4;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3___closed__2;
lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_prove___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___boxed__const__1;
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpHs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMapM___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpIfTarget(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__8;
lean_object* l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitIfTarget_x3f___spec__1___at_Lean_Meta_splitIfTarget_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4___closed__2;
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4___boxed(lean_object**);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_arrayLit_x3f(lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_prove___closed__2;
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpHs_match__1(lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__6;
uint8_t l_Lean_Expr_isStringLit(lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__3;
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__5;
lean_object* l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg___closed__1;
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___closed__2;
lean_object* l_Lean_Meta_withLCtx___at_Lean_Meta_ppGoal___spec__15___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor_simpEq___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__5;
static lean_object* l_Lean_Meta_Match_mkEquationsFor___lambda__1___closed__1;
lean_object* l_Lean_throwError___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
lean_object* l_Lean_Meta_deltaTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor_simpEq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_prove___closed__5;
lean_object* l_List_map___at_Lean_mkConstWithLevelParams___spec__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor___closed__3;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_prove___closed__7;
lean_object* l_Lean_Meta_modifyTargetEqLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed(lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__3;
static lean_object* l_Lean_Meta_Match_mkEquationsFor_prove___closed__1;
static lean_object* l_Lean_Meta_Match_mkEquationsFor_prove___closed__3;
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchValue___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___closed__1;
uint8_t l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchValue(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isNatLit(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isCharLit(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_Expr_isStringLit(x_1);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchValue___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchValue(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_3(x_2, x_7, x_8, x_9);
return x_10;
}
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'casesOnStuckLHS' failed");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg___closed__2;
x_7 = l_Lean_throwError___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___spec__1___rarg(x_6, x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = 1;
x_13 = x_2 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_8, x_2, x_14);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Expr_fvarId_x21(x_1);
x_10 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1;
x_11 = l_Lean_Meta_Cases_cases(x_2, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = x_13;
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___spec__1(x_15, x_16, x_17);
x_19 = x_18;
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_array_get_size(x_20);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = 0;
x_25 = x_20;
x_26 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___spec__1(x_23, x_24, x_25);
x_27 = x_26;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
else
{
uint8_t x_29; 
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
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_4);
x_10 = l_Lean_RecursorVal_getMajorIdx(x_1);
lean_dec(x_1);
x_11 = l_Lean_instInhabitedExpr;
x_12 = lean_array_get(x_11, x_2, x_10);
lean_dec(x_10);
lean_dec(x_2);
x_13 = l_Lean_Expr_isFVar(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_3);
x_14 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg(x_5, x_6, x_7, x_8, x_9);
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
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1(x_12, x_3, x_19, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
return x_20;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_getMVarType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Meta_matchEq_x3f(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg(x_2, x_3, x_4, x_5, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_getAppFn(x_17);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_5, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_environment_find(x_23, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec(x_17);
lean_dec(x_1);
x_25 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg(x_2, x_3, x_4, x_5, x_22);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
if (lean_obj_tag(x_26) == 7)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_Expr_getAppNumArgsAux(x_17, x_28);
x_30 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___closed__1;
lean_inc(x_29);
x_31 = lean_mk_array(x_29, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_29, x_32);
lean_dec(x_29);
x_34 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_17, x_31, x_33);
x_35 = lean_array_get_size(x_34);
x_36 = l_Lean_RecursorVal_getMajorIdx(x_27);
x_37 = lean_nat_dec_le(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__2(x_27, x_34, x_1, x_38, x_2, x_3, x_4, x_5, x_22);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_34);
lean_dec(x_27);
lean_dec(x_1);
x_40 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg(x_2, x_3, x_4, x_5, x_22);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_1);
x_45 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg(x_2, x_3, x_4, x_5, x_22);
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_46 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg(x_2, x_3, x_4, x_5, x_16);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_10);
if (x_47 == 0)
{
return x_10;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_10, 0);
x_49 = lean_ctor_get(x_10, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_7);
if (x_51 == 0)
{
return x_7;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_7, 0);
x_53 = lean_ctor_get(x_7, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_7);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___spec__1(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkEquationsFor_simpEq_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkEquationsFor_simpEq_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_2(x_4, x_1, x_2);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_6);
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_apply_4(x_3, x_9, x_10, x_11, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkEquationsFor_simpEq_match__3___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_2(x_4, x_1, x_2);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_6);
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_apply_4(x_3, x_9, x_10, x_11, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkEquationsFor_simpEq_match__4___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpHs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpHs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkEquationsFor_simpHs_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkEquationsFor_proveLoop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_Match_mkEquationsFor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkEquationsFor_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_Match_mkEquationsFor_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkEquationsFor_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_match__3___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_Match_mkEquationsFor_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkEquationsFor_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_Match_mkEquationsFor_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkEquationsFor_match__4___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Unit");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unit");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__2;
x_2 = l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__6;
x_2 = l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1;
x_2 = l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_instInhabitedExpr;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get(x_7, x_1, x_8);
x_10 = lean_infer_type(x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_array_get_size(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_inc(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__2;
x_18 = l_Lean_Expr_isConstOf(x_12, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
lean_object* x_19; 
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
else
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__8;
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_array_get_size(x_1);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
lean_inc(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__2;
x_29 = l_Lean_Expr_isConstOf(x_21, x_28);
lean_dec(x_21);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_inc(x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_22);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_32 = l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__8;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_22);
return x_33;
}
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_10);
if (x_34 == 0)
{
return x_10;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_10, 0);
x_36 = lean_ctor_get(x_10, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_10);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor_simpEq___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_3 < x_2;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_array_uget(x_14, x_3);
x_37 = lean_ctor_get(x_4, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 2);
lean_inc(x_39);
x_40 = lean_nat_dec_lt(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_15);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_4);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_16 = x_42;
x_17 = x_10;
goto block_36;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_4);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_4, 2);
lean_dec(x_44);
x_45 = lean_ctor_get(x_4, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_4, 0);
lean_dec(x_46);
x_47 = lean_array_fget(x_37, x_38);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_38, x_48);
lean_dec(x_38);
lean_ctor_set(x_4, 1, x_49);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_50 = l_Lean_Meta_Match_mkEquationsFor_simpEq(x_15, x_47, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_4);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_box(0);
x_16 = x_53;
x_17 = x_52;
goto block_36;
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 0);
lean_dec(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_51, 0, x_57);
x_16 = x_51;
x_17 = x_56;
goto block_36;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_51);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_dec(x_50);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_4);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_16 = x_60;
x_17 = x_58;
goto block_36;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_4);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_61 = !lean_is_exclusive(x_50);
if (x_61 == 0)
{
return x_50;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_50, 0);
x_63 = lean_ctor_get(x_50, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_50);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_4);
x_65 = lean_array_fget(x_37, x_38);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_38, x_66);
lean_dec(x_38);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_37);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_39);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_69 = l_Lean_Meta_Match_mkEquationsFor_simpEq(x_15, x_65, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_box(0);
x_16 = x_72;
x_17 = x_71;
goto block_36;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_68);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_75);
x_16 = x_76;
x_17 = x_74;
goto block_36;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_68);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_77 = lean_ctor_get(x_69, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_69, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_79 = x_69;
} else {
 lean_dec_ref(x_69);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
block_36:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
lean_ctor_set(x_16, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; 
lean_free_object(x_16);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = x_3 + x_25;
x_3 = x_26;
x_4 = x_24;
x_10 = x_17;
goto _start;
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
lean_dec(x_16);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_17);
return x_31;
}
else
{
lean_object* x_32; size_t x_33; size_t x_34; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
x_33 = 1;
x_34 = x_3 + x_33;
x_3 = x_34;
x_4 = x_32;
x_10 = x_17;
goto _start;
}
}
}
}
}
}
}
lean_object* l_List_forIn_loop___at_Lean_Meta_Match_mkEquationsFor_simpEq___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_2);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_13 = x_31;
x_14 = x_8;
goto block_29;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_34 = l_Lean_Meta_Match_mkEquationsFor_simpEq(x_11, x_32, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_box(0);
x_13 = x_37;
x_14 = x_36;
goto block_29;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_35, 0, x_41);
x_13 = x_35;
x_14 = x_40;
goto block_29;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_35);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_33);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_13 = x_44;
x_14 = x_42;
goto block_29;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_33);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_34);
if (x_45 == 0)
{
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_34);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
block_29:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
lean_ctor_set(x_13, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
else
{
lean_object* x_21; 
lean_free_object(x_13);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_1 = x_12;
x_2 = x_21;
x_8 = x_14;
goto _start;
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_14);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_1 = x_12;
x_2 = x_27;
x_8 = x_14;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_383; 
x_383 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchValue(x_1);
if (x_383 == 0)
{
uint8_t x_384; 
x_384 = l_Lean_Expr_isFVar(x_2);
if (x_384 == 0)
{
lean_object* x_385; 
x_385 = lean_box(0);
x_9 = x_385;
goto block_382;
}
else
{
lean_object* x_386; lean_object* x_387; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_386 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_8);
return x_387;
}
}
else
{
uint8_t x_388; 
x_388 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_isMatchValue(x_2);
if (x_388 == 0)
{
uint8_t x_389; 
x_389 = l_Lean_Expr_isFVar(x_2);
if (x_389 == 0)
{
lean_object* x_390; 
x_390 = lean_box(0);
x_9 = x_390;
goto block_382;
}
else
{
lean_object* x_391; lean_object* x_392; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_391 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_8);
return x_392;
}
}
else
{
lean_object* x_393; 
x_393 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; uint8_t x_395; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_unbox(x_394);
lean_dec(x_394);
if (x_395 == 0)
{
uint8_t x_396; 
x_396 = !lean_is_exclusive(x_393);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; 
x_397 = lean_ctor_get(x_393, 0);
lean_dec(x_397);
x_398 = lean_box(0);
lean_ctor_set(x_393, 0, x_398);
return x_393;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_393, 1);
lean_inc(x_399);
lean_dec(x_393);
x_400 = lean_box(0);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_399);
return x_401;
}
}
else
{
uint8_t x_402; 
x_402 = !lean_is_exclusive(x_393);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; 
x_403 = lean_ctor_get(x_393, 0);
lean_dec(x_403);
x_404 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
lean_ctor_set(x_393, 0, x_404);
return x_393;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_405 = lean_ctor_get(x_393, 1);
lean_inc(x_405);
lean_dec(x_393);
x_406 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
x_407 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_405);
return x_407;
}
}
}
else
{
uint8_t x_408; 
x_408 = !lean_is_exclusive(x_393);
if (x_408 == 0)
{
return x_393;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_393, 0);
x_410 = lean_ctor_get(x_393, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_393);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
return x_411;
}
}
}
}
block_382:
{
lean_object* x_10; 
lean_dec(x_9);
x_10 = l_Lean_Expr_arrayLit_x3f(x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_7, x_13);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_1);
x_20 = l_Lean_Meta_toCtorIfLit(x_1);
x_21 = l_Lean_Expr_constructorApp_x3f(x_14, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_free_object(x_15);
lean_inc(x_7);
x_22 = l_Lean_Meta_mkEq(x_1, x_2, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_7, x_24);
lean_dec(x_7);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_st_ref_take(x_3, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_array_push(x_28, x_23);
x_31 = lean_st_ref_set(x_3, x_30, x_29);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_7);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_21, 0);
lean_inc(x_42);
lean_dec(x_21);
lean_inc(x_2);
x_43 = l_Lean_Meta_toCtorIfLit(x_2);
x_44 = l_Lean_Expr_constructorApp_x3f(x_19, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_dec(x_42);
lean_free_object(x_15);
lean_inc(x_7);
x_45 = l_Lean_Meta_mkEq(x_1, x_2, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_st_ref_get(x_7, x_47);
lean_dec(x_7);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_st_ref_take(x_3, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_array_push(x_51, x_46);
x_54 = lean_st_ref_set(x_3, x_53, x_52);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_dec(x_7);
x_61 = !lean_is_exclusive(x_45);
if (x_61 == 0)
{
return x_45;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_45, 0);
x_63 = lean_ctor_get(x_45, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_45);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
lean_dec(x_44);
x_66 = lean_ctor_get(x_42, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_42, 1);
lean_inc(x_67);
lean_dec(x_42);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
lean_dec(x_68);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_name_eq(x_71, x_73);
lean_dec(x_73);
lean_dec(x_71);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_75 = lean_box(0);
lean_ctor_set(x_15, 0, x_75);
return x_15;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; size_t x_82; lean_object* x_83; size_t x_84; lean_object* x_85; 
lean_free_object(x_15);
x_76 = lean_ctor_get(x_66, 3);
lean_inc(x_76);
lean_dec(x_66);
x_77 = lean_array_get_size(x_69);
lean_inc(x_76);
x_78 = l_Array_toSubarray___rarg(x_69, x_76, x_77);
x_79 = lean_array_get_size(x_67);
x_80 = l_Array_toSubarray___rarg(x_67, x_76, x_79);
x_81 = lean_ctor_get(x_80, 2);
lean_inc(x_81);
x_82 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
x_84 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_85 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor_simpEq___spec__1(x_80, x_82, x_84, x_78, x_3, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_80);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 0);
lean_dec(x_88);
x_89 = lean_box(0);
lean_ctor_set(x_85, 0, x_89);
return x_85;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
uint8_t x_93; 
lean_dec(x_86);
x_93 = !lean_is_exclusive(x_85);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_85, 0);
lean_dec(x_94);
x_95 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
lean_ctor_set(x_85, 0, x_95);
return x_85;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_85, 1);
lean_inc(x_96);
lean_dec(x_85);
x_97 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_85);
if (x_99 == 0)
{
return x_85;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_85, 0);
x_101 = lean_ctor_get(x_85, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_85);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_15, 0);
x_104 = lean_ctor_get(x_15, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_15);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_1);
x_106 = l_Lean_Meta_toCtorIfLit(x_1);
x_107 = l_Lean_Expr_constructorApp_x3f(x_14, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
lean_dec(x_105);
lean_inc(x_7);
x_108 = l_Lean_Meta_mkEq(x_1, x_2, x_4, x_5, x_6, x_7, x_104);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_st_ref_get(x_7, x_110);
lean_dec(x_7);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_st_ref_take(x_3, x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_array_push(x_114, x_109);
x_117 = lean_st_ref_set(x_3, x_116, x_115);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_7);
x_122 = lean_ctor_get(x_108, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_108, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_124 = x_108;
} else {
 lean_dec_ref(x_108);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_107, 0);
lean_inc(x_126);
lean_dec(x_107);
lean_inc(x_2);
x_127 = l_Lean_Meta_toCtorIfLit(x_2);
x_128 = l_Lean_Expr_constructorApp_x3f(x_105, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
lean_dec(x_126);
lean_inc(x_7);
x_129 = l_Lean_Meta_mkEq(x_1, x_2, x_4, x_5, x_6, x_7, x_104);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_st_ref_get(x_7, x_131);
lean_dec(x_7);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_st_ref_take(x_3, x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_array_push(x_135, x_130);
x_138 = lean_st_ref_set(x_3, x_137, x_136);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
x_141 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_139);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_7);
x_143 = lean_ctor_get(x_129, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_129, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_145 = x_129;
} else {
 lean_dec_ref(x_129);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_2);
lean_dec(x_1);
x_147 = lean_ctor_get(x_128, 0);
lean_inc(x_147);
lean_dec(x_128);
x_148 = lean_ctor_get(x_126, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_126, 1);
lean_inc(x_149);
lean_dec(x_126);
x_150 = lean_ctor_get(x_147, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_147, 1);
lean_inc(x_151);
lean_dec(x_147);
x_152 = lean_ctor_get(x_148, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_ctor_get(x_150, 0);
lean_inc(x_154);
lean_dec(x_150);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_name_eq(x_153, x_155);
lean_dec(x_155);
lean_dec(x_153);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_151);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_104);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; size_t x_165; lean_object* x_166; size_t x_167; lean_object* x_168; 
x_159 = lean_ctor_get(x_148, 3);
lean_inc(x_159);
lean_dec(x_148);
x_160 = lean_array_get_size(x_151);
lean_inc(x_159);
x_161 = l_Array_toSubarray___rarg(x_151, x_159, x_160);
x_162 = lean_array_get_size(x_149);
x_163 = l_Array_toSubarray___rarg(x_149, x_159, x_162);
x_164 = lean_ctor_get(x_163, 2);
lean_inc(x_164);
x_165 = lean_usize_of_nat(x_164);
lean_dec(x_164);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
x_167 = lean_usize_of_nat(x_166);
lean_dec(x_166);
x_168 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor_simpEq___spec__1(x_163, x_165, x_167, x_161, x_3, x_4, x_5, x_6, x_7, x_104);
lean_dec(x_163);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
x_172 = lean_box(0);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_170);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_169);
x_174 = lean_ctor_get(x_168, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_175 = x_168;
} else {
 lean_dec_ref(x_168);
 x_175 = lean_box(0);
}
x_176 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_175;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_174);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_168, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_168, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_180 = x_168;
} else {
 lean_dec_ref(x_168);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_10, 0);
lean_inc(x_182);
lean_dec(x_10);
x_183 = l_Lean_Expr_arrayLit_x3f(x_2);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
lean_dec(x_182);
x_184 = lean_st_ref_get(x_7, x_8);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_ctor_get(x_185, 0);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_st_ref_get(x_7, x_186);
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_190 = lean_ctor_get(x_188, 0);
x_191 = lean_ctor_get(x_188, 1);
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
lean_dec(x_190);
lean_inc(x_1);
x_193 = l_Lean_Meta_toCtorIfLit(x_1);
x_194 = l_Lean_Expr_constructorApp_x3f(x_187, x_193);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; 
lean_dec(x_192);
lean_free_object(x_188);
lean_inc(x_7);
x_195 = l_Lean_Meta_mkEq(x_1, x_2, x_4, x_5, x_6, x_7, x_191);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_st_ref_get(x_7, x_197);
lean_dec(x_7);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_st_ref_take(x_3, x_199);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = lean_array_push(x_201, x_196);
x_204 = lean_st_ref_set(x_3, x_203, x_202);
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_204, 0);
lean_dec(x_206);
x_207 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
lean_ctor_set(x_204, 0, x_207);
return x_204;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_204, 1);
lean_inc(x_208);
lean_dec(x_204);
x_209 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
uint8_t x_211; 
lean_dec(x_7);
x_211 = !lean_is_exclusive(x_195);
if (x_211 == 0)
{
return x_195;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_195, 0);
x_213 = lean_ctor_get(x_195, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_195);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_194, 0);
lean_inc(x_215);
lean_dec(x_194);
lean_inc(x_2);
x_216 = l_Lean_Meta_toCtorIfLit(x_2);
x_217 = l_Lean_Expr_constructorApp_x3f(x_192, x_216);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; 
lean_dec(x_215);
lean_free_object(x_188);
lean_inc(x_7);
x_218 = l_Lean_Meta_mkEq(x_1, x_2, x_4, x_5, x_6, x_7, x_191);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = lean_st_ref_get(x_7, x_220);
lean_dec(x_7);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec(x_221);
x_223 = lean_st_ref_take(x_3, x_222);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_array_push(x_224, x_219);
x_227 = lean_st_ref_set(x_3, x_226, x_225);
x_228 = !lean_is_exclusive(x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_227, 0);
lean_dec(x_229);
x_230 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
lean_ctor_set(x_227, 0, x_230);
return x_227;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_227, 1);
lean_inc(x_231);
lean_dec(x_227);
x_232 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
else
{
uint8_t x_234; 
lean_dec(x_7);
x_234 = !lean_is_exclusive(x_218);
if (x_234 == 0)
{
return x_218;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_218, 0);
x_236 = lean_ctor_get(x_218, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_218);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
lean_dec(x_2);
lean_dec(x_1);
x_238 = lean_ctor_get(x_217, 0);
lean_inc(x_238);
lean_dec(x_217);
x_239 = lean_ctor_get(x_215, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_215, 1);
lean_inc(x_240);
lean_dec(x_215);
x_241 = lean_ctor_get(x_238, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_238, 1);
lean_inc(x_242);
lean_dec(x_238);
x_243 = lean_ctor_get(x_239, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
lean_dec(x_243);
x_245 = lean_ctor_get(x_241, 0);
lean_inc(x_245);
lean_dec(x_241);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec(x_245);
x_247 = lean_name_eq(x_244, x_246);
lean_dec(x_246);
lean_dec(x_244);
if (x_247 == 0)
{
lean_object* x_248; 
lean_dec(x_242);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_248 = lean_box(0);
lean_ctor_set(x_188, 0, x_248);
return x_188;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; size_t x_255; lean_object* x_256; size_t x_257; lean_object* x_258; 
lean_free_object(x_188);
x_249 = lean_ctor_get(x_239, 3);
lean_inc(x_249);
lean_dec(x_239);
x_250 = lean_array_get_size(x_242);
lean_inc(x_249);
x_251 = l_Array_toSubarray___rarg(x_242, x_249, x_250);
x_252 = lean_array_get_size(x_240);
x_253 = l_Array_toSubarray___rarg(x_240, x_249, x_252);
x_254 = lean_ctor_get(x_253, 2);
lean_inc(x_254);
x_255 = lean_usize_of_nat(x_254);
lean_dec(x_254);
x_256 = lean_ctor_get(x_253, 1);
lean_inc(x_256);
x_257 = lean_usize_of_nat(x_256);
lean_dec(x_256);
x_258 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor_simpEq___spec__1(x_253, x_255, x_257, x_251, x_3, x_4, x_5, x_6, x_7, x_191);
lean_dec(x_253);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
if (lean_obj_tag(x_259) == 0)
{
uint8_t x_260; 
x_260 = !lean_is_exclusive(x_258);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_258, 0);
lean_dec(x_261);
x_262 = lean_box(0);
lean_ctor_set(x_258, 0, x_262);
return x_258;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_258, 1);
lean_inc(x_263);
lean_dec(x_258);
x_264 = lean_box(0);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
}
else
{
uint8_t x_266; 
lean_dec(x_259);
x_266 = !lean_is_exclusive(x_258);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; 
x_267 = lean_ctor_get(x_258, 0);
lean_dec(x_267);
x_268 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
lean_ctor_set(x_258, 0, x_268);
return x_258;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_258, 1);
lean_inc(x_269);
lean_dec(x_258);
x_270 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
}
else
{
uint8_t x_272; 
x_272 = !lean_is_exclusive(x_258);
if (x_272 == 0)
{
return x_258;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_258, 0);
x_274 = lean_ctor_get(x_258, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_258);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
}
}
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_276 = lean_ctor_get(x_188, 0);
x_277 = lean_ctor_get(x_188, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_188);
x_278 = lean_ctor_get(x_276, 0);
lean_inc(x_278);
lean_dec(x_276);
lean_inc(x_1);
x_279 = l_Lean_Meta_toCtorIfLit(x_1);
x_280 = l_Lean_Expr_constructorApp_x3f(x_187, x_279);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; 
lean_dec(x_278);
lean_inc(x_7);
x_281 = l_Lean_Meta_mkEq(x_1, x_2, x_4, x_5, x_6, x_7, x_277);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_st_ref_get(x_7, x_283);
lean_dec(x_7);
x_285 = lean_ctor_get(x_284, 1);
lean_inc(x_285);
lean_dec(x_284);
x_286 = lean_st_ref_take(x_3, x_285);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_array_push(x_287, x_282);
x_290 = lean_st_ref_set(x_3, x_289, x_288);
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_292 = x_290;
} else {
 lean_dec_ref(x_290);
 x_292 = lean_box(0);
}
x_293 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
if (lean_is_scalar(x_292)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_292;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_291);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_7);
x_295 = lean_ctor_get(x_281, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_281, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_297 = x_281;
} else {
 lean_dec_ref(x_281);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_295);
lean_ctor_set(x_298, 1, x_296);
return x_298;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_280, 0);
lean_inc(x_299);
lean_dec(x_280);
lean_inc(x_2);
x_300 = l_Lean_Meta_toCtorIfLit(x_2);
x_301 = l_Lean_Expr_constructorApp_x3f(x_278, x_300);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; 
lean_dec(x_299);
lean_inc(x_7);
x_302 = l_Lean_Meta_mkEq(x_1, x_2, x_4, x_5, x_6, x_7, x_277);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
x_305 = lean_st_ref_get(x_7, x_304);
lean_dec(x_7);
x_306 = lean_ctor_get(x_305, 1);
lean_inc(x_306);
lean_dec(x_305);
x_307 = lean_st_ref_take(x_3, x_306);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_array_push(x_308, x_303);
x_311 = lean_st_ref_set(x_3, x_310, x_309);
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_313 = x_311;
} else {
 lean_dec_ref(x_311);
 x_313 = lean_box(0);
}
x_314 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
if (lean_is_scalar(x_313)) {
 x_315 = lean_alloc_ctor(0, 2, 0);
} else {
 x_315 = x_313;
}
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_312);
return x_315;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_7);
x_316 = lean_ctor_get(x_302, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_302, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_318 = x_302;
} else {
 lean_dec_ref(x_302);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 2, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_316);
lean_ctor_set(x_319, 1, x_317);
return x_319;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
lean_dec(x_2);
lean_dec(x_1);
x_320 = lean_ctor_get(x_301, 0);
lean_inc(x_320);
lean_dec(x_301);
x_321 = lean_ctor_get(x_299, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_299, 1);
lean_inc(x_322);
lean_dec(x_299);
x_323 = lean_ctor_get(x_320, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_320, 1);
lean_inc(x_324);
lean_dec(x_320);
x_325 = lean_ctor_get(x_321, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
lean_dec(x_325);
x_327 = lean_ctor_get(x_323, 0);
lean_inc(x_327);
lean_dec(x_323);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
lean_dec(x_327);
x_329 = lean_name_eq(x_326, x_328);
lean_dec(x_328);
lean_dec(x_326);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; 
lean_dec(x_324);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_330 = lean_box(0);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_277);
return x_331;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; size_t x_338; lean_object* x_339; size_t x_340; lean_object* x_341; 
x_332 = lean_ctor_get(x_321, 3);
lean_inc(x_332);
lean_dec(x_321);
x_333 = lean_array_get_size(x_324);
lean_inc(x_332);
x_334 = l_Array_toSubarray___rarg(x_324, x_332, x_333);
x_335 = lean_array_get_size(x_322);
x_336 = l_Array_toSubarray___rarg(x_322, x_332, x_335);
x_337 = lean_ctor_get(x_336, 2);
lean_inc(x_337);
x_338 = lean_usize_of_nat(x_337);
lean_dec(x_337);
x_339 = lean_ctor_get(x_336, 1);
lean_inc(x_339);
x_340 = lean_usize_of_nat(x_339);
lean_dec(x_339);
x_341 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor_simpEq___spec__1(x_336, x_338, x_340, x_334, x_3, x_4, x_5, x_6, x_7, x_277);
lean_dec(x_336);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_344 = x_341;
} else {
 lean_dec_ref(x_341);
 x_344 = lean_box(0);
}
x_345 = lean_box(0);
if (lean_is_scalar(x_344)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_344;
}
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_343);
return x_346;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_342);
x_347 = lean_ctor_get(x_341, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_348 = x_341;
} else {
 lean_dec_ref(x_341);
 x_348 = lean_box(0);
}
x_349 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
if (lean_is_scalar(x_348)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_348;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_347);
return x_350;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_351 = lean_ctor_get(x_341, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_341, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_353 = x_341;
} else {
 lean_dec_ref(x_341);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 2, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_352);
return x_354;
}
}
}
}
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; 
lean_dec(x_2);
lean_dec(x_1);
x_355 = lean_ctor_get(x_183, 0);
lean_inc(x_355);
lean_dec(x_183);
x_356 = lean_ctor_get(x_182, 1);
lean_inc(x_356);
lean_dec(x_182);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_358 = lean_unsigned_to_nat(0u);
x_359 = l_List_lengthAux___rarg(x_356, x_358);
x_360 = l_List_lengthAux___rarg(x_357, x_358);
x_361 = lean_nat_dec_eq(x_359, x_360);
lean_dec(x_360);
lean_dec(x_359);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_362 = lean_box(0);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_8);
return x_363;
}
else
{
lean_object* x_364; 
x_364 = l_List_forIn_loop___at_Lean_Meta_Match_mkEquationsFor_simpEq___spec__2(x_356, x_357, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
if (lean_obj_tag(x_365) == 0)
{
uint8_t x_366; 
x_366 = !lean_is_exclusive(x_364);
if (x_366 == 0)
{
lean_object* x_367; lean_object* x_368; 
x_367 = lean_ctor_get(x_364, 0);
lean_dec(x_367);
x_368 = lean_box(0);
lean_ctor_set(x_364, 0, x_368);
return x_364;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_364, 1);
lean_inc(x_369);
lean_dec(x_364);
x_370 = lean_box(0);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_369);
return x_371;
}
}
else
{
uint8_t x_372; 
lean_dec(x_365);
x_372 = !lean_is_exclusive(x_364);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_ctor_get(x_364, 0);
lean_dec(x_373);
x_374 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
lean_ctor_set(x_364, 0, x_374);
return x_364;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_364, 1);
lean_inc(x_375);
lean_dec(x_364);
x_376 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_375);
return x_377;
}
}
}
else
{
uint8_t x_378; 
x_378 = !lean_is_exclusive(x_364);
if (x_378 == 0)
{
return x_364;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_364, 0);
x_380 = lean_ctor_get(x_364, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_364);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
return x_381;
}
}
}
}
}
}
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor_simpEq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor_simpEq___spec__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_List_forIn_loop___at_Lean_Meta_Match_mkEquationsFor_simpEq___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_loop___at_Lean_Meta_Match_mkEquationsFor_simpEq___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Match_mkEquationsFor_simpEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to generate equality theorems for 'match', equality expected");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_2 == x_3;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_2);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__2;
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Expr_isAppOfArity(x_12, x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = l_Lean_indentExpr(x_12);
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__4;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__6;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__1(x_20, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l_Lean_Expr_appFn_x21(x_12);
x_27 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
x_28 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = l_Lean_Meta_Match_mkEquationsFor_simpEq(x_27, x_28, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; 
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
lean_dec(x_30);
x_39 = 1;
x_40 = x_2 + x_39;
x_2 = x_40;
x_4 = x_38;
x_10 = x_37;
goto _start;
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
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_4);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_10);
return x_47;
}
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_8, x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2(x_1, x_16, x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_19;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpEqs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Match_mkEquationsFor_simpEqs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_2 < x_1;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = x_3;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = x_12;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = lean_infer_type(x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = x_2 + x_19;
x_21 = x_17;
x_22 = lean_array_uset(x_14, x_2, x_21);
x_2 = x_20;
x_3 = x_22;
x_8 = x_18;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_3 == x_4;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = l_Lean_Expr_fvarId_x21(x_12);
lean_inc(x_1);
x_14 = l_Lean_Meta_dependsOn(x_1, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
lean_dec(x_12);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = 1;
x_19 = x_3 + x_18;
x_3 = x_19;
x_10 = x_17;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_array_push(x_5, x_12);
x_23 = 1;
x_24 = x_3 + x_23;
x_3 = x_24;
x_5 = x_22;
x_10 = x_21;
goto _start;
}
}
else
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_2 == x_3;
if (x_10 == 0)
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = 1;
x_12 = x_2 - x_11;
x_13 = lean_array_uget(x_1, x_12);
x_14 = l_Lean_Meta_mkArrow(x_13, x_4, x_5, x_6, x_7, x_8, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_2 = x_12;
x_4 = x_15;
x_9 = x_16;
goto _start;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("False");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_sub(x_9, x_2);
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_1);
x_12 = l_Array_toSubarray___rarg(x_1, x_11, x_10);
x_13 = l_Array_ofSubarray___rarg(x_12);
x_14 = l_Array_toSubarray___rarg(x_1, x_10, x_9);
x_15 = l_Array_ofSubarray___rarg(x_14);
x_16 = lean_array_get_size(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = x_15;
x_20 = lean_box_usize(x_17);
x_21 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___boxed__const__1;
x_22 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__1___boxed), 8, 3);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
lean_closure_set(x_22, 2, x_19);
x_23 = x_22;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = lean_apply_5(x_23, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_108; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_get(x_7, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1;
x_30 = lean_st_mk_ref(x_29, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_31);
x_108 = l_Lean_Meta_Match_mkEquationsFor_simpEqs(x_25, x_31, x_4, x_5, x_6, x_7, x_32);
lean_dec(x_25);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_box(0);
x_33 = x_111;
x_34 = x_110;
goto block_107;
}
else
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_113 = lean_ctor_get(x_109, 0);
lean_dec(x_113);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_dec(x_108);
x_115 = lean_st_ref_get(x_7, x_114);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_st_ref_get(x_31, x_116);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
lean_ctor_set(x_109, 0, x_118);
x_33 = x_109;
x_34 = x_119;
goto block_107;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_109);
x_120 = lean_ctor_get(x_108, 1);
lean_inc(x_120);
lean_dec(x_108);
x_121 = lean_st_ref_get(x_7, x_120);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_st_ref_get(x_31, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_124);
x_33 = x_126;
x_34 = x_125;
goto block_107;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_31);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_108);
if (x_127 == 0)
{
return x_108;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_108, 0);
x_129 = lean_ctor_get(x_108, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_108);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
block_107:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_st_ref_get(x_7, x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_get(x_31, x_36);
lean_dec(x_31);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_38; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_100; 
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_ctor_get(x_33, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_46 = x_33;
} else {
 lean_dec_ref(x_33);
 x_46 = lean_box(0);
}
x_47 = lean_array_get_size(x_45);
x_100 = lean_nat_dec_lt(x_11, x_47);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_47);
lean_dec(x_45);
x_101 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__3;
x_48 = x_101;
x_49 = x_44;
goto block_99;
}
else
{
size_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_103 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__3;
x_104 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__3(x_45, x_102, x_18, x_103, x_4, x_5, x_6, x_7, x_44);
lean_dec(x_45);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_48 = x_105;
x_49 = x_106;
goto block_99;
}
block_99:
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_array_get_size(x_13);
x_51 = lean_nat_dec_lt(x_11, x_50);
if (x_51 == 0)
{
uint8_t x_52; uint8_t x_53; lean_object* x_54; 
lean_dec(x_50);
lean_dec(x_13);
x_52 = 0;
x_53 = 1;
x_54 = l_Lean_Meta_mkForallFVars(x_29, x_48, x_52, x_53, x_4, x_5, x_6, x_7, x_49);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
if (lean_is_scalar(x_46)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_46;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_54);
if (lean_is_scalar(x_46)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_46;
}
lean_ctor_set(x_60, 0, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_46);
x_62 = !lean_is_exclusive(x_54);
if (x_62 == 0)
{
return x_54;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_54, 0);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_54);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
x_66 = lean_nat_dec_le(x_50, x_50);
if (x_66 == 0)
{
uint8_t x_67; uint8_t x_68; lean_object* x_69; 
lean_dec(x_50);
lean_dec(x_13);
x_67 = 0;
x_68 = 1;
x_69 = l_Lean_Meta_mkForallFVars(x_29, x_48, x_67, x_68, x_4, x_5, x_6, x_7, x_49);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
if (lean_is_scalar(x_46)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_46;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_69, 0, x_72);
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_69);
if (lean_is_scalar(x_46)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_46;
}
lean_ctor_set(x_75, 0, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_46);
x_77 = !lean_is_exclusive(x_69);
if (x_77 == 0)
{
return x_69;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_69, 0);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_69);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
size_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_86; lean_object* x_87; 
x_81 = lean_usize_of_nat(x_50);
lean_dec(x_50);
lean_inc(x_48);
x_82 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__2(x_48, x_13, x_18, x_81, x_29, x_4, x_5, x_6, x_7, x_49);
lean_dec(x_13);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = 0;
x_86 = 1;
x_87 = l_Lean_Meta_mkForallFVars(x_83, x_48, x_85, x_86, x_4, x_5, x_6, x_7, x_84);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_87, 0);
if (lean_is_scalar(x_46)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_46;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_87, 0, x_90);
return x_87;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_87, 0);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_87);
if (lean_is_scalar(x_46)) {
 x_93 = lean_alloc_ctor(1, 1, 0);
} else {
 x_93 = x_46;
}
lean_ctor_set(x_93, 0, x_91);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_dec(x_46);
x_95 = !lean_is_exclusive(x_87);
if (x_95 == 0)
{
return x_87;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_87, 0);
x_97 = lean_ctor_get(x_87, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_87);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_131 = !lean_is_exclusive(x_24);
if (x_131 == 0)
{
return x_24;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_24, 0);
x_133 = lean_ctor_get(x_24, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_24);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("debug");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__2;
x_2 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ys: ");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__4;
x_26 = lean_st_ref_get(x_7, x_8);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get_uint8(x_28, sizeof(void*)*1);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = 0;
x_10 = x_31;
x_11 = x_30;
goto block_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_9, x_4, x_5, x_6, x_7, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unbox(x_34);
lean_dec(x_34);
x_10 = x_36;
x_11 = x_35;
goto block_25;
}
block_25:
{
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1(x_2, x_1, x_12, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_1);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_2);
x_14 = lean_array_to_list(lean_box(0), x_2);
x_15 = l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_14);
x_16 = l_Lean_MessageData_ofList(x_15);
lean_dec(x_15);
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__6;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__6;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_9, x_20, x_4, x_5, x_6, x_7, x_11);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1(x_2, x_1, x_22, x_4, x_5, x_6, x_7, x_23);
lean_dec(x_22);
lean_dec(x_1);
return x_24;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_3 == x_4;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2), 8, 1);
lean_closure_set(x_13, 0, x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_12, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = x_3 + x_17;
x_3 = x_18;
x_10 = x_16;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_array_push(x_5, x_21);
x_23 = 1;
x_24 = x_3 + x_23;
x_3 = x_24;
x_5 = x_22;
x_10 = x_20;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_10);
return x_30;
}
}
}
lean_object* l_Array_filterMapM___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_3, x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_2);
x_14 = lean_nat_dec_le(x_4, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_18 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_19 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1;
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5(x_1, x_2, x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
}
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_simpHs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_filterMapM___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__4(x_2, x_1, x_9, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_filterMapM___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_filterMapM___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_proveLoop___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_3 == x_4;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_1, x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Meta_Match_mkEquationsFor_proveLoop(x_12, x_14, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = x_3 + x_18;
x_3 = x_19;
x_5 = x_16;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
else
{
lean_object* x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_Match_mkEquationsFor_proveLoop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__6;
x_9 = lean_array_push(x_8, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("refl failed");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to generate equality theorems for `match` expression, support for array literals has not been implemented yet");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("spliIf failed");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simpIf failed");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_30; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
x_9 = lean_box(0);
lean_inc(x_1);
x_10 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__6;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__6;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_38 = lean_st_ref_get(x_7, x_8);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_st_ref_get(x_7, x_40);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_st_ref_get(x_5, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__3;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_49 = l_Lean_Meta_applyRefl(x_1, x_48, x_4, x_5, x_6, x_7, x_46);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_1);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1;
x_15 = x_51;
x_16 = x_50;
goto block_29;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_41, x_4, x_5, x_6, x_7, x_52);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_Meta_setMCtx(x_47, x_4, x_5, x_6, x_7, x_54);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_st_ref_get(x_7, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_st_ref_get(x_7, x_59);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_st_ref_get(x_5, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_68 = l_Lean_Meta_contradiction(x_1, x_67, x_4, x_5, x_6, x_7, x_65);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
lean_dec(x_66);
lean_dec(x_60);
lean_dec(x_14);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
lean_dec(x_70);
x_71 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1;
lean_ctor_set(x_68, 0, x_71);
x_30 = x_68;
goto block_37;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_dec(x_68);
x_73 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1;
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_30 = x_74;
goto block_37;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_dec(x_68);
x_76 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_60, x_4, x_5, x_6, x_7, x_75);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Lean_Meta_setMCtx(x_66, x_4, x_5, x_6, x_7, x_77);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_st_ref_get(x_7, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_st_ref_get(x_7, x_82);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_st_ref_get(x_5, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_90 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS(x_1, x_4, x_5, x_6, x_7, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_dec(x_89);
lean_dec(x_83);
lean_dec(x_14);
lean_dec(x_1);
x_30 = x_90;
goto block_37;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_156; lean_object* x_157; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_83, x_4, x_5, x_6, x_7, x_91);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lean_Meta_setMCtx(x_89, x_4, x_5, x_6, x_7, x_93);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_st_ref_get(x_7, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_st_ref_get(x_7, x_98);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_st_ref_get(x_5, x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_156 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_157 = l_Lean_Meta_simpIfTarget(x_1, x_156, x_4, x_5, x_6, x_7, x_104);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_name_eq(x_158, x_1);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_105);
lean_dec(x_99);
lean_dec(x_14);
lean_dec(x_1);
x_161 = lean_box(0);
x_162 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__1(x_158, x_161, x_4, x_5, x_6, x_7, x_159);
x_30 = x_162;
goto block_37;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_158);
x_163 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__11;
x_164 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_163, x_4, x_5, x_6, x_7, x_159);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_106 = x_165;
goto block_155;
}
}
else
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_157, 1);
lean_inc(x_166);
lean_dec(x_157);
x_106 = x_166;
goto block_155;
}
block_155:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_128; 
x_107 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_99, x_4, x_5, x_6, x_7, x_106);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = l_Lean_Meta_setMCtx(x_105, x_4, x_5, x_6, x_7, x_108);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_st_ref_get(x_7, x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_st_ref_get(x_7, x_113);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_st_ref_get(x_5, x_116);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
lean_dec(x_118);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_128 = l_Lean_commitWhenSome_x3f___at_Lean_Meta_splitIfTarget_x3f___spec__1___at_Lean_Meta_splitIfTarget_x3f___spec__2(x_1, x_9, x_4, x_5, x_6, x_7, x_119);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__8;
x_132 = l_Lean_throwError___at_Lean_Meta_Match_mkEquationsFor_proveLoop___spec__2(x_131, x_4, x_5, x_6, x_7, x_130);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_121 = x_133;
goto block_127;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
lean_dec(x_120);
lean_dec(x_114);
lean_dec(x_14);
x_134 = lean_ctor_get(x_129, 0);
lean_inc(x_134);
lean_dec(x_129);
x_135 = lean_ctor_get(x_128, 1);
lean_inc(x_135);
lean_dec(x_128);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_140 = l_Lean_Meta_trySubst(x_138, x_139, x_4, x_5, x_6, x_7, x_135);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_140, 0);
x_143 = lean_ctor_get(x_137, 0);
lean_inc(x_143);
lean_dec(x_137);
x_144 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__9;
x_145 = lean_array_push(x_144, x_142);
x_146 = lean_array_push(x_145, x_143);
lean_ctor_set(x_140, 0, x_146);
x_30 = x_140;
goto block_37;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_147 = lean_ctor_get(x_140, 0);
x_148 = lean_ctor_get(x_140, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_140);
x_149 = lean_ctor_get(x_137, 0);
lean_inc(x_149);
lean_dec(x_137);
x_150 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__9;
x_151 = lean_array_push(x_150, x_147);
x_152 = lean_array_push(x_151, x_149);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_148);
x_30 = x_153;
goto block_37;
}
}
}
else
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_128, 1);
lean_inc(x_154);
lean_dec(x_128);
x_121 = x_154;
goto block_127;
}
block_127:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_114, x_4, x_5, x_6, x_7, x_121);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_124 = l_Lean_Meta_setMCtx(x_120, x_4, x_5, x_6, x_7, x_123);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = l_Lean_throwError___at_Lean_Meta_Match_mkEquationsFor_proveLoop___spec__2(x_14, x_4, x_5, x_6, x_7, x_125);
x_30 = x_126;
goto block_37;
}
}
}
}
}
block_29:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_array_get_size(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_17, x_17);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
return x_24;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_27 = lean_box(0);
x_28 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_proveLoop___spec__1(x_2, x_15, x_25, x_26, x_27, x_4, x_5, x_6, x_7, x_16);
lean_dec(x_15);
lean_dec(x_2);
return x_28;
}
}
}
block_37:
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_15 = x_31;
x_16 = x_32;
goto block_29;
}
else
{
uint8_t x_33; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_whnfCore), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("proveLoop [");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_4);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
lean_ctor_set(x_7, 1, x_11);
x_14 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Meta_modifyTargetEqLHS(x_2, x_14, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__4;
x_39 = lean_st_ref_get(x_8, x_17);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = 0;
x_19 = x_44;
x_20 = x_43;
goto block_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_18, x_5, x_6, x_7, x_8, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unbox(x_47);
lean_dec(x_47);
x_19 = x_49;
x_20 = x_48;
goto block_38;
}
block_38:
{
if (x_19 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2(x_16, x_3, x_21, x_5, x_6, x_7, x_8, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_3);
x_23 = l_Nat_repr(x_3);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__3;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__5;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_16);
x_30 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_30, 0, x_16);
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__6;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_18, x_33, x_5, x_6, x_7, x_8, x_20);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2(x_16, x_3, x_35, x_5, x_6, x_7, x_8, x_36);
return x_37;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
return x_15;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_15, 0);
x_52 = lean_ctor_get(x_15, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_15);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_ctor_get(x_7, 2);
x_56 = lean_ctor_get(x_7, 3);
x_57 = lean_ctor_get(x_7, 4);
x_58 = lean_ctor_get(x_7, 5);
x_59 = lean_ctor_get(x_7, 6);
x_60 = lean_ctor_get(x_7, 7);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_7);
x_61 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_61, 0, x_54);
lean_ctor_set(x_61, 1, x_11);
lean_ctor_set(x_61, 2, x_55);
lean_ctor_set(x_61, 3, x_56);
lean_ctor_set(x_61, 4, x_57);
lean_ctor_set(x_61, 5, x_58);
lean_ctor_set(x_61, 6, x_59);
lean_ctor_set(x_61, 7, x_60);
x_62 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__1;
lean_inc(x_8);
lean_inc(x_61);
lean_inc(x_6);
lean_inc(x_5);
x_63 = l_Lean_Meta_modifyTargetEqLHS(x_2, x_62, x_5, x_6, x_61, x_8, x_9);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__4;
x_87 = lean_st_ref_get(x_8, x_65);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_88, 3);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_ctor_get_uint8(x_89, sizeof(void*)*1);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_dec(x_87);
x_92 = 0;
x_67 = x_92;
x_68 = x_91;
goto block_86;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_dec(x_87);
x_94 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_66, x_5, x_6, x_61, x_8, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_unbox(x_95);
lean_dec(x_95);
x_67 = x_97;
x_68 = x_96;
goto block_86;
}
block_86:
{
if (x_67 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_box(0);
x_70 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2(x_64, x_3, x_69, x_5, x_6, x_61, x_8, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_inc(x_3);
x_71 = l_Nat_repr(x_3);
x_72 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__3;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__5;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_inc(x_64);
x_78 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_78, 0, x_64);
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__6;
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_66, x_81, x_5, x_6, x_61, x_8, x_68);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2(x_64, x_3, x_83, x_5, x_6, x_61, x_8, x_84);
return x_85;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_61);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_98 = lean_ctor_get(x_63, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_63, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_100 = x_63;
} else {
 lean_dec_ref(x_63);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3(x_8, x_1, x_2, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___closed__2;
x_14 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_13, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_proveLoop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_proveLoop___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_Match_mkEquationsFor_proveLoop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_Match_mkEquationsFor_proveLoop___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
uint8_t l_Lean_Meta_Match_mkEquationsFor_prove___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_prove___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_box(0);
lean_inc(x_4);
x_10 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_3, x_9, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_mvarId_x21(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkEquationsFor_prove___lambda__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Meta_deltaTarget(x_13, x_14, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Meta_Match_mkEquationsFor_proveLoop(x_16, x_18, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Meta_instantiateMVars(x_11, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 0;
x_25 = 1;
x_26 = l_Lean_Meta_mkLambdaFVars(x_2, x_22, x_24, x_25, x_4, x_5, x_6, x_7, x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
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
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_prove___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_prove___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkEquationsFor_prove___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_prove___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Match_mkEquationsFor_prove___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_prove___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_prove___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkEquationsFor_prove___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_prove___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_Match_mkEquationsFor_prove___closed__5;
x_3 = l_Lean_Meta_Match_mkEquationsFor_prove___closed__4;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor_prove___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Match_mkEquationsFor_prove___closed__3;
x_2 = l_Lean_Meta_Match_mkEquationsFor_prove___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_prove(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_instantiateMVars(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkEquationsFor_prove___lambda__2), 8, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg), 7, 2);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_Match_mkEquationsFor_prove___closed__7;
x_14 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1;
x_15 = l_Lean_Meta_withLCtx___at_Lean_Meta_ppGoal___spec__15___rarg(x_13, x_14, x_12, x_3, x_4, x_5, x_6, x_10);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor_prove___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Match_mkEquationsFor_prove___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_1, x_14, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_push(x_5, x_16);
x_19 = 1;
x_20 = x_4 + x_19;
x_4 = x_20;
x_5 = x_18;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_3 < x_2;
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_1, x_3);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_14, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_14, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = lean_array_fget(x_16, x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_17, x_26);
lean_dec(x_17);
lean_ctor_set(x_14, 1, x_27);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_28 = l_Lean_Meta_mkEq(x_12, x_25, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_mkArrow(x_29, x_15, x_5, x_6, x_7, x_8, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_ctor_set(x_4, 0, x_32);
x_34 = 1;
x_35 = x_3 + x_34;
x_3 = x_35;
x_9 = x_33;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_14);
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_28, 0);
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_28);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_14);
x_41 = lean_array_fget(x_16, x_17);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_17, x_42);
lean_dec(x_17);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_16);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_45 = l_Lean_Meta_mkEq(x_12, x_41, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Meta_mkArrow(x_46, x_15, x_5, x_6, x_7, x_8, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_ctor_set(x_4, 1, x_44);
lean_ctor_set(x_4, 0, x_49);
x_51 = 1;
x_52 = x_3 + x_51;
x_3 = x_52;
x_9 = x_50;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_44);
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_54 = lean_ctor_get(x_45, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_56 = x_45;
} else {
 lean_dec_ref(x_45);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_4, 1);
x_59 = lean_ctor_get(x_4, 0);
lean_inc(x_58);
lean_inc(x_59);
lean_dec(x_4);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 2);
lean_inc(x_62);
x_63 = lean_nat_dec_lt(x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_58);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_9);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 x_66 = x_58;
} else {
 lean_dec_ref(x_58);
 x_66 = lean_box(0);
}
x_67 = lean_array_fget(x_60, x_61);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_add(x_61, x_68);
lean_dec(x_61);
if (lean_is_scalar(x_66)) {
 x_70 = lean_alloc_ctor(0, 3, 0);
} else {
 x_70 = x_66;
}
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_62);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_71 = l_Lean_Meta_mkEq(x_12, x_67, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Meta_mkArrow(x_72, x_59, x_5, x_6, x_7, x_8, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_70);
x_78 = 1;
x_79 = x_3 + x_78;
x_3 = x_79;
x_4 = x_77;
x_9 = x_76;
goto _start;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_70);
lean_dec(x_59);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_81 = lean_ctor_get(x_71, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_71, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_83 = x_71;
} else {
 lean_dec_ref(x_71);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("eq");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1___closed__2;
x_15 = lean_name_append_index_after(x_14, x_1);
x_16 = l_Lean_Name_append(x_2, x_15);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_addDecl___at_Lean_Meta_mkAuxLemma___spec__2(x_19, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_array_push(x_6, x_7);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_array_push(x_6, x_7);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("thmVal: ");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, size_t x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23) {
_start:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = l_Lean_ConstantInfo_name(x_1);
lean_dec(x_1);
x_25 = l_Lean_mkConst(x_24, x_2);
x_26 = l_Array_ofSubarray___rarg(x_3);
x_27 = l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__6;
x_28 = lean_array_push(x_27, x_4);
x_29 = l_Array_append___rarg(x_26, x_28);
lean_inc(x_29);
x_30 = l_Array_append___rarg(x_29, x_5);
x_31 = l_Array_ofSubarray___rarg(x_6);
lean_inc(x_31);
x_32 = l_Array_append___rarg(x_30, x_31);
x_33 = l_Lean_mkAppN(x_25, x_32);
x_34 = l_Lean_mkAppN(x_7, x_8);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_35 = l_Lean_Meta_mkEq(x_33, x_34, x_19, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_84; uint8_t x_85; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_array_get_size(x_9);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_lt(x_84, x_38);
if (x_85 == 0)
{
lean_dec(x_38);
lean_dec(x_9);
x_39 = x_36;
x_40 = x_37;
goto block_83;
}
else
{
size_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_87 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__3(x_9, x_86, x_17, x_36, x_19, x_20, x_21, x_22, x_37);
lean_dec(x_9);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_39 = x_88;
x_40 = x_89;
goto block_83;
}
block_83:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; 
x_41 = l_Array_append___rarg(x_29, x_31);
x_42 = l_Array_append___rarg(x_41, x_10);
x_43 = 0;
x_44 = 1;
lean_inc(x_19);
x_45 = l_Lean_Meta_mkForallFVars(x_42, x_39, x_43, x_44, x_19, x_20, x_21, x_22, x_40);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_46);
lean_inc(x_11);
x_48 = l_Lean_Meta_Match_mkEquationsFor_prove(x_11, x_46, x_19, x_20, x_21, x_22, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_65 = lean_st_ref_get(x_22, x_50);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 3);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_ctor_get_uint8(x_67, sizeof(void*)*1);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_51 = x_43;
x_52 = x_69;
goto block_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_dec(x_65);
lean_inc(x_16);
x_71 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_16, x_19, x_20, x_21, x_22, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_unbox(x_72);
lean_dec(x_72);
x_51 = x_74;
x_52 = x_73;
goto block_64;
}
block_64:
{
if (x_51 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_16);
x_53 = lean_box(0);
x_54 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1(x_12, x_11, x_13, x_46, x_49, x_14, x_15, x_53, x_19, x_20, x_21, x_22, x_52);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_11);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_inc(x_49);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_49);
x_56 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2___closed__2;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__6;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_16, x_59, x_19, x_20, x_21, x_22, x_52);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1(x_12, x_11, x_13, x_46, x_49, x_14, x_15, x_61, x_19, x_20, x_21, x_22, x_62);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_61);
lean_dec(x_11);
return x_63;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_46);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_75 = !lean_is_exclusive(x_48);
if (x_75 == 0)
{
return x_48;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_48, 0);
x_77 = lean_ctor_get(x_48, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_48);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_79 = !lean_is_exclusive(x_45);
if (x_79 == 0)
{
return x_45;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_45, 0);
x_81 = lean_ctor_get(x_45, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_45);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_90 = !lean_is_exclusive(x_35);
if (x_90 == 0)
{
return x_35;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_35, 0);
x_92 = lean_ctor_get(x_35, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_35);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("notAlt: ");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23) {
_start:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; 
lean_dec(x_18);
lean_inc(x_1);
x_24 = l_Array_reverse___rarg(x_1);
x_25 = lean_array_get_size(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_toSubarray___rarg(x_24, x_26, x_25);
x_28 = l_Array_ofSubarray___rarg(x_2);
lean_inc(x_28);
x_29 = l_Array_reverse___rarg(x_28);
x_30 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__3;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
x_32 = lean_array_get_size(x_29);
x_33 = lean_usize_of_nat(x_32);
lean_dec(x_32);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_34 = l_Array_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__2(x_29, x_33, x_3, x_31, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_4);
x_38 = l_Array_append___rarg(x_28, x_4);
x_39 = 0;
x_40 = 1;
lean_inc(x_19);
x_41 = l_Lean_Meta_mkForallFVars(x_38, x_37, x_39, x_40, x_19, x_20, x_21, x_22, x_36);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_58 = lean_st_ref_get(x_22, x_43);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 3);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get_uint8(x_60, sizeof(void*)*1);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_44 = x_39;
x_45 = x_62;
goto block_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_dec(x_58);
lean_inc(x_17);
x_64 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_17, x_19, x_20, x_21, x_22, x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unbox(x_65);
lean_dec(x_65);
x_44 = x_67;
x_45 = x_66;
goto block_57;
}
block_57:
{
if (x_44 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_box(0);
x_47 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2(x_5, x_6, x_7, x_8, x_1, x_9, x_10, x_11, x_12, x_4, x_13, x_14, x_15, x_16, x_42, x_17, x_3, x_46, x_19, x_20, x_21, x_22, x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_inc(x_42);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_42);
x_49 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3___closed__2;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__6;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_17);
x_53 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_17, x_52, x_19, x_20, x_21, x_22, x_45);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2(x_5, x_6, x_7, x_8, x_1, x_9, x_10, x_11, x_12, x_4, x_13, x_14, x_15, x_16, x_42, x_17, x_3, x_54, x_19, x_20, x_21, x_22, x_55);
lean_dec(x_54);
return x_56;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_41);
if (x_68 == 0)
{
return x_41;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_41, 0);
x_70 = lean_ctor_get(x_41, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_41);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_34);
if (x_72 == 0)
{
return x_34;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_34, 0);
x_74 = lean_ctor_get(x_34, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_34);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hs: ");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_21 = l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs(x_14, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Expr_getAppNumArgsAux(x_15, x_26);
x_28 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___closed__1;
lean_inc(x_27);
x_29 = lean_mk_array(x_27, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_27, x_30);
lean_dec(x_27);
x_32 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_15, x_29, x_31);
x_33 = lean_array_get_size(x_1);
x_34 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_35 = 0;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_36 = l_Array_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__1(x_32, x_1, x_34, x_35, x_2, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_array_get_size(x_32);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_40 = l_Lean_Meta_Match_mkEquationsFor_simpHs(x_37, x_39, x_16, x_17, x_18, x_19, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_59 = lean_st_ref_get(x_19, x_42);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 3);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_ctor_get_uint8(x_61, sizeof(void*)*1);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = 0;
x_43 = x_64;
x_44 = x_63;
goto block_58;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
lean_inc(x_13);
x_66 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_13, x_16, x_17, x_18, x_19, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_43 = x_69;
x_44 = x_68;
goto block_58;
}
block_58:
{
if (x_43 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_box(0);
x_46 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3(x_32, x_3, x_35, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_25, x_41, x_10, x_11, x_12, x_1, x_13, x_45, x_16, x_17, x_18, x_19, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_inc(x_41);
x_47 = lean_array_to_list(lean_box(0), x_41);
x_48 = l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_47);
x_49 = l_Lean_MessageData_ofList(x_48);
lean_dec(x_48);
x_50 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4___closed__2;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__6;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_13);
x_54 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_13, x_53, x_16, x_17, x_18, x_19, x_44);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3(x_32, x_3, x_35, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_25, x_41, x_10, x_11, x_12, x_1, x_13, x_55, x_16, x_17, x_18, x_19, x_56);
return x_57;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_40);
if (x_70 == 0)
{
return x_40;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_40, 0);
x_72 = lean_ctor_get(x_40, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_40);
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
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_36);
if (x_74 == 0)
{
return x_36;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_36, 0);
x_76 = lean_ctor_get(x_36, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_36);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_21);
if (x_78 == 0)
{
return x_21;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_21, 0);
x_80 = lean_ctor_get(x_21, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_21);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; 
lean_inc(x_14);
x_21 = lean_alloc_closure((void*)(l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4___boxed), 20, 13);
lean_closure_set(x_21, 0, x_13);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_3);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_5);
lean_closure_set(x_21, 6, x_6);
lean_closure_set(x_21, 7, x_7);
lean_closure_set(x_21, 8, x_8);
lean_closure_set(x_21, 9, x_9);
lean_closure_set(x_21, 10, x_14);
lean_closure_set(x_21, 11, x_10);
lean_closure_set(x_21, 12, x_11);
x_22 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_12, x_21, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_14, x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_22, 0, x_28);
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_14, x_31);
lean_dec(x_14);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_14);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(">> ");
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, size_t x_11, size_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
x_19 = x_12 < x_11;
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_array_uget(x_21, x_12);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_dec(x_13);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_22);
x_25 = lean_infer_type(x_22, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__4;
x_75 = lean_st_ref_get(x_17, x_27);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_76, 3);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_ctor_get_uint8(x_77, sizeof(void*)*1);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = 0;
x_29 = x_80;
x_30 = x_79;
goto block_74;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_dec(x_75);
x_82 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_28, x_14, x_15, x_16, x_17, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_unbox(x_83);
lean_dec(x_83);
x_29 = x_85;
x_30 = x_84;
goto block_74;
}
block_74:
{
if (x_29 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_8);
lean_inc(x_9);
x_32 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__5(x_9, x_8, x_2, x_4, x_5, x_6, x_7, x_22, x_1, x_3, x_28, x_26, x_23, x_24, x_31, x_14, x_15, x_16, x_17, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; 
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_42 = 1;
x_43 = x_12 + x_42;
x_12 = x_43;
x_13 = x_41;
x_18 = x_40;
goto _start;
}
}
else
{
uint8_t x_45; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_32);
if (x_45 == 0)
{
return x_32;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_32, 0);
x_47 = lean_ctor_get(x_32, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_32);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_inc(x_26);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_26);
x_50 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___closed__2;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__6;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_28, x_53, x_14, x_15, x_16, x_17, x_30);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_8);
lean_inc(x_9);
x_57 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__5(x_9, x_8, x_2, x_4, x_5, x_6, x_7, x_22, x_1, x_3, x_28, x_26, x_23, x_24, x_55, x_14, x_15, x_16, x_17, x_56);
lean_dec(x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 0);
lean_dec(x_60);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec(x_58);
lean_ctor_set(x_57, 0, x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
lean_dec(x_58);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; 
x_65 = lean_ctor_get(x_57, 1);
lean_inc(x_65);
lean_dec(x_57);
x_66 = lean_ctor_get(x_58, 0);
lean_inc(x_66);
lean_dec(x_58);
x_67 = 1;
x_68 = x_12 + x_67;
x_12 = x_68;
x_13 = x_66;
x_18 = x_65;
goto _start;
}
}
else
{
uint8_t x_70; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_57);
if (x_70 == 0)
{
return x_57;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_57, 0);
x_72 = lean_ctor_get(x_57, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_57);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_25);
if (x_86 == 0)
{
return x_25;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_25, 0);
x_88 = lean_ctor_get(x_25, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_25);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
lean_inc(x_13);
lean_inc(x_6);
x_15 = l_Array_toSubarray___rarg(x_6, x_14, x_13);
x_16 = l_Lean_instInhabitedExpr;
x_17 = lean_array_get(x_16, x_6, x_13);
x_18 = lean_array_get_size(x_6);
x_19 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_1);
x_20 = lean_nat_sub(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = lean_array_get_size(x_6);
lean_inc(x_6);
x_22 = l_Array_toSubarray___rarg(x_6, x_20, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_13, x_23);
lean_dec(x_13);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_nat_add(x_24, x_25);
lean_dec(x_25);
x_27 = l_Array_toSubarray___rarg(x_6, x_24, x_26);
x_28 = lean_ctor_get(x_22, 2);
lean_inc(x_28);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
x_31 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_32 = l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1;
x_33 = l_Lean_Meta_Match_mkEquationsFor___lambda__1___closed__1;
lean_inc(x_22);
x_34 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3(x_2, x_3, x_4, x_5, x_15, x_17, x_22, x_27, x_32, x_22, x_29, x_31, x_33, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_22);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
return x_34;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_34, 0);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_34);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkEquationsFor___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a matcher function");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Match_mkEquationsFor___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Match_mkEquationsFor___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_ConstantInfo_levelParams(x_8);
lean_inc(x_10);
x_11 = l_List_map___at_Lean_mkConstWithLevelParams___spec__1(x_10);
lean_inc(x_1);
x_12 = l_Lean_Meta_getMatcherInfo_x3f(x_1, x_2, x_3, x_4, x_5, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = l_Lean_Meta_Match_mkEquationsFor___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Meta_Match_mkEquationsFor___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_19, x_2, x_3, x_4, x_5, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_ConstantInfo_type(x_8);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_Match_mkEquationsFor___lambda__1___boxed), 12, 5);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_1);
lean_closure_set(x_24, 2, x_8);
lean_closure_set(x_24, 3, x_10);
lean_closure_set(x_24, 4, x_11);
x_25 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_23, x_24, x_2, x_3, x_4, x_5, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
return x_7;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
return x_14;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2___boxed(lean_object** _args) {
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
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
_start:
{
size_t x_24; lean_object* x_25; 
x_24 = lean_unbox_usize(x_17);
lean_dec(x_17);
x_25 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_24, x_18, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_18);
return x_25;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3___boxed(lean_object** _args) {
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
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
_start:
{
size_t x_24; lean_object* x_25; 
x_24 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_25 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3(x_1, x_2, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
return x_25;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4___boxed(lean_object** _args) {
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
lean_object* x_21; 
x_21 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_21;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__5___boxed(lean_object** _args) {
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
lean_object* x_21; 
x_21 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_15);
return x_21;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___boxed(lean_object** _args) {
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
_start:
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_20 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_21 = l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19, x_20, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_10);
return x_21;
}
}
lean_object* l_Lean_Meta_Match_mkEquationsFor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Match_mkEquationsFor___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_13;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Match_Match(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Delta(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_SplitIf(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Match_MatchEqs(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Match(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Delta(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_SplitIf(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg___closed__1 = _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg___closed__1);
l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg___closed__2 = _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS_failed___rarg___closed__2);
l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1 = _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___lambda__1___closed__1);
l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___closed__1 = _init_l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_MatchEqs_0__Lean_Meta_Match_casesOnStuckLHS___closed__1);
l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__1 = _init_l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__1);
l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__2 = _init_l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__2);
l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__3 = _init_l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__3);
l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__4 = _init_l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__4);
l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__5 = _init_l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__5();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__5);
l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__6 = _init_l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__6();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__6);
l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__7 = _init_l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__7();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__7);
l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__8 = _init_l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__8();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_toFVarsRHSArgs___closed__8);
l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1 = _init_l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_simpEq___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__3);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__4 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__4);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__5 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__5();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__5);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__6 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__6();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpEqs___spec__2___closed__6);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___closed__3);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___boxed__const__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___boxed__const__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__1___boxed__const__1);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__3);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__4 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__4);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__5 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__5();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__5);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__6 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__6();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Match_mkEquationsFor_simpHs___spec__5___lambda__2___closed__6);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__1 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__1);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__2 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__2);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__3 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__3);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__4 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__4);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__5 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__5);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__6 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__6);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__7 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__7);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__8 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__8);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__9 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__9);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__10 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__10);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__11 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__11();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__2___closed__11);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__1 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__1);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__2 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__2);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__3 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__3);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__4 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__4);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__5 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___lambda__3___closed__5);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___closed__1 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___closed__1);
l_Lean_Meta_Match_mkEquationsFor_proveLoop___closed__2 = _init_l_Lean_Meta_Match_mkEquationsFor_proveLoop___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_proveLoop___closed__2);
l_Lean_Meta_Match_mkEquationsFor_prove___closed__1 = _init_l_Lean_Meta_Match_mkEquationsFor_prove___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_prove___closed__1);
l_Lean_Meta_Match_mkEquationsFor_prove___closed__2 = _init_l_Lean_Meta_Match_mkEquationsFor_prove___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_prove___closed__2);
l_Lean_Meta_Match_mkEquationsFor_prove___closed__3 = _init_l_Lean_Meta_Match_mkEquationsFor_prove___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_prove___closed__3);
l_Lean_Meta_Match_mkEquationsFor_prove___closed__4 = _init_l_Lean_Meta_Match_mkEquationsFor_prove___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_prove___closed__4);
l_Lean_Meta_Match_mkEquationsFor_prove___closed__5 = _init_l_Lean_Meta_Match_mkEquationsFor_prove___closed__5();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_prove___closed__5);
l_Lean_Meta_Match_mkEquationsFor_prove___closed__6 = _init_l_Lean_Meta_Match_mkEquationsFor_prove___closed__6();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_prove___closed__6);
l_Lean_Meta_Match_mkEquationsFor_prove___closed__7 = _init_l_Lean_Meta_Match_mkEquationsFor_prove___closed__7();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor_prove___closed__7);
l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1___closed__1 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1___closed__1);
l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1___closed__2 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1___closed__2();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__1___closed__2);
l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2___closed__1 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2___closed__1);
l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2___closed__2 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2___closed__2();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__2___closed__2);
l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3___closed__1 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3___closed__1();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3___closed__1);
l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3___closed__2 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3___closed__2();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__3___closed__2);
l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4___closed__1 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4___closed__1();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4___closed__1);
l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4___closed__2 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4___closed__2();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___lambda__4___closed__2);
l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___closed__1 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___closed__1();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___closed__1);
l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___closed__2 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___closed__2();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Meta_Match_mkEquationsFor___spec__3___closed__2);
l_Lean_Meta_Match_mkEquationsFor___lambda__1___closed__1 = _init_l_Lean_Meta_Match_mkEquationsFor___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor___lambda__1___closed__1);
l_Lean_Meta_Match_mkEquationsFor___closed__1 = _init_l_Lean_Meta_Match_mkEquationsFor___closed__1();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor___closed__1);
l_Lean_Meta_Match_mkEquationsFor___closed__2 = _init_l_Lean_Meta_Match_mkEquationsFor___closed__2();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor___closed__2);
l_Lean_Meta_Match_mkEquationsFor___closed__3 = _init_l_Lean_Meta_Match_mkEquationsFor___closed__3();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor___closed__3);
l_Lean_Meta_Match_mkEquationsFor___closed__4 = _init_l_Lean_Meta_Match_mkEquationsFor___closed__4();
lean_mark_persistent(l_Lean_Meta_Match_mkEquationsFor___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
