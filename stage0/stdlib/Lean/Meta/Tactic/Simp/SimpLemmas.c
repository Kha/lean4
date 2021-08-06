// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.SimpLemmas
// Imports: Init Lean.ScopedEnvExtension Lean.Util.Recognizers Lean.Meta.LevelDefEq Lean.Meta.DiscrTree Lean.Meta.AppBuilder Lean.Meta.Tactic.AuxLemma
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
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__3;
lean_object* l_Lean_ScopedEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_Meta_addSimpLemmaEntry___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474__match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__5;
lean_object* l_Lean_Meta_mkPropExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__7;
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore_match__2(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__16;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__1;
lean_object* l_Lean_Meta_SimpLemma_name_x3f___default;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__5;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__3;
static lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__3;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addSimpLemmaEntry(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpExtension___lambda__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_mkSimpLemmas___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_add_getName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__13;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___closed__1;
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_contains___at_Lean_Meta_addSimpLemmaEntry___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemma_getValue___boxed__const__1;
static lean_object* l_Lean_Meta_SimpLemma_getValue___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__3;
static lean_object* l_Lean_Meta_instInhabitedSimpLemmas___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedSimpLemmas;
static lean_object* l_Lean_Meta_instInhabitedSimpLemmas___closed__2;
static lean_object* l_Lean_Meta_instToFormatSimpLemma___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__1(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpLemmaEntry___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore_match__3___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__4(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore_match__1(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__7;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_mkSimpLemmas___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__24;
static lean_object* l_Lean_Meta_simpExtension___closed__7;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_addSimpLemma___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__4;
static uint64_t l_Lean_Meta_instInhabitedSimpLemma___closed__2;
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__2;
lean_object* l_Lean_Meta_simpExtension___lambda__3(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__2;
lean_object* l_id___rarg___boxed(lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_isDeclToUnfold___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_DiscrTree_instHashableKey;
lean_object* l_Lean_Meta_SimpLemma_getName(lean_object*);
extern lean_object* l_Lean_instHashableName;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__23;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__6;
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__5;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__21;
lean_object* l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
lean_object* l_Lean_Meta_simpExtension___lambda__6(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocessProof___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__1;
lean_object* l_Lean_Meta_mkSimpLemmas(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpLemmas_erase___rarg___closed__1;
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_addSimpLemmaEntry___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_registerTagAttribute___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__2(lean_object*);
static lean_object* l_Lean_Meta_SimpLemmas_erase___rarg___closed__4;
lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__22;
static lean_object* l_Lean_Meta_instInhabitedSimpLemma___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__1;
uint8_t l_USize_decLt(size_t, size_t);
static lean_object* l_Lean_Meta_simpExtension___closed__11;
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpLemmas_erase___rarg___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__10;
lean_object* l_Lean_Meta_simpExtension___lambda__7___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7___closed__2;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_addSimpLemma___spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__25;
static lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__3;
lean_object* l_Lean_Meta_SimpLemmas_erase___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1;
lean_object* l_List_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__14;
extern lean_object* l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_post___default;
lean_object* l_Lean_Meta_SimpLemmas_addDeclToUnfold(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_add_getName_x3f_match__1(lean_object*);
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocessProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpLemmas(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__1;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instToFormatSimpLemma(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__19;
static lean_object* l_Lean_Meta_SimpLemmas_pre___default___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__2;
lean_object* l_Lean_Meta_SimpLemmas_eraseCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_erase___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpLemma___closed__2;
static lean_object* l_Lean_Meta_simpExtension___closed__12;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__4;
lean_object* l_Lean_Meta_simpExtension___lambda__3___boxed(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_toUnfold___default;
static lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_erase___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474__match__1(lean_object*);
lean_object* l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7___boxed(lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpLemma___closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__6;
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__11;
lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpExtension;
lean_object* l_Lean_Meta_simpExtension___lambda__4___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_simpExtension___closed__2;
lean_object* l_Lean_Meta_SimpLemmas_add_getName_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binInsertM___at_Lean_Meta_addSimpLemmaEntry___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_erase___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpLemma___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__3;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instToMessageDataSimpLemma(lean_object*);
lean_object* l_List_mapM___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpLemmaEntry___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpExtension___lambda__4(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addSimpLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__17;
lean_object* l_Lean_Meta_SimpLemmas_erase___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__1;
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__4___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__8;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_DiscrTree_instBEqKey;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__5;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__2;
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpExtension___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_eraseCore___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_eraseCore___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addSimpLemma(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__4;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__4;
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore_match__3(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__4;
lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Meta_simpExtension___closed__5;
lean_object* l_List_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__9;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__8;
lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpLemma___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_erased___default;
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_isLemma___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__4;
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__2;
static lean_object* l_Lean_Meta_simpExtension___closed__8;
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpLemmas___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__9;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__1;
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm_match__1(lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_erase(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__7;
lean_object* l_Lean_Meta_addSimpLemmaEntry_updateLemmaNames_match__1(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474_(lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304_(lean_object*);
lean_object* l_Lean_Meta_simpExtension___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__4;
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpLemmas_addConst___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__2;
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__3;
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__3(lean_object*);
lean_object* l_Lean_Meta_instBEqSimpLemma___boxed(lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_lemmaNames___default;
lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_DiscrTree_instInhabitedKey;
lean_object* l_Lean_Meta_SimpLemma_getName_match__1(lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_pre___default;
lean_object* l_Lean_Meta_simpExtension___lambda__7(lean_object*);
static lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__1;
static lean_object* l_Lean_Meta_SimpLemma_getValue___closed__1;
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpLemma_getValue___closed__2;
lean_object* l_Lean_Meta_instInhabitedSimpLemma;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_addSimpLemmaEntry___spec__5(lean_object*, lean_object*, size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__1;
lean_object* l_Lean_Meta_SimpLemma_getName_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l_Lean_Meta_SimpLemma_getValue___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__1;
lean_object* l_Array_binInsertM___at_Lean_Meta_addSimpLemmaEntry___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_simpExtension___closed__3;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpLemma___closed__3;
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__10;
lean_object* l_Lean_PersistentEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_add(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_erase___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_SimpLemmas_isDeclToUnfold(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpLemmas___rarg___boxed(lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__13;
lean_object* l_Lean_Meta_SimpLemmas_eraseCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__12;
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___rarg(lean_object*);
static lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__3;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__26;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__6;
static lean_object* l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__1;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Meta_simpExtension___lambda__1(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__12;
lean_object* l_Lean_Meta_mkSimpLemmas___boxed__const__1;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_simpExtension___lambda__1___closed__2;
lean_object* l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__1(lean_object*);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpLemma___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instBEqExpr;
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_Lean_Meta_addSimpLemmaEntry___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_eraseCore(lean_object*);
lean_object* l_Lean_Meta_addSimpLemmaEntry_updateLemmaNames_match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedSimpLemma___closed__4;
lean_object* l_Lean_ScopedEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
static uint32_t l_Lean_Meta_simpExtension___lambda__1___closed__1;
lean_object* l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpExtension___lambda__6___boxed(lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_add_getName_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__6;
lean_object* l_Lean_Meta_SimpLemma_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_simpExtension___closed__6;
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__14;
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSimpLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instToFormatSimpLemma___closed__3;
lean_object* l_Lean_Meta_SimpLemmas_erase___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_addConst(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__15;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__5;
static lean_object* l_Lean_Meta_simpExtension___closed__10;
lean_object* l_List_map___at_Lean_mkConstWithLevelParams___spec__1(lean_object*);
static lean_object* l_Lean_Meta_simpExtension___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocessProof___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__3;
static lean_object* l_Lean_Meta_simpExtension___closed__4;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_SimpLemmas_erase___rarg___closed__3;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpLemmas_addConst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__18;
static lean_object* l_Lean_Meta_SimpLemma_getName___closed__2;
static lean_object* l_Lean_Meta_simpExtension___closed__9;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__5;
uint8_t l_Lean_Meta_instBEqSimpLemma(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7(lean_object*);
lean_object* l_Lean_Meta_SimpLemmas_addConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__2;
lean_object* l_Lean_Meta_SimpLemma_getName___boxed(lean_object*);
static lean_object* l_Lean_Meta_SimpLemma_getName___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addSimpLemmaEntry_updateLemmaNames(lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedSimpEntry;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__3;
static lean_object* l_Lean_Meta_instInhabitedSimpEntry___closed__1;
lean_object* l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_object*);
lean_object* l_Lean_Meta_getSimpLemmas___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__11;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__20;
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpExtension___lambda__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__2(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEqName;
static lean_object* l_Lean_Meta_instToFormatSimpLemma___closed__5;
uint8_t l_Lean_Meta_SimpLemmas_isLemma(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_SimpLemma_name_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpLemma___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static uint64_t _init_l_Lean_Meta_instInhabitedSimpLemma___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpLemma___closed__3() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_instInhabitedSimpLemma___closed__2;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpLemma___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_instInhabitedSimpLemma___closed__1;
x_3 = l_Lean_Meta_instInhabitedSimpLemma___closed__3;
x_4 = lean_unsigned_to_nat(0u);
x_5 = 0;
x_6 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*5 + 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpLemma() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedSimpLemma___closed__4;
return x_1;
}
}
lean_object* l_Lean_Meta_SimpLemma_getName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_SimpLemma_getName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SimpLemma_getName_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemma_getName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<unknown>");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemma_getName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_SimpLemma_getName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_SimpLemma_getName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_Meta_SimpLemma_getName___closed__2;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
return x_4;
}
}
}
lean_object* l_Lean_Meta_SimpLemma_getName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_SimpLemma_getName(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpLemma___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpLemma___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpLemma___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpLemma___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpLemma___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpLemma___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpLemma___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":perm");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpLemma___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpLemma___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_instToFormatSimpLemma(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_3 = l_Lean_Meta_SimpLemma_getName(x_1);
x_4 = 1;
x_5 = l_Lean_Name_toString(x_3, x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Nat_repr(x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_Meta_instToFormatSimpLemma___closed__2;
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Meta_instToFormatSimpLemma___closed__4;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
if (x_2 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Meta_instToFormatSimpLemma___closed__6;
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
lean_object* l_Lean_Meta_instToMessageDataSimpLemma(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
x_3 = l_Lean_Meta_SimpLemma_getName(x_1);
x_4 = 1;
x_5 = l_Lean_Name_toString(x_3, x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Nat_repr(x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_Meta_instToFormatSimpLemma___closed__2;
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Meta_instToFormatSimpLemma___closed__4;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
if (x_2 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_Meta_instToFormatSimpLemma___closed__6;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
uint8_t l_Lean_Meta_instBEqSimpLemma(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_expr_eqv(x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_instBEqSimpLemma___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_instBEqSimpLemma(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemmas_pre___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemmas_pre___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SimpLemmas_pre___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemmas_post___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_SimpLemmas_pre___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemmas_lemmaNames___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemmas_toUnfold___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemmas_erased___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpLemmas___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpLemmas___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instInhabitedSimpLemmas___closed__1;
x_2 = l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1;
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpLemmas() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedSimpLemmas___closed__2;
return x_1;
}
}
lean_object* l_Lean_Meta_addSimpLemmaEntry_updateLemmaNames_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_addSimpLemmaEntry_updateLemmaNames_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_addSimpLemmaEntry_updateLemmaNames_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_addSimpLemmaEntry_updateLemmaNames(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Name_instBEqName;
x_6 = l_Lean_instHashableName;
x_7 = lean_box(0);
x_8 = l_Std_PersistentHashMap_insert___rarg(x_5, x_6, x_2, x_4, x_7);
return x_8;
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_addSimpLemmaEntry___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_expr_eqv(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = x_3 + x_10;
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
uint8_t l_Array_contains___at_Lean_Meta_addSimpLemmaEntry___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Meta_addSimpLemmaEntry___spec__5(x_2, x_1, x_9, x_10);
return x_11;
}
}
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_Lean_Meta_addSimpLemmaEntry___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Array_contains___at_Lean_Meta_addSimpLemmaEntry___spec__4(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_array_push(x_1, x_2);
return x_4;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
static lean_object* _init_l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_instInhabitedTrie(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_DiscrTree_instInhabitedKey;
x_2 = l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7___closed__2;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instInhabitedSimpLemma___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__1;
x_2 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_nat_add(x_7, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
x_12 = l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7___closed__2;
x_13 = lean_array_get(x_12, x_5, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_6, 0);
x_16 = l_Lean_Meta_DiscrTree_Key_lt(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_8);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_15, x_14);
lean_dec(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_7);
x_18 = lean_array_get_size(x_5);
x_19 = lean_nat_dec_lt(x_11, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_array_fget(x_5, x_11);
x_21 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__3;
x_22 = lean_array_fset(x_5, x_11, x_21);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_ctor_get(x_20, 0);
lean_dec(x_25);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
x_28 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpLemmaEntry___spec__2(x_1, x_2, x_27, x_24);
lean_dec(x_27);
lean_ctor_set(x_20, 1, x_28);
lean_ctor_set(x_20, 0, x_4);
x_29 = lean_array_fset(x_22, x_11, x_20);
lean_dec(x_11);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_3, x_31);
x_33 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpLemmaEntry___spec__2(x_1, x_2, x_32, x_30);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_array_fset(x_22, x_11, x_34);
lean_dec(x_11);
return x_35;
}
}
}
else
{
x_8 = x_11;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_14);
x_37 = lean_nat_dec_eq(x_11, x_7);
if (x_37 == 0)
{
lean_dec(x_7);
x_7 = x_11;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_11);
lean_dec(x_8);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_3, x_39);
x_41 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_nat_add(x_7, x_39);
lean_dec(x_7);
x_44 = l_Array_insertAt___rarg(x_5, x_43, x_42);
lean_dec(x_43);
return x_44;
}
}
}
}
lean_object* l_Array_binInsertM___at_Lean_Meta_addSimpLemmaEntry___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Array_isEmpty___rarg(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7___closed__2;
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get(x_8, x_5, x_9);
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_DiscrTree_Key_lt(x_11, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_11);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_5);
x_16 = lean_nat_dec_lt(x_9, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_array_fget(x_5, x_9);
x_18 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__3;
x_19 = lean_array_fset(x_5, x_9, x_18);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 0);
lean_dec(x_22);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_3, x_23);
x_25 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpLemmaEntry___spec__2(x_1, x_2, x_24, x_21);
lean_dec(x_24);
lean_ctor_set(x_17, 1, x_25);
lean_ctor_set(x_17, 0, x_4);
x_26 = lean_array_fset(x_19, x_9, x_17);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_3, x_28);
x_30 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpLemmaEntry___spec__2(x_1, x_2, x_29, x_27);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_fset(x_19, x_9, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7(x_5);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Meta_DiscrTree_Key_lt(x_34, x_11);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Meta_DiscrTree_Key_lt(x_11, x_34);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_array_get_size(x_5);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_37, x_38);
x_40 = lean_nat_dec_lt(x_39, x_37);
lean_dec(x_37);
if (x_40 == 0)
{
lean_dec(x_39);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_array_fget(x_5, x_39);
x_42 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__3;
x_43 = lean_array_fset(x_5, x_39, x_42);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_41, 1);
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = lean_nat_add(x_3, x_38);
x_48 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpLemmaEntry___spec__2(x_1, x_2, x_47, x_45);
lean_dec(x_47);
lean_ctor_set(x_41, 1, x_48);
lean_ctor_set(x_41, 0, x_4);
x_49 = lean_array_fset(x_43, x_39, x_41);
lean_dec(x_39);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
x_51 = lean_nat_add(x_3, x_38);
x_52 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpLemmaEntry___spec__2(x_1, x_2, x_51, x_50);
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_4);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_array_fset(x_43, x_39, x_53);
lean_dec(x_39);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_array_get_size(x_5);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_sub(x_55, x_56);
lean_dec(x_55);
x_58 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_34);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_3, x_59);
x_61 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_4);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_array_push(x_5, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_12);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_3, x_64);
x_66 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_65);
lean_dec(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_4);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Array_insertAt___rarg(x_5, x_9, x_67);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_3, x_69);
x_71 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_4);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_array_push(x_5, x_72);
return x_73;
}
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpLemmaEntry___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_Lean_Meta_addSimpLemmaEntry___spec__3(x_6, x_2);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_1, x_3);
x_12 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__2;
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Array_binInsertM___at_Lean_Meta_addSimpLemmaEntry___spec__6(x_1, x_2, x_3, x_11, x_7, x_13);
lean_dec(x_13);
lean_ctor_set(x_4, 1, x_14);
return x_4;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_Lean_Meta_addSimpLemmaEntry___spec__3(x_15, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_array_fget(x_1, x_3);
x_22 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__2;
lean_inc(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Array_binInsertM___at_Lean_Meta_addSimpLemmaEntry___spec__6(x_1, x_2, x_3, x_21, x_16, x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_instInhabitedDiscrTree(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.DiscrTree");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.DiscrTree.insertCore");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid key sequence");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__2;
x_2 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__3;
x_3 = lean_unsigned_to_nat(352u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___rarg(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Meta_DiscrTree_instInhabitedKey;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_2, x_6);
x_8 = l_Lean_Meta_DiscrTree_instBEqKey;
x_9 = l_Lean_Meta_DiscrTree_instHashableKey;
lean_inc(x_7);
lean_inc(x_1);
x_10 = l_Std_PersistentHashMap_find_x3f___rarg(x_8, x_9, x_1, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_11);
x_13 = l_Std_PersistentHashMap_insert___rarg(x_8, x_9, x_1, x_7, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpLemmaEntry___spec__2(x_2, x_3, x_15, x_14);
x_17 = l_Std_PersistentHashMap_insert___rarg(x_8, x_9, x_1, x_7, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_1);
x_18 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__1;
x_19 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__5;
x_20 = lean_panic_fn(x_18, x_19);
return x_20;
}
}
}
lean_object* l_Lean_Meta_addSimpLemmaEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_inc(x_2);
x_8 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1(x_5, x_7, x_2);
lean_dec(x_7);
x_9 = l_Lean_Meta_addSimpLemmaEntry_updateLemmaNames(x_2, x_6);
lean_ctor_set(x_1, 2, x_9);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_inc(x_2);
x_16 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1(x_10, x_15, x_2);
lean_dec(x_15);
x_17 = l_Lean_Meta_addSimpLemmaEntry_updateLemmaNames(x_2, x_12);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_13);
lean_ctor_set(x_18, 4, x_14);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_inc(x_2);
x_23 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1(x_20, x_22, x_2);
lean_dec(x_22);
x_24 = l_Lean_Meta_addSimpLemmaEntry_updateLemmaNames(x_2, x_21);
lean_ctor_set(x_1, 2, x_24);
lean_ctor_set(x_1, 1, x_23);
return x_1;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 2);
x_28 = lean_ctor_get(x_1, 3);
x_29 = lean_ctor_get(x_1, 4);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
lean_inc(x_2);
x_31 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1(x_26, x_30, x_2);
lean_dec(x_30);
x_32 = l_Lean_Meta_addSimpLemmaEntry_updateLemmaNames(x_2, x_27);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_28);
lean_ctor_set(x_33, 4, x_29);
return x_33;
}
}
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_addSimpLemmaEntry___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_addSimpLemmaEntry___spec__5(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_contains___at_Lean_Meta_addSimpLemmaEntry___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_Meta_addSimpLemmaEntry___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_binInsertM___at_Lean_Meta_addSimpLemmaEntry___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binInsertM___at_Lean_Meta_addSimpLemmaEntry___spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpLemmaEntry___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_addSimpLemmaEntry___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_SimpLemmas_addDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lean_Name_instBEqName;
x_6 = l_Lean_instHashableName;
x_7 = lean_box(0);
x_8 = l_Std_PersistentHashMap_insert___rarg(x_5, x_6, x_4, x_2, x_7);
lean_ctor_set(x_1, 3, x_8);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_1, 4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_14 = l_Lean_Name_instBEqName;
x_15 = l_Lean_instHashableName;
x_16 = lean_box(0);
x_17 = l_Std_PersistentHashMap_insert___rarg(x_14, x_15, x_12, x_2, x_16);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_10);
lean_ctor_set(x_18, 2, x_11);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set(x_18, 4, x_13);
return x_18;
}
}
}
uint8_t l_Lean_Meta_SimpLemmas_isDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__4(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_SimpLemmas_isDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpLemmas_isDeclToUnfold(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_Meta_SimpLemmas_isLemma(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__4(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_SimpLemmas_isLemma___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpLemmas_isLemma(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_SimpLemmas_eraseCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_ctor_get(x_3, 3);
x_10 = lean_ctor_get(x_3, 4);
x_11 = l_Lean_Name_instBEqName;
x_12 = l_Lean_instHashableName;
lean_inc(x_4);
x_13 = l_Std_PersistentHashMap_erase___rarg(x_11, x_12, x_8, x_4);
lean_inc(x_4);
x_14 = l_Std_PersistentHashMap_erase___rarg(x_11, x_12, x_9, x_4);
x_15 = lean_box(0);
x_16 = l_Std_PersistentHashMap_insert___rarg(x_11, x_12, x_10, x_4, x_15);
lean_ctor_set(x_3, 4, x_16);
lean_ctor_set(x_3, 3, x_14);
lean_ctor_set(x_3, 2, x_13);
x_17 = lean_apply_2(x_6, lean_box(0), x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_23 = l_Lean_Name_instBEqName;
x_24 = l_Lean_instHashableName;
lean_inc(x_4);
x_25 = l_Std_PersistentHashMap_erase___rarg(x_23, x_24, x_20, x_4);
lean_inc(x_4);
x_26 = l_Std_PersistentHashMap_erase___rarg(x_23, x_24, x_21, x_4);
x_27 = lean_box(0);
x_28 = l_Std_PersistentHashMap_insert___rarg(x_23, x_24, x_22, x_4, x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_19);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_26);
lean_ctor_set(x_29, 4, x_28);
x_30 = lean_apply_2(x_6, lean_box(0), x_29);
return x_30;
}
}
}
lean_object* l_Lean_Meta_SimpLemmas_eraseCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SimpLemmas_eraseCore___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_SimpLemmas_eraseCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SimpLemmas_eraseCore___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Meta_SimpLemmas_erase___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_SimpLemmas_eraseCore___rarg(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemmas_erase___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemmas_erase___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SimpLemmas_erase___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemmas_erase___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not have [simp] attribute");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemmas_erase___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_SimpLemmas_erase___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SimpLemmas_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_SimpLemmas_erase___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
lean_inc(x_4);
lean_inc(x_3);
x_6 = l_Lean_Meta_SimpLemmas_isLemma(x_3, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_inc(x_4);
x_7 = l_Lean_Meta_SimpLemmas_isDeclToUnfold(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_10 = l_Lean_Meta_SimpLemmas_erase___rarg___closed__2;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Meta_SimpLemmas_erase___rarg___closed__4;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___rarg(x_1, x_2, x_13);
x_15 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_14, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_18, lean_box(0), x_19);
x_21 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_20, x_5);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = lean_apply_2(x_24, lean_box(0), x_25);
x_27 = lean_apply_4(x_22, lean_box(0), lean_box(0), x_26, x_5);
return x_27;
}
}
}
lean_object* l_Lean_Meta_SimpLemmas_erase(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SimpLemmas_erase___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_SimpLemmas_erase___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_SimpLemmas_erase___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpEntry___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instInhabitedSimpLemma___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpEntry() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedSimpEntry___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474__match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474__match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474__match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Meta_addSimpLemmaEntry(x_1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Meta_SimpLemmas_addDeclToUnfold(x_1, x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simpExt");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_SimpLemmas_pre___default___closed__1;
x_2 = l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1;
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__3;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__5;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__6;
x_3 = l_Lean_registerSimpleScopedEnvExtension___rarg(x_2, x_1);
return x_3;
}
}
static uint32_t _init_l_Lean_Meta_simpExtension___lambda__1___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_simpExtension___lambda__1___closed__2() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_simpExtension___lambda__1___closed__1;
x_3 = l_Lean_Meta_instToFormatSimpLemma___closed__3;
x_4 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_simpExtension___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_simpExtension___lambda__1___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_simpExtension___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_simpExtension___lambda__1___closed__2;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_simpExtension___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_instInhabitedSimpEntry___closed__1;
return x_2;
}
}
lean_object* l_Lean_Meta_simpExtension___lambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Meta_simpExtension___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_simpExtension___lambda__1___closed__2;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Meta_simpExtension___lambda__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_instInhabitedSimpLemma___closed__1;
return x_2;
}
}
lean_object* l_Lean_Meta_simpExtension___lambda__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_simpExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_simpExtension___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_simpExtension___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_simpExtension___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_simpExtension___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_simpExtension___lambda__3___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_simpExtension___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_simpExtension___lambda__4___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_simpExtension___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_simpExtension___closed__1;
x_3 = l_Lean_Meta_simpExtension___closed__2;
x_4 = l_Lean_Meta_simpExtension___closed__3;
x_5 = l_Lean_Meta_simpExtension___closed__4;
x_6 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__5;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_simpExtension___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_simpExtension___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_simpExtension___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_simpExtension___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_simpExtension___lambda__5___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_simpExtension___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_simpExtension___lambda__6___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_simpExtension___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_simpExtension___lambda__7___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_simpExtension___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Meta_simpExtension___closed__7;
x_2 = lean_box(0);
x_3 = l_Lean_Meta_simpExtension___closed__8;
x_4 = l_Lean_Meta_simpExtension___closed__4;
x_5 = l_Lean_Meta_simpExtension___closed__9;
x_6 = l_Lean_Meta_simpExtension___closed__10;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_simpExtension___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_simpExtension___closed__5;
x_2 = l_Lean_Meta_simpExtension___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_simpExtension___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_simpExtension___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_simpExtension___lambda__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_simpExtension___lambda__3(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_simpExtension___lambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_simpExtension___lambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_simpExtension___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_simpExtension___lambda__5(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_simpExtension___lambda__6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_simpExtension___lambda__6(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_simpExtension___lambda__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_simpExtension___lambda__7(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_2, sizeof(void*)*1);
x_16 = lean_box_uint64(x_13);
x_17 = lean_box_uint64(x_15);
x_18 = lean_apply_6(x_6, x_1, x_12, x_16, x_2, x_14, x_17);
return x_18;
}
case 10:
{
lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_6);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
x_21 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_22 = lean_box_uint64(x_21);
x_23 = lean_apply_4(x_5, x_1, x_19, x_20, x_22);
return x_23;
}
default: 
{
lean_object* x_24; 
lean_dec(x_6);
lean_dec(x_5);
x_24 = lean_apply_2(x_11, x_1, x_2);
return x_24;
}
}
}
case 5:
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_11);
lean_dec(x_5);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_31 = lean_box_uint64(x_27);
x_32 = lean_box_uint64(x_30);
x_33 = lean_apply_6(x_3, x_25, x_26, x_31, x_28, x_29, x_32);
return x_33;
}
case 10:
{
lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_3);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
x_36 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_37 = lean_box_uint64(x_36);
x_38 = lean_apply_4(x_5, x_1, x_34, x_35, x_37);
return x_38;
}
default: 
{
lean_object* x_39; 
lean_dec(x_5);
lean_dec(x_3);
x_39 = lean_apply_2(x_11, x_1, x_2);
return x_39;
}
}
}
case 6:
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_11);
lean_dec(x_5);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 2);
lean_inc(x_46);
x_47 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_dec(x_2);
x_48 = lean_box_uint64(x_43);
x_49 = lean_box_uint64(x_47);
x_50 = lean_apply_8(x_8, x_40, x_41, x_42, x_48, x_44, x_45, x_46, x_49);
return x_50;
}
case 10:
{
lean_object* x_51; lean_object* x_52; uint64_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_11);
lean_dec(x_8);
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
x_53 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_54 = lean_box_uint64(x_53);
x_55 = lean_apply_4(x_5, x_1, x_51, x_52, x_54);
return x_55;
}
default: 
{
lean_object* x_56; 
lean_dec(x_8);
lean_dec(x_5);
x_56 = lean_apply_2(x_11, x_1, x_2);
return x_56;
}
}
}
case 7:
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint64_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_11);
lean_dec(x_5);
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 2);
lean_inc(x_59);
x_60 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_61 = lean_ctor_get(x_2, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_2, 2);
lean_inc(x_63);
x_64 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_dec(x_2);
x_65 = lean_box_uint64(x_60);
x_66 = lean_box_uint64(x_64);
x_67 = lean_apply_8(x_7, x_57, x_58, x_59, x_65, x_61, x_62, x_63, x_66);
return x_67;
}
case 10:
{
lean_object* x_68; lean_object* x_69; uint64_t x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_11);
lean_dec(x_7);
x_68 = lean_ctor_get(x_2, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_2, 1);
lean_inc(x_69);
x_70 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_71 = lean_box_uint64(x_70);
x_72 = lean_apply_4(x_5, x_1, x_68, x_69, x_71);
return x_72;
}
default: 
{
lean_object* x_73; 
lean_dec(x_7);
lean_dec(x_5);
x_73 = lean_apply_2(x_11, x_1, x_2);
return x_73;
}
}
}
case 8:
{
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 8:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint64_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint64_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_11);
lean_dec(x_5);
x_74 = lean_ctor_get(x_1, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_1, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_1, 3);
lean_inc(x_77);
x_78 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_79 = lean_ctor_get(x_2, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_2, 3);
lean_inc(x_82);
x_83 = lean_ctor_get_uint64(x_2, sizeof(void*)*4);
lean_dec(x_2);
x_84 = lean_box_uint64(x_78);
x_85 = lean_box_uint64(x_83);
x_86 = lean_apply_10(x_9, x_74, x_75, x_76, x_77, x_84, x_79, x_80, x_81, x_82, x_85);
return x_86;
}
case 10:
{
lean_object* x_87; lean_object* x_88; uint64_t x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_11);
lean_dec(x_9);
x_87 = lean_ctor_get(x_2, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_2, 1);
lean_inc(x_88);
x_89 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_90 = lean_box_uint64(x_89);
x_91 = lean_apply_4(x_5, x_1, x_87, x_88, x_90);
return x_91;
}
default: 
{
lean_object* x_92; 
lean_dec(x_9);
lean_dec(x_5);
x_92 = lean_apply_2(x_11, x_1, x_2);
return x_92;
}
}
}
case 10:
{
lean_object* x_93; lean_object* x_94; uint64_t x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_93 = lean_ctor_get(x_1, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_1, 1);
lean_inc(x_94);
x_95 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_96 = lean_box_uint64(x_95);
x_97 = lean_apply_4(x_4, x_93, x_94, x_96, x_2);
return x_97;
}
case 11:
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 10:
{
lean_object* x_98; lean_object* x_99; uint64_t x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_11);
lean_dec(x_10);
x_98 = lean_ctor_get(x_2, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_2, 1);
lean_inc(x_99);
x_100 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_101 = lean_box_uint64(x_100);
x_102 = lean_apply_4(x_5, x_1, x_98, x_99, x_101);
return x_102;
}
case 11:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint64_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint64_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_11);
lean_dec(x_5);
x_103 = lean_ctor_get(x_1, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_1, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_1, 2);
lean_inc(x_105);
x_106 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_107 = lean_ctor_get(x_2, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_2, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_2, 2);
lean_inc(x_109);
x_110 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_dec(x_2);
x_111 = lean_box_uint64(x_106);
x_112 = lean_box_uint64(x_110);
x_113 = lean_apply_8(x_10, x_103, x_104, x_105, x_111, x_107, x_108, x_109, x_112);
return x_113;
}
default: 
{
lean_object* x_114; 
lean_dec(x_10);
lean_dec(x_5);
x_114 = lean_apply_2(x_11, x_1, x_2);
return x_114;
}
}
}
default: 
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_115; lean_object* x_116; uint64_t x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_11);
x_115 = lean_ctor_get(x_2, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_2, 1);
lean_inc(x_116);
x_117 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_118 = lean_box_uint64(x_117);
x_119 = lean_apply_4(x_5, x_1, x_115, x_116, x_118);
return x_119;
}
else
{
lean_object* x_120; 
lean_dec(x_5);
x_120 = lean_apply_2(x_11, x_1, x_2);
return x_120;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm_match__1___rarg), 11, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__2___rarg), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_expr_instantiate1(x_1, x_3);
lean_dec(x_1);
x_10 = lean_expr_instantiate1(x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_11 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm(x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
case 10:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
default: 
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm(x_14, x_16, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_19);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_1 = x_15;
x_2 = x_17;
x_7 = x_25;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
case 10:
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_dec(x_2);
x_2 = x_31;
goto _start;
}
default: 
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_7);
return x_35;
}
}
}
case 6:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 2);
lean_inc(x_40);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_37);
x_41 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm(x_37, x_39, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
lean_dec(x_42);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___lambda__1), 8, 2);
lean_closure_set(x_49, 0, x_38);
lean_closure_set(x_49, 1, x_40);
x_50 = 0;
x_51 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__1___rarg(x_36, x_50, x_37, x_49, x_3, x_4, x_5, x_6, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
return x_41;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_41, 0);
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_41);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
case 10:
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
lean_dec(x_2);
x_2 = x_56;
goto _start;
}
default: 
{
uint8_t x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_box(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_7);
return x_60;
}
}
}
case 7:
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 2);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_ctor_get(x_2, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 2);
lean_inc(x_65);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_62);
x_66 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm(x_62, x_64, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
if (x_68 == 0)
{
uint8_t x_69; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_66, 0);
lean_dec(x_70);
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
lean_dec(x_67);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_dec(x_66);
x_74 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___lambda__1), 8, 2);
lean_closure_set(x_74, 0, x_63);
lean_closure_set(x_74, 1, x_65);
x_75 = 0;
x_76 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__1___rarg(x_61, x_75, x_62, x_74, x_3, x_4, x_5, x_6, x_73);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_66);
if (x_77 == 0)
{
return x_66;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_66, 0);
x_79 = lean_ctor_get(x_66, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_66);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
case 10:
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_2, 1);
lean_inc(x_81);
lean_dec(x_2);
x_2 = x_81;
goto _start;
}
default: 
{
uint8_t x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_83 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_84 = lean_box(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_7);
return x_85;
}
}
}
case 8:
{
switch (lean_obj_tag(x_2)) {
case 8:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_86 = lean_ctor_get(x_1, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_1, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_1, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 3);
lean_inc(x_89);
lean_dec(x_1);
x_90 = lean_ctor_get(x_2, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_2, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_2, 3);
lean_inc(x_92);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_87);
x_93 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm(x_87, x_90, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
if (x_95 == 0)
{
uint8_t x_96; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_96 = !lean_is_exclusive(x_93);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_93, 0);
lean_dec(x_97);
return x_93;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_dec(x_93);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_94);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_94);
x_100 = lean_ctor_get(x_93, 1);
lean_inc(x_100);
lean_dec(x_93);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_88);
x_101 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm(x_88, x_91, x_3, x_4, x_5, x_6, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
if (x_103 == 0)
{
uint8_t x_104; 
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_104 = !lean_is_exclusive(x_101);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_101, 0);
lean_dec(x_105);
return x_101;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
lean_dec(x_101);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_102);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_102);
x_108 = lean_ctor_get(x_101, 1);
lean_inc(x_108);
lean_dec(x_101);
x_109 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___lambda__1), 8, 2);
lean_closure_set(x_109, 0, x_89);
lean_closure_set(x_109, 1, x_92);
x_110 = l_Lean_Meta_withLetDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__2___rarg(x_86, x_87, x_88, x_109, x_3, x_4, x_5, x_6, x_108);
return x_110;
}
}
else
{
uint8_t x_111; 
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = !lean_is_exclusive(x_101);
if (x_111 == 0)
{
return x_101;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_101, 0);
x_113 = lean_ctor_get(x_101, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_101);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_115 = !lean_is_exclusive(x_93);
if (x_115 == 0)
{
return x_93;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_93, 0);
x_117 = lean_ctor_get(x_93, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_93);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
case 10:
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_2, 1);
lean_inc(x_119);
lean_dec(x_2);
x_2 = x_119;
goto _start;
}
default: 
{
uint8_t x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_121 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_122 = lean_box(x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_7);
return x_123;
}
}
}
case 10:
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_1, 1);
lean_inc(x_124);
lean_dec(x_1);
x_1 = x_124;
goto _start;
}
case 11:
{
switch (lean_obj_tag(x_2)) {
case 10:
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_2, 1);
lean_inc(x_126);
lean_dec(x_2);
x_2 = x_126;
goto _start;
}
case 11:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_1, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_1, 2);
lean_inc(x_129);
lean_dec(x_1);
x_130 = lean_ctor_get(x_2, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_2, 2);
lean_inc(x_131);
lean_dec(x_2);
x_132 = lean_nat_dec_eq(x_128, x_130);
lean_dec(x_130);
lean_dec(x_128);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_133 = lean_box(x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_7);
return x_134;
}
else
{
x_1 = x_129;
x_2 = x_131;
goto _start;
}
}
default: 
{
uint8_t x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_136 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_137 = lean_box(x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_7);
return x_138;
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_2, 1);
lean_inc(x_139);
lean_dec(x_2);
x_2 = x_139;
goto _start;
}
else
{
uint8_t x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_141 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_142 = lean_box(x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_7);
return x_143;
}
}
}
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm___spec__1___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isEq(x_2);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess___lambda__1___boxed), 7, 0);
return x_1;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess___closed__1;
x_8 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = 0;
x_17 = 1;
lean_inc(x_3);
lean_inc(x_1);
x_18 = l_Lean_Meta_mkLambdaFVars(x_1, x_14, x_16, x_17, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_21 = l_Lean_Meta_mkForallFVars(x_1, x_15, x_16, x_17, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_11, 1, x_22);
lean_ctor_set(x_11, 0, x_19);
x_24 = l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_ctor_set(x_2, 1, x_26);
lean_ctor_set(x_24, 0, x_2);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_2, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_free_object(x_2);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_19);
lean_free_object(x_11);
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
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
lean_free_object(x_11);
lean_dec(x_15);
lean_free_object(x_2);
lean_dec(x_13);
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
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_2, 1);
x_43 = lean_ctor_get(x_11, 0);
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_11);
x_45 = 0;
x_46 = 1;
lean_inc(x_3);
lean_inc(x_1);
x_47 = l_Lean_Meta_mkLambdaFVars(x_1, x_43, x_45, x_46, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_50 = l_Lean_Meta_mkForallFVars(x_1, x_44, x_45, x_46, x_3, x_4, x_5, x_6, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___spec__1(x_1, x_42, x_3, x_4, x_5, x_6, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
lean_ctor_set(x_2, 1, x_55);
lean_ctor_set(x_2, 0, x_53);
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_2);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_53);
lean_free_object(x_2);
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_61 = x_54;
} else {
 lean_dec_ref(x_54);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_48);
lean_free_object(x_2);
lean_dec(x_42);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_63 = lean_ctor_get(x_50, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_65 = x_50;
} else {
 lean_dec_ref(x_50);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_44);
lean_free_object(x_2);
lean_dec(x_42);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_67 = lean_ctor_get(x_47, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_47, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_69 = x_47;
} else {
 lean_dec_ref(x_47);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_2, 0);
x_72 = lean_ctor_get(x_2, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_2);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_75 = x_71;
} else {
 lean_dec_ref(x_71);
 x_75 = lean_box(0);
}
x_76 = 0;
x_77 = 1;
lean_inc(x_3);
lean_inc(x_1);
x_78 = l_Lean_Meta_mkLambdaFVars(x_1, x_73, x_76, x_77, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_81 = l_Lean_Meta_mkForallFVars(x_1, x_74, x_76, x_77, x_3, x_4, x_5, x_6, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
if (lean_is_scalar(x_75)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_75;
}
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___spec__1(x_1, x_72, x_3, x_4, x_5, x_6, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_86);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_84);
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_85, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_93 = x_85;
} else {
 lean_dec_ref(x_85);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_79);
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_95 = lean_ctor_get(x_81, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_81, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_97 = x_81;
} else {
 lean_dec_ref(x_81);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_99 = lean_ctor_get(x_78, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_78, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_101 = x_78;
} else {
 lean_dec_ref(x_78);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
x_9 = l_Lean_mkAppN(x_1, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess(x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___spec__1(x_2, x_11, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Iff");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Ne");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Not");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("And");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("True");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__10;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("False");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__13;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_whnf(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Expr_isForall(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isEq(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_free_object(x_8);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__2;
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Expr_isAppOfArity(x_10, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__4;
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Expr_isAppOfArity(x_10, x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__6;
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Expr_isAppOfArity(x_10, x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__8;
x_24 = l_Lean_Expr_isAppOfArity(x_10, x_23, x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_box(0);
x_26 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__11;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_27 = l_Lean_Meta_mkEq(x_10, x_26, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_mkEqTrue(x_1, x_3, x_4, x_5, x_6, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_28);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_25);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_28);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
return x_30;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_30);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_27);
if (x_44 == 0)
{
return x_27;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_27, 0);
x_46 = lean_ctor_get(x_27, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_27);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = l_Lean_Expr_appFn_x21(x_10);
x_49 = l_Lean_Expr_appArg_x21(x_48);
lean_dec(x_48);
x_50 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
x_51 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_52 = l_Lean_mkProj(x_23, x_51, x_1);
x_53 = l_Lean_mkProj(x_23, x_21, x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_54 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess(x_52, x_49, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess(x_53, x_50, x_3, x_4, x_5, x_6, x_56);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = l_List_append___rarg(x_55, x_59);
lean_ctor_set(x_57, 0, x_60);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_57, 0);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_57);
x_63 = l_List_append___rarg(x_55, x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_55);
x_65 = !lean_is_exclusive(x_57);
if (x_65 == 0)
{
return x_57;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_57, 0);
x_67 = lean_ctor_get(x_57, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_57);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_54);
if (x_69 == 0)
{
return x_54;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_54, 0);
x_71 = lean_ctor_get(x_54, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_54);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
x_74 = lean_box(0);
x_75 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__14;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_76 = l_Lean_Meta_mkEq(x_73, x_75, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Meta_mkEqFalse(x_1, x_3, x_4, x_5, x_6, x_78);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_79, 0, x_83);
return x_79;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_79, 0);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_79);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_77);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_74);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_dec(x_77);
x_89 = !lean_is_exclusive(x_79);
if (x_89 == 0)
{
return x_79;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_79, 0);
x_91 = lean_ctor_get(x_79, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_79);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_76);
if (x_93 == 0)
{
return x_76;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_76, 0);
x_95 = lean_ctor_get(x_76, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_76);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = l_Lean_Expr_appFn_x21(x_10);
x_98 = l_Lean_Expr_appArg_x21(x_97);
lean_dec(x_97);
x_99 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_100 = l_Lean_Meta_mkEq(x_98, x_99, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_box(0);
x_104 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__14;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_105 = l_Lean_Meta_mkEq(x_101, x_104, x_3, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Meta_mkEqFalse(x_1, x_3, x_4, x_5, x_6, x_107);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_106);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_103);
lean_ctor_set(x_108, 0, x_112);
return x_108;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_108, 0);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_108);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_106);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_103);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
return x_117;
}
}
else
{
uint8_t x_118; 
lean_dec(x_106);
x_118 = !lean_is_exclusive(x_108);
if (x_118 == 0)
{
return x_108;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_108, 0);
x_120 = lean_ctor_get(x_108, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_108);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
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
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_105);
if (x_122 == 0)
{
return x_105;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_105, 0);
x_124 = lean_ctor_get(x_105, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_105);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_100);
if (x_126 == 0)
{
return x_100;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_100, 0);
x_128 = lean_ctor_get(x_100, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_100);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = l_Lean_Expr_appFn_x21(x_10);
x_131 = l_Lean_Expr_appArg_x21(x_130);
lean_dec(x_130);
x_132 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_133 = l_Lean_Meta_mkEq(x_131, x_132, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lean_Meta_mkPropExt(x_1, x_3, x_4, x_5, x_6, x_135);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_134);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_136, 0, x_141);
return x_136;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_136, 0);
x_143 = lean_ctor_get(x_136, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_136);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_134);
x_145 = lean_box(0);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_143);
return x_147;
}
}
else
{
uint8_t x_148; 
lean_dec(x_134);
x_148 = !lean_is_exclusive(x_136);
if (x_148 == 0)
{
return x_136;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_136, 0);
x_150 = lean_ctor_get(x_136, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_136);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_133);
if (x_152 == 0)
{
return x_133;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_133, 0);
x_154 = lean_ctor_get(x_133, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_133);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_1);
lean_ctor_set(x_156, 1, x_10);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_8, 0, x_158);
return x_8;
}
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_free_object(x_8);
x_159 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___lambda__1), 8, 1);
lean_closure_set(x_159, 0, x_1);
x_160 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_10, x_159, x_3, x_4, x_5, x_6, x_11);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_8, 0);
x_162 = lean_ctor_get(x_8, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_8);
x_163 = l_Lean_Expr_isForall(x_161);
if (x_163 == 0)
{
uint8_t x_164; 
x_164 = l_Lean_Expr_isEq(x_161);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_165 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__2;
x_166 = lean_unsigned_to_nat(2u);
x_167 = l_Lean_Expr_isAppOfArity(x_161, x_165, x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__4;
x_169 = lean_unsigned_to_nat(3u);
x_170 = l_Lean_Expr_isAppOfArity(x_161, x_168, x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__6;
x_172 = lean_unsigned_to_nat(1u);
x_173 = l_Lean_Expr_isAppOfArity(x_161, x_171, x_172);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
x_174 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__8;
x_175 = l_Lean_Expr_isAppOfArity(x_161, x_174, x_166);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_box(0);
x_177 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__11;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_178 = l_Lean_Meta_mkEq(x_161, x_177, x_3, x_4, x_5, x_6, x_162);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = l_Lean_Meta_mkEqTrue(x_1, x_3, x_4, x_5, x_6, x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_184 = x_181;
} else {
 lean_dec_ref(x_181);
 x_184 = lean_box(0);
}
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_179);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_176);
if (lean_is_scalar(x_184)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_184;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_183);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_179);
x_188 = lean_ctor_get(x_181, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_181, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_190 = x_181;
} else {
 lean_dec_ref(x_181);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_192 = lean_ctor_get(x_178, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_178, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_194 = x_178;
} else {
 lean_dec_ref(x_178);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_196 = l_Lean_Expr_appFn_x21(x_161);
x_197 = l_Lean_Expr_appArg_x21(x_196);
lean_dec(x_196);
x_198 = l_Lean_Expr_appArg_x21(x_161);
lean_dec(x_161);
x_199 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_200 = l_Lean_mkProj(x_174, x_199, x_1);
x_201 = l_Lean_mkProj(x_174, x_172, x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_202 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess(x_200, x_197, x_3, x_4, x_5, x_6, x_162);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess(x_201, x_198, x_3, x_4, x_5, x_6, x_204);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_208 = x_205;
} else {
 lean_dec_ref(x_205);
 x_208 = lean_box(0);
}
x_209 = l_List_append___rarg(x_203, x_206);
if (lean_is_scalar(x_208)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_208;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_207);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_203);
x_211 = lean_ctor_get(x_205, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_205, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_213 = x_205;
} else {
 lean_dec_ref(x_205);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_201);
lean_dec(x_198);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_215 = lean_ctor_get(x_202, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_202, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_217 = x_202;
} else {
 lean_dec_ref(x_202);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_219 = l_Lean_Expr_appArg_x21(x_161);
lean_dec(x_161);
x_220 = lean_box(0);
x_221 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__14;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_222 = l_Lean_Meta_mkEq(x_219, x_221, x_3, x_4, x_5, x_6, x_162);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = l_Lean_Meta_mkEqFalse(x_1, x_3, x_4, x_5, x_6, x_224);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
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
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_223);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_220);
if (lean_is_scalar(x_228)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_228;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_227);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_223);
x_232 = lean_ctor_get(x_225, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_225, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_234 = x_225;
} else {
 lean_dec_ref(x_225);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_236 = lean_ctor_get(x_222, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_222, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_238 = x_222;
} else {
 lean_dec_ref(x_222);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_240 = l_Lean_Expr_appFn_x21(x_161);
x_241 = l_Lean_Expr_appArg_x21(x_240);
lean_dec(x_240);
x_242 = l_Lean_Expr_appArg_x21(x_161);
lean_dec(x_161);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_243 = l_Lean_Meta_mkEq(x_241, x_242, x_3, x_4, x_5, x_6, x_162);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_box(0);
x_247 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__14;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_248 = l_Lean_Meta_mkEq(x_244, x_247, x_3, x_4, x_5, x_6, x_245);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = l_Lean_Meta_mkEqFalse(x_1, x_3, x_4, x_5, x_6, x_250);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_254 = x_251;
} else {
 lean_dec_ref(x_251);
 x_254 = lean_box(0);
}
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_249);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_246);
if (lean_is_scalar(x_254)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_254;
}
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_253);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_249);
x_258 = lean_ctor_get(x_251, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_251, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_260 = x_251;
} else {
 lean_dec_ref(x_251);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_262 = lean_ctor_get(x_248, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_248, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_264 = x_248;
} else {
 lean_dec_ref(x_248);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_266 = lean_ctor_get(x_243, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_243, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_268 = x_243;
} else {
 lean_dec_ref(x_243);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_270 = l_Lean_Expr_appFn_x21(x_161);
x_271 = l_Lean_Expr_appArg_x21(x_270);
lean_dec(x_270);
x_272 = l_Lean_Expr_appArg_x21(x_161);
lean_dec(x_161);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_273 = l_Lean_Meta_mkEq(x_271, x_272, x_3, x_4, x_5, x_6, x_162);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = l_Lean_Meta_mkPropExt(x_1, x_3, x_4, x_5, x_6, x_275);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_279 = x_276;
} else {
 lean_dec_ref(x_276);
 x_279 = lean_box(0);
}
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_274);
x_281 = lean_box(0);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
if (lean_is_scalar(x_279)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_279;
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_278);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_274);
x_284 = lean_ctor_get(x_276, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_276, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_286 = x_276;
} else {
 lean_dec_ref(x_276);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_285);
return x_287;
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_288 = lean_ctor_get(x_273, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_273, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_290 = x_273;
} else {
 lean_dec_ref(x_273);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_289);
return x_291;
}
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_1);
lean_ctor_set(x_292, 1, x_161);
x_293 = lean_box(0);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_162);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___lambda__1), 8, 1);
lean_closure_set(x_296, 0, x_1);
x_297 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_161, x_296, x_3, x_4, x_5, x_6, x_162);
return x_297;
}
}
}
else
{
uint8_t x_298; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_298 = !lean_is_exclusive(x_8);
if (x_298 == 0)
{
return x_8;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_8, 0);
x_300 = lean_ctor_get(x_8, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_8);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
}
lean_object* l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'simp', proposition expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instToFormatSimpLemma___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_isProp(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_indentExpr(x_1);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_15, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_7, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_2, x_8, x_9, x_10);
return x_11;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_2);
lean_ctor_set(x_14, 3, x_3);
lean_ctor_set(x_14, 4, x_5);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_4);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected kind of 'simp' theorem");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 4);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_19 = 2;
lean_ctor_set_uint8(x_13, 5, x_19);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_17);
x_21 = 1;
x_22 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_1, x_21, x_2, x_22, x_20, x_9, x_10, x_11, x_12);
lean_dec(x_2);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_30 = l_Lean_Meta_whnfR(x_28, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__2;
x_34 = lean_unsigned_to_nat(3u);
x_35 = l_Lean_Expr_isAppOfArity(x_31, x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_free_object(x_25);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = l_Lean_indentExpr(x_31);
x_37 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__4;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__3;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___spec__1(x_40, x_8, x_9, x_10, x_11, x_32);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = l_Lean_Expr_appFn_x21(x_31);
x_47 = l_Lean_Expr_appArg_x21(x_46);
lean_dec(x_46);
x_48 = l_Lean_Expr_appArg_x21(x_31);
lean_dec(x_31);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_47);
x_49 = l_Lean_Meta_DiscrTree_mkPath(x_47, x_8, x_9, x_10, x_11, x_32);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_52 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm(x_47, x_48, x_8, x_9, x_10, x_11, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_ctor_set(x_25, 1, x_53);
lean_ctor_set(x_25, 0, x_50);
x_55 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__1(x_3, x_4, x_5, x_6, x_7, x_25, x_8, x_9, x_10, x_11, x_54);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_25);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_50);
lean_free_object(x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_52);
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
lean_dec(x_48);
lean_dec(x_47);
lean_free_object(x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_49);
if (x_60 == 0)
{
return x_49;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_49, 0);
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_49);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_free_object(x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_30);
if (x_64 == 0)
{
return x_30;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_30, 0);
x_66 = lean_ctor_get(x_30, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_30);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_25, 1);
lean_inc(x_68);
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_69 = l_Lean_Meta_whnfR(x_68, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__2;
x_73 = lean_unsigned_to_nat(3u);
x_74 = l_Lean_Expr_isAppOfArity(x_70, x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_75 = l_Lean_indentExpr(x_70);
x_76 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__4;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__3;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___spec__1(x_79, x_8, x_9, x_10, x_11, x_71);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
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
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = l_Lean_Expr_appFn_x21(x_70);
x_86 = l_Lean_Expr_appArg_x21(x_85);
lean_dec(x_85);
x_87 = l_Lean_Expr_appArg_x21(x_70);
lean_dec(x_70);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_86);
x_88 = l_Lean_Meta_DiscrTree_mkPath(x_86, x_8, x_9, x_10, x_11, x_71);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_91 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm(x_86, x_87, x_8, x_9, x_10, x_11, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_92);
x_95 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__1(x_3, x_4, x_5, x_6, x_7, x_94, x_8, x_9, x_10, x_11, x_93);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_94);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_89);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_98 = x_91;
} else {
 lean_dec_ref(x_91);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = lean_ctor_get(x_88, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_88, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_102 = x_88;
} else {
 lean_dec_ref(x_88);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_104 = lean_ctor_get(x_69, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_69, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_106 = x_69;
} else {
 lean_dec_ref(x_69);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_108 = !lean_is_exclusive(x_23);
if (x_108 == 0)
{
return x_23;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_23, 0);
x_110 = lean_ctor_get(x_23, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_23);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_126; lean_object* x_127; 
x_112 = lean_ctor_get_uint8(x_13, 0);
x_113 = lean_ctor_get_uint8(x_13, 1);
x_114 = lean_ctor_get_uint8(x_13, 2);
x_115 = lean_ctor_get_uint8(x_13, 3);
x_116 = lean_ctor_get_uint8(x_13, 4);
x_117 = lean_ctor_get_uint8(x_13, 6);
x_118 = lean_ctor_get_uint8(x_13, 7);
x_119 = lean_ctor_get_uint8(x_13, 8);
x_120 = lean_ctor_get_uint8(x_13, 9);
x_121 = lean_ctor_get_uint8(x_13, 10);
lean_dec(x_13);
x_122 = 2;
x_123 = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(x_123, 0, x_112);
lean_ctor_set_uint8(x_123, 1, x_113);
lean_ctor_set_uint8(x_123, 2, x_114);
lean_ctor_set_uint8(x_123, 3, x_115);
lean_ctor_set_uint8(x_123, 4, x_116);
lean_ctor_set_uint8(x_123, 5, x_122);
lean_ctor_set_uint8(x_123, 6, x_117);
lean_ctor_set_uint8(x_123, 7, x_118);
lean_ctor_set_uint8(x_123, 8, x_119);
lean_ctor_set_uint8(x_123, 9, x_120);
lean_ctor_set_uint8(x_123, 10, x_121);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_14);
lean_ctor_set(x_124, 2, x_15);
lean_ctor_set(x_124, 3, x_16);
lean_ctor_set(x_124, 4, x_17);
x_125 = 1;
x_126 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_127 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_1, x_125, x_2, x_126, x_124, x_9, x_10, x_11, x_12);
lean_dec(x_2);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_133 = l_Lean_Meta_whnfR(x_131, x_8, x_9, x_10, x_11, x_130);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__2;
x_137 = lean_unsigned_to_nat(3u);
x_138 = l_Lean_Expr_isAppOfArity(x_134, x_136, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_132);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_139 = l_Lean_indentExpr(x_134);
x_140 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__4;
x_141 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__3;
x_143 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___spec__1(x_143, x_8, x_9, x_10, x_11, x_135);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = l_Lean_Expr_appFn_x21(x_134);
x_150 = l_Lean_Expr_appArg_x21(x_149);
lean_dec(x_149);
x_151 = l_Lean_Expr_appArg_x21(x_134);
lean_dec(x_134);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_150);
x_152 = l_Lean_Meta_DiscrTree_mkPath(x_150, x_8, x_9, x_10, x_11, x_135);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_155 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_isPerm(x_150, x_151, x_8, x_9, x_10, x_11, x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
if (lean_is_scalar(x_132)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_132;
}
lean_ctor_set(x_158, 0, x_153);
lean_ctor_set(x_158, 1, x_156);
x_159 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__1(x_3, x_4, x_5, x_6, x_7, x_158, x_8, x_9, x_10, x_11, x_157);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_158);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_153);
lean_dec(x_132);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_160 = lean_ctor_get(x_155, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_155, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_162 = x_155;
} else {
 lean_dec_ref(x_155);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_132);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_164 = lean_ctor_get(x_152, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_152, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_166 = x_152;
} else {
 lean_dec_ref(x_152);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_132);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_168 = lean_ctor_get(x_133, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_133, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_170 = x_133;
} else {
 lean_dec_ref(x_133);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_172 = lean_ctor_get(x_127, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_127, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_174 = x_127;
} else {
 lean_dec_ref(x_127);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = lean_infer_type(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Meta_instantiateMVars(x_13, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_box(x_4);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___boxed), 12, 7);
lean_closure_set(x_20, 0, x_16);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_5);
lean_closure_set(x_20, 5, x_19);
lean_closure_set(x_20, 6, x_6);
x_21 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___spec__1___rarg(x_20, x_7, x_8, x_9, x_10, x_17);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__1(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_4);
x_18 = l_Lean_Meta_mkAuxLemma(x_4, x_17, x_16, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_5);
lean_inc(x_19);
x_21 = l_Lean_mkConst(x_19, x_5);
x_22 = lean_box(0);
x_23 = l_Lean_mkConst(x_19, x_22);
lean_inc(x_1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = l_Lean_Meta_instInhabitedSimpLemma___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_26 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore(x_21, x_25, x_23, x_2, x_3, x_24, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_array_push(x_7, x_27);
x_6 = x_15;
x_7 = x_29;
x_12 = x_28;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
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
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_ConstantInfo_levelParams(x_10);
lean_dec(x_10);
lean_inc(x_12);
x_13 = l_List_map___at_Lean_mkConstWithLevelParams___spec__1(x_12);
lean_inc(x_13);
lean_inc(x_1);
x_14 = l_Lean_mkConst(x_1, x_13);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 2;
lean_ctor_set_uint8(x_16, 5, x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_19 = lean_infer_type(x_14, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_20);
x_22 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp(x_20, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_20);
x_25 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_20, x_24, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
lean_inc(x_1);
x_30 = l_Lean_mkConst(x_1, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_1);
x_32 = l_Lean_Meta_instInhabitedSimpLemma___closed__1;
x_33 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore(x_14, x_32, x_30, x_2, x_3, x_31, x_4, x_5, x_6, x_7, x_28);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___closed__1;
x_37 = lean_array_push(x_36, x_35);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___closed__1;
x_41 = lean_array_push(x_40, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_33);
if (x_43 == 0)
{
return x_33;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_33, 0);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_33);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
lean_dec(x_25);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_48 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess(x_14, x_20, x_4, x_5, x_6, x_7, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Meta_instInhabitedSimpLemma___closed__1;
x_52 = l_List_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___spec__1(x_1, x_2, x_3, x_12, x_13, x_49, x_51, x_4, x_5, x_6, x_7, x_50);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_48);
if (x_61 == 0)
{
return x_48;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_48, 0);
x_63 = lean_ctor_get(x_48, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_48);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_25);
if (x_65 == 0)
{
return x_25;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_25, 0);
x_67 = lean_ctor_get(x_25, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_25);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_22);
if (x_69 == 0)
{
return x_22;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_22, 0);
x_71 = lean_ctor_get(x_22, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_22);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_4);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_19);
if (x_73 == 0)
{
return x_19;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_19, 0);
x_75 = lean_ctor_get(x_19, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_19);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_77 = lean_ctor_get_uint8(x_16, 0);
x_78 = lean_ctor_get_uint8(x_16, 1);
x_79 = lean_ctor_get_uint8(x_16, 2);
x_80 = lean_ctor_get_uint8(x_16, 3);
x_81 = lean_ctor_get_uint8(x_16, 4);
x_82 = lean_ctor_get_uint8(x_16, 6);
x_83 = lean_ctor_get_uint8(x_16, 7);
x_84 = lean_ctor_get_uint8(x_16, 8);
x_85 = lean_ctor_get_uint8(x_16, 9);
x_86 = lean_ctor_get_uint8(x_16, 10);
lean_dec(x_16);
x_87 = 2;
x_88 = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(x_88, 0, x_77);
lean_ctor_set_uint8(x_88, 1, x_78);
lean_ctor_set_uint8(x_88, 2, x_79);
lean_ctor_set_uint8(x_88, 3, x_80);
lean_ctor_set_uint8(x_88, 4, x_81);
lean_ctor_set_uint8(x_88, 5, x_87);
lean_ctor_set_uint8(x_88, 6, x_82);
lean_ctor_set_uint8(x_88, 7, x_83);
lean_ctor_set_uint8(x_88, 8, x_84);
lean_ctor_set_uint8(x_88, 9, x_85);
lean_ctor_set_uint8(x_88, 10, x_86);
lean_ctor_set(x_4, 0, x_88);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_89 = lean_infer_type(x_14, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_90);
x_92 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp(x_90, x_4, x_5, x_6, x_7, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_90);
x_95 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_90, x_94, x_4, x_5, x_6, x_7, x_93);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_90);
lean_dec(x_13);
lean_dec(x_12);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_99 = lean_box(0);
lean_inc(x_1);
x_100 = l_Lean_mkConst(x_1, x_99);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_1);
x_102 = l_Lean_Meta_instInhabitedSimpLemma___closed__1;
x_103 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore(x_14, x_102, x_100, x_2, x_3, x_101, x_4, x_5, x_6, x_7, x_98);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
x_107 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___closed__1;
x_108 = lean_array_push(x_107, x_104);
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_106;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_105);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_103, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_103, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_112 = x_103;
} else {
 lean_dec_ref(x_103);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_95, 1);
lean_inc(x_114);
lean_dec(x_95);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_115 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess(x_14, x_90, x_4, x_5, x_6, x_7, x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lean_Meta_instInhabitedSimpLemma___closed__1;
x_119 = l_List_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___spec__1(x_1, x_2, x_3, x_12, x_13, x_116, x_118, x_4, x_5, x_6, x_7, x_117);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_119, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_126 = x_119;
} else {
 lean_dec_ref(x_119);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_4);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_128 = lean_ctor_get(x_115, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_115, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_130 = x_115;
} else {
 lean_dec_ref(x_115);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_90);
lean_dec(x_4);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_132 = lean_ctor_get(x_95, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_95, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_134 = x_95;
} else {
 lean_dec_ref(x_95);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_90);
lean_dec(x_4);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_136 = lean_ctor_get(x_92, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_92, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_138 = x_92;
} else {
 lean_dec_ref(x_92);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_4);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_140 = lean_ctor_get(x_89, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_89, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_142 = x_89;
} else {
 lean_dec_ref(x_89);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_144 = lean_ctor_get(x_4, 0);
x_145 = lean_ctor_get(x_4, 1);
x_146 = lean_ctor_get(x_4, 2);
x_147 = lean_ctor_get(x_4, 3);
x_148 = lean_ctor_get(x_4, 4);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_4);
x_149 = lean_ctor_get_uint8(x_144, 0);
x_150 = lean_ctor_get_uint8(x_144, 1);
x_151 = lean_ctor_get_uint8(x_144, 2);
x_152 = lean_ctor_get_uint8(x_144, 3);
x_153 = lean_ctor_get_uint8(x_144, 4);
x_154 = lean_ctor_get_uint8(x_144, 6);
x_155 = lean_ctor_get_uint8(x_144, 7);
x_156 = lean_ctor_get_uint8(x_144, 8);
x_157 = lean_ctor_get_uint8(x_144, 9);
x_158 = lean_ctor_get_uint8(x_144, 10);
if (lean_is_exclusive(x_144)) {
 x_159 = x_144;
} else {
 lean_dec_ref(x_144);
 x_159 = lean_box(0);
}
x_160 = 2;
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(0, 0, 11);
} else {
 x_161 = x_159;
}
lean_ctor_set_uint8(x_161, 0, x_149);
lean_ctor_set_uint8(x_161, 1, x_150);
lean_ctor_set_uint8(x_161, 2, x_151);
lean_ctor_set_uint8(x_161, 3, x_152);
lean_ctor_set_uint8(x_161, 4, x_153);
lean_ctor_set_uint8(x_161, 5, x_160);
lean_ctor_set_uint8(x_161, 6, x_154);
lean_ctor_set_uint8(x_161, 7, x_155);
lean_ctor_set_uint8(x_161, 8, x_156);
lean_ctor_set_uint8(x_161, 9, x_157);
lean_ctor_set_uint8(x_161, 10, x_158);
x_162 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_145);
lean_ctor_set(x_162, 2, x_146);
lean_ctor_set(x_162, 3, x_147);
lean_ctor_set(x_162, 4, x_148);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_162);
lean_inc(x_14);
x_163 = lean_infer_type(x_14, x_162, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_162);
lean_inc(x_164);
x_166 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp(x_164, x_162, x_5, x_6, x_7, x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_162);
lean_inc(x_164);
x_169 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_164, x_168, x_162, x_5, x_6, x_7, x_167);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_unbox(x_170);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_164);
lean_dec(x_13);
lean_dec(x_12);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = lean_box(0);
lean_inc(x_1);
x_174 = l_Lean_mkConst(x_1, x_173);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_1);
x_176 = l_Lean_Meta_instInhabitedSimpLemma___closed__1;
x_177 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore(x_14, x_176, x_174, x_2, x_3, x_175, x_162, x_5, x_6, x_7, x_172);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_180 = x_177;
} else {
 lean_dec_ref(x_177);
 x_180 = lean_box(0);
}
x_181 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___closed__1;
x_182 = lean_array_push(x_181, x_178);
if (lean_is_scalar(x_180)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_180;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_179);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_177, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_177, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_186 = x_177;
} else {
 lean_dec_ref(x_177);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_169, 1);
lean_inc(x_188);
lean_dec(x_169);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_162);
x_189 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess(x_14, x_164, x_162, x_5, x_6, x_7, x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = l_Lean_Meta_instInhabitedSimpLemma___closed__1;
x_193 = l_List_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___spec__1(x_1, x_2, x_3, x_12, x_13, x_190, x_192, x_162, x_5, x_6, x_7, x_191);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_196 = x_193;
} else {
 lean_dec_ref(x_193);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_193, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_193, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_200 = x_193;
} else {
 lean_dec_ref(x_193);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_162);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_202 = lean_ctor_get(x_189, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_189, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_204 = x_189;
} else {
 lean_dec_ref(x_189);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_164);
lean_dec(x_162);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_206 = lean_ctor_get(x_169, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_169, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_208 = x_169;
} else {
 lean_dec_ref(x_169);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_164);
lean_dec(x_162);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_210 = lean_ctor_get(x_166, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_166, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_212 = x_166;
} else {
 lean_dec_ref(x_166);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_162);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_214 = lean_ctor_get(x_163, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_163, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_216 = x_163;
} else {
 lean_dec_ref(x_163);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
}
else
{
uint8_t x_218; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_218 = !lean_is_exclusive(x_9);
if (x_218 == 0)
{
return x_9;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_9, 0);
x_220 = lean_ctor_get(x_9, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_9);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_List_forIn_loop___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpLemma___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (x_3) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_6);
x_9 = lean_st_ref_take(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_13, x_2);
lean_ctor_set(x_10, 0, x_14);
x_15 = lean_st_ref_set(x_7, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_26 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_22, x_2);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
x_28 = lean_st_ref_set(x_7, x_27, x_11);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_6);
x_33 = lean_st_ref_take(x_7, x_8);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_37, x_2);
lean_ctor_set(x_34, 0, x_38);
x_39 = lean_st_ref_set(x_7, x_34, x_35);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 1);
x_48 = lean_ctor_get(x_34, 2);
x_49 = lean_ctor_get(x_34, 3);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_34);
x_50 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_46, x_2);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set(x_51, 3, x_49);
x_52 = lean_st_ref_set(x_7, x_51, x_35);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
default: 
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_6, 4);
lean_inc(x_57);
lean_dec(x_6);
x_58 = lean_st_ref_take(x_7, x_8);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_59, 0);
x_63 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_62, x_57, x_2);
lean_ctor_set(x_59, 0, x_63);
x_64 = lean_st_ref_set(x_7, x_59, x_60);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
x_67 = lean_box(0);
lean_ctor_set(x_64, 0, x_67);
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_71 = lean_ctor_get(x_59, 0);
x_72 = lean_ctor_get(x_59, 1);
x_73 = lean_ctor_get(x_59, 2);
x_74 = lean_ctor_get(x_59, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_59);
x_75 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_71, x_57, x_2);
x_76 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
lean_ctor_set(x_76, 2, x_73);
lean_ctor_set(x_76, 3, x_74);
x_77 = lean_st_ref_set(x_7, x_76, x_60);
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
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_addSimpLemma___spec__2(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_4 < x_3;
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
lean_dec(x_5);
x_13 = lean_array_uget(x_2, x_4);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_Meta_simpExtension;
lean_inc(x_8);
x_16 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpLemma___spec__1(x_15, x_14, x_1, x_6, x_7, x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 1;
x_19 = x_4 + x_18;
x_20 = lean_box(0);
x_4 = x_19;
x_5 = x_20;
x_10 = x_17;
goto _start;
}
}
}
lean_object* l_Lean_Meta_addSimpLemma(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_array_get_size(x_11);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = lean_box(0);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_addSimpLemma___spec__2(x_3, x_11, x_14, x_15, x_16, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpLemma___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpLemma___spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_addSimpLemma___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_addSimpLemma___spec__2(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_14;
}
}
lean_object* l_Lean_Meta_addSimpLemma___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_addSimpLemma(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ScopedEnvExtension_instInhabitedStateStack(lean_box(0), lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__1;
x_2 = l_Lean_instInhabitedPersistentEnvExtensionState___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Environment");
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.EnvExtensionInterfaceUnsafe.getState");
return x_1;
}
}
static lean_object* _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__3;
x_2 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__4;
x_3 = lean_unsigned_to_nat(220u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l___private_Lean_Environment_0__Lean_EnvExtensionInterfaceUnsafe_invalidExtMsg;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__2;
x_8 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__5;
x_9 = lean_panic_fn(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget(x_4, x_3);
x_11 = x_10;
return x_11;
}
}
}
lean_object* l_Lean_PersistentEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3(x_3, x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.ScopedEnvExtension");
return x_1;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.ScopedEnvExtension.getState");
return x_1;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__1;
x_2 = l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__2;
x_3 = lean_unsigned_to_nat(157u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_PersistentEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__2(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Meta_instInhabitedSimpLemmas;
x_7 = l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__4;
x_8 = lean_panic_fn(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
return x_10;
}
}
}
lean_object* l_Lean_Meta_SimpLemmas_eraseCore___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 4);
x_10 = l_Lean_Name_instBEqName;
x_11 = l_Lean_instHashableName;
lean_inc(x_2);
x_12 = l_Std_PersistentHashMap_erase___rarg(x_10, x_11, x_7, x_2);
lean_inc(x_2);
x_13 = l_Std_PersistentHashMap_erase___rarg(x_10, x_11, x_8, x_2);
x_14 = lean_box(0);
x_15 = l_Std_PersistentHashMap_insert___rarg(x_10, x_11, x_9, x_2, x_14);
lean_ctor_set(x_1, 4, x_15);
lean_ctor_set(x_1, 3, x_13);
lean_ctor_set(x_1, 2, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_1, 2);
x_20 = lean_ctor_get(x_1, 3);
x_21 = lean_ctor_get(x_1, 4);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_22 = l_Lean_Name_instBEqName;
x_23 = l_Lean_instHashableName;
lean_inc(x_2);
x_24 = l_Std_PersistentHashMap_erase___rarg(x_22, x_23, x_19, x_2);
lean_inc(x_2);
x_25 = l_Std_PersistentHashMap_erase___rarg(x_22, x_23, x_20, x_2);
x_26 = lean_box(0);
x_27 = l_Std_PersistentHashMap_insert___rarg(x_22, x_23, x_21, x_2, x_26);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_25);
lean_ctor_set(x_28, 4, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_5);
return x_29;
}
}
}
lean_object* l_Lean_Meta_SimpLemmas_erase___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = l_Lean_Meta_SimpLemmas_eraseCore___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__5(x_1, x_2, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_Meta_SimpLemmas_erase___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Lean_Meta_SimpLemmas_isLemma(x_1, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_SimpLemmas_isDeclToUnfold(x_1, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = l_Lean_Meta_SimpLemmas_erase___rarg___closed__2;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Meta_SimpLemmas_erase___rarg___closed__4;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__5(x_12, x_3, x_4, x_5);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Meta_SimpLemmas_eraseCore___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__5(x_1, x_2, x_3, x_4, x_5);
return x_18;
}
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Meta_SimpLemmas_eraseCore___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__5(x_1, x_2, x_3, x_4, x_5);
return x_19;
}
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, 2, x_1);
lean_ctor_set_uint8(x_4, 3, x_1);
lean_ctor_set_uint8(x_4, 4, x_1);
lean_ctor_set_uint8(x_4, 5, x_2);
lean_ctor_set_uint8(x_4, 6, x_3);
lean_ctor_set_uint8(x_4, 7, x_1);
lean_ctor_set_uint8(x_4, 8, x_3);
lean_ctor_set_uint8(x_4, 9, x_3);
lean_ctor_set_uint8(x_4, 10, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__3;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__2;
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__3;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__1;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__5;
x_4 = l_Lean_Meta_instInhabitedSimpLemma___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__3;
x_3 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__8;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__10;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__11;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__14;
x_5 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__7;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__15;
x_3 = l_Lean_NameSet_empty;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'simp', it is not a proposition nor a definition (to unfold)");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__20;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__21;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__22;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__23;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simpPost");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__24;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__25;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_25; lean_object* x_26; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__16;
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_25 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__6;
lean_inc(x_1);
x_26 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_25, x_11, x_4, x_5, x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_ConstantInfo_type(x_27);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_11);
x_30 = l_Lean_Meta_isProp(x_29, x_25, x_11, x_4, x_5, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l_Lean_ConstantInfo_hasValue(x_27);
lean_dec(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_1);
x_35 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__18;
x_36 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_35, x_25, x_11, x_4, x_5, x_33);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_11);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_1);
x_42 = l_Lean_Meta_simpExtension;
x_43 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addSimpLemma___spec__1(x_42, x_41, x_3, x_25, x_11, x_4, x_5, x_33);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_13 = x_44;
x_14 = x_45;
goto block_24;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_27);
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_dec(x_30);
x_47 = lean_unsigned_to_nat(1u);
x_48 = l_Lean_Syntax_getArg(x_2, x_47);
x_49 = l_Lean_Syntax_isNone(x_48);
x_50 = lean_unsigned_to_nat(2u);
x_51 = l_Lean_Syntax_getArg(x_2, x_50);
if (x_49 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Lean_Syntax_getArg(x_48, x_52);
lean_dec(x_48);
x_54 = l_Lean_Syntax_getKind(x_53);
x_55 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__26;
x_56 = lean_name_eq(x_54, x_55);
lean_dec(x_54);
lean_inc(x_5);
lean_inc(x_4);
x_57 = l_Lean_getAttrParamOptPrio(x_51, x_4, x_5, x_46);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_5);
lean_inc(x_11);
x_60 = l_Lean_Meta_addSimpLemma(x_1, x_56, x_3, x_58, x_25, x_11, x_4, x_5, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_13 = x_61;
x_14 = x_62;
goto block_24;
}
else
{
uint8_t x_63; 
lean_dec(x_11);
lean_dec(x_5);
x_63 = !lean_is_exclusive(x_60);
if (x_63 == 0)
{
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_60);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_57);
if (x_67 == 0)
{
return x_57;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_57, 0);
x_69 = lean_ctor_get(x_57, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_57);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; 
lean_dec(x_48);
lean_inc(x_5);
lean_inc(x_4);
x_71 = l_Lean_getAttrParamOptPrio(x_51, x_4, x_5, x_46);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = 1;
lean_inc(x_5);
lean_inc(x_11);
x_75 = l_Lean_Meta_addSimpLemma(x_1, x_74, x_3, x_72, x_25, x_11, x_4, x_5, x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_13 = x_76;
x_14 = x_77;
goto block_24;
}
else
{
uint8_t x_78; 
lean_dec(x_11);
lean_dec(x_5);
x_78 = !lean_is_exclusive(x_75);
if (x_78 == 0)
{
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_75, 0);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_75);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_71);
if (x_82 == 0)
{
return x_71;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_71, 0);
x_84 = lean_ctor_get(x_71, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_71);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_30);
if (x_86 == 0)
{
return x_30;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_30, 0);
x_88 = lean_ctor_get(x_30, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_30);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_26);
if (x_90 == 0)
{
return x_26;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_26, 0);
x_92 = lean_ctor_get(x_26, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_26);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
block_24:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_13);
x_15 = lean_st_ref_get(x_5, x_14);
lean_dec(x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_11, x_16);
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Meta_simpExtension;
x_10 = l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_Meta_SimpLemmas_erase___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__4(x_10, x_1, x_2, x_3, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_3, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_simpExtension___lambda__4___boxed), 2, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = l_Lean_ScopedEnvExtension_modifyState___rarg(x_9, x_18, x_19);
lean_ctor_set(x_15, 0, x_20);
x_21 = lean_st_ref_set(x_3, x_15, x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
x_30 = lean_ctor_get(x_15, 2);
x_31 = lean_ctor_get(x_15, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_32 = lean_alloc_closure((void*)(l_Lean_Meta_simpExtension___lambda__4___boxed), 2, 1);
lean_closure_set(x_32, 0, x_12);
x_33 = l_Lean_ScopedEnvExtension_modifyState___rarg(x_9, x_28, x_32);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
lean_ctor_set(x_34, 2, x_30);
lean_ctor_set(x_34, 3, x_31);
x_35 = lean_st_ref_set(x_3, x_34, x_16);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
return x_11;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simp");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simplification theorem");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__3;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__4;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__5;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__7;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_PersistentEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_SimpLemmas_eraseCore___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_SimpLemmas_eraseCore___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Meta_SimpLemmas_erase___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_SimpLemmas_erase___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Meta_getSimpLemmas___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Meta_simpExtension;
x_8 = l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1(x_7, x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_simpExtension;
x_13 = l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1(x_12, x_11);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
}
lean_object* l_Lean_Meta_getSimpLemmas(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpLemmas___rarg___boxed), 2, 0);
return x_4;
}
}
lean_object* l_Lean_Meta_getSimpLemmas___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_getSimpLemmas___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_getSimpLemmas___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getSimpLemmas(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpLemmas_addConst___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Meta_addSimpLemmaEntry(x_4, x_6);
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
lean_object* l_Lean_Meta_SimpLemmas_addConst(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpLemmas_addConst___spec__1(x_12, x_17, x_18, x_1);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_array_get_size(x_20);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_22, x_22);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_30 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpLemmas_addConst___spec__1(x_20, x_28, x_29, x_1);
lean_dec(x_20);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_21);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_10);
if (x_32 == 0)
{
return x_10;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpLemmas_addConst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpLemmas_addConst___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_SimpLemmas_addConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_SimpLemmas_addConst(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemma_getValue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemma_getValue___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Expr.updateConst!");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemma_getValue___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constant expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemma_getValue___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_SimpLemma_getValue___closed__1;
x_2 = l_Lean_Meta_SimpLemma_getValue___closed__2;
x_3 = lean_unsigned_to_nat(876u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Meta_SimpLemma_getValue___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_SimpLemma_getValue___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_SimpLemma_getValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = l_Lean_Expr_isConst(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
lean_inc(x_9);
x_12 = x_9;
x_13 = lean_box_usize(x_11);
x_14 = l_Lean_Meta_SimpLemma_getValue___boxed__const__1;
x_15 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1___boxed), 8, 3);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_12);
x_16 = x_15;
x_17 = lean_apply_5(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_9, x_19, x_7);
lean_dec(x_19);
lean_dec(x_9);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_9, x_21, x_7);
lean_dec(x_21);
lean_dec(x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_7);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = l_Array_isEmpty___rarg(x_29);
if (x_30 == 0)
{
lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_array_get_size(x_29);
x_32 = lean_usize_of_nat(x_31);
lean_dec(x_31);
lean_inc(x_29);
x_33 = x_29;
x_34 = lean_box_usize(x_32);
x_35 = l_Lean_Meta_SimpLemma_getValue___boxed__const__1;
x_36 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_openAbstractMVarsResult___spec__1___boxed), 8, 3);
lean_closure_set(x_36, 0, x_34);
lean_closure_set(x_36, 1, x_35);
lean_closure_set(x_36, 2, x_33);
x_37 = x_36;
x_38 = lean_apply_5(x_37, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_29, x_40, x_7);
lean_dec(x_40);
lean_dec(x_29);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = l_Lean_Expr_instantiateLevelParamsCore_visit___at_Lean_Expr_instantiateLevelParamsArray___spec__1(x_29, x_42, x_7);
lean_dec(x_42);
lean_dec(x_29);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_29);
lean_dec(x_7);
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
return x_38;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_38, 0);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_38);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_29);
x_50 = l_Lean_Expr_constName_x21(x_7);
x_51 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_50, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
x_55 = l_Lean_ConstantInfo_levelParams(x_53);
lean_dec(x_53);
x_56 = l_List_isEmpty___rarg(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_free_object(x_51);
x_57 = l_List_mapM___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(x_55, x_2, x_3, x_4, x_5, x_54);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_7) == 4)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_7);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 0);
x_61 = lean_expr_update_const(x_7, x_60);
lean_ctor_set(x_57, 0, x_61);
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_7, 0);
x_64 = lean_ctor_get(x_7, 1);
x_65 = lean_ctor_get_uint64(x_7, sizeof(void*)*2);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_7);
x_66 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set_uint64(x_66, sizeof(void*)*2, x_65);
x_67 = lean_expr_update_const(x_66, x_62);
lean_ctor_set(x_57, 0, x_67);
return x_57;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_57, 0);
x_69 = lean_ctor_get(x_57, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_57);
x_70 = lean_ctor_get(x_7, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_7, 1);
lean_inc(x_71);
x_72 = lean_ctor_get_uint64(x_7, sizeof(void*)*2);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_73 = x_7;
} else {
 lean_dec_ref(x_7);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(4, 2, 8);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_71);
lean_ctor_set_uint64(x_74, sizeof(void*)*2, x_72);
x_75 = lean_expr_update_const(x_74, x_68);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_7);
x_77 = !lean_is_exclusive(x_57);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_57, 0);
lean_dec(x_78);
x_79 = l_Lean_instInhabitedExpr;
x_80 = l_Lean_Meta_SimpLemma_getValue___closed__4;
x_81 = lean_panic_fn(x_79, x_80);
lean_ctor_set(x_57, 0, x_81);
return x_57;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_57, 1);
lean_inc(x_82);
lean_dec(x_57);
x_83 = l_Lean_instInhabitedExpr;
x_84 = l_Lean_Meta_SimpLemma_getValue___closed__4;
x_85 = lean_panic_fn(x_83, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_82);
return x_86;
}
}
}
else
{
lean_dec(x_55);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_51, 0, x_7);
return x_51;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_51, 0);
x_88 = lean_ctor_get(x_51, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_51);
x_89 = l_Lean_ConstantInfo_levelParams(x_87);
lean_dec(x_87);
x_90 = l_List_isEmpty___rarg(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = l_List_mapM___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(x_89, x_2, x_3, x_4, x_5, x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint64_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_7, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_7, 1);
lean_inc(x_96);
x_97 = lean_ctor_get_uint64(x_7, sizeof(void*)*2);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_98 = x_7;
} else {
 lean_dec_ref(x_7);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(4, 2, 8);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_96);
lean_ctor_set_uint64(x_99, sizeof(void*)*2, x_97);
x_100 = lean_expr_update_const(x_99, x_92);
if (lean_is_scalar(x_94)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_94;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_93);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_7);
x_102 = lean_ctor_get(x_91, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_103 = x_91;
} else {
 lean_dec_ref(x_91);
 x_103 = lean_box(0);
}
x_104 = l_Lean_instInhabitedExpr;
x_105 = l_Lean_Meta_SimpLemma_getValue___closed__4;
x_106 = lean_panic_fn(x_104, x_105);
if (lean_is_scalar(x_103)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_103;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_102);
return x_107;
}
}
else
{
lean_object* x_108; 
lean_dec(x_89);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_7);
lean_ctor_set(x_108, 1, x_88);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_109 = !lean_is_exclusive(x_51);
if (x_109 == 0)
{
return x_51;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_51, 0);
x_111 = lean_ctor_get(x_51, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_51);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocessProof___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = 1;
x_11 = x_2 + x_10;
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = x_12;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_11;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocessProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_inc(x_8);
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess(x_1, x_8, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_List_redLength___rarg(x_14);
x_16 = lean_mk_empty_array_with_capacity(x_15);
lean_dec(x_15);
x_17 = l_List_toArrayAux___rarg(x_14, x_16);
x_18 = lean_array_get_size(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = x_17;
x_22 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocessProof___spec__1(x_19, x_20, x_21);
x_23 = x_22;
lean_ctor_set(x_12, 0, x_23);
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = l_List_redLength___rarg(x_24);
x_27 = lean_mk_empty_array_with_capacity(x_26);
lean_dec(x_26);
x_28 = l_List_toArrayAux___rarg(x_24, x_27);
x_29 = lean_array_get_size(x_28);
x_30 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_31 = 0;
x_32 = x_28;
x_33 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocessProof___spec__1(x_30, x_31, x_32);
x_34 = x_33;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_25);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
return x_12;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_7);
if (x_44 == 0)
{
return x_7;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_7, 0);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_7);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocessProof___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocessProof___spec__1(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_mkSimpLemmas___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_6 < x_5;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = x_7;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_uget(x_7, x_6);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_uset(x_7, x_6, x_17);
x_19 = x_16;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_19);
x_20 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore(x_19, x_1, x_19, x_2, x_3, x_4, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = x_6 + x_23;
x_25 = x_21;
x_26 = lean_array_uset(x_18, x_6, x_25);
x_6 = x_24;
x_7 = x_26;
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
lean_dec(x_4);
lean_dec(x_3);
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
static lean_object* _init_l_Lean_Meta_mkSimpLemmas___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkSimpLemmas(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
x_14 = 2;
lean_ctor_set_uint8(x_12, 5, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocessProof(x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_get_size(x_16);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = x_16;
x_21 = lean_box(x_3);
x_22 = lean_box_usize(x_19);
x_23 = l_Lean_Meta_mkSimpLemmas___boxed__const__1;
x_24 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_mkSimpLemmas___spec__1___boxed), 12, 7);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_21);
lean_closure_set(x_24, 2, x_4);
lean_closure_set(x_24, 3, x_5);
lean_closure_set(x_24, 4, x_22);
lean_closure_set(x_24, 5, x_23);
lean_closure_set(x_24, 6, x_20);
x_25 = x_24;
x_26 = lean_apply_5(x_25, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
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
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
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
lean_dec(x_6);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
else
{
uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_39 = lean_ctor_get_uint8(x_12, 0);
x_40 = lean_ctor_get_uint8(x_12, 1);
x_41 = lean_ctor_get_uint8(x_12, 2);
x_42 = lean_ctor_get_uint8(x_12, 3);
x_43 = lean_ctor_get_uint8(x_12, 4);
x_44 = lean_ctor_get_uint8(x_12, 6);
x_45 = lean_ctor_get_uint8(x_12, 7);
x_46 = lean_ctor_get_uint8(x_12, 8);
x_47 = lean_ctor_get_uint8(x_12, 9);
x_48 = lean_ctor_get_uint8(x_12, 10);
lean_dec(x_12);
x_49 = 2;
x_50 = lean_alloc_ctor(0, 0, 11);
lean_ctor_set_uint8(x_50, 0, x_39);
lean_ctor_set_uint8(x_50, 1, x_40);
lean_ctor_set_uint8(x_50, 2, x_41);
lean_ctor_set_uint8(x_50, 3, x_42);
lean_ctor_set_uint8(x_50, 4, x_43);
lean_ctor_set_uint8(x_50, 5, x_49);
lean_ctor_set_uint8(x_50, 6, x_44);
lean_ctor_set_uint8(x_50, 7, x_45);
lean_ctor_set_uint8(x_50, 8, x_46);
lean_ctor_set_uint8(x_50, 9, x_47);
lean_ctor_set_uint8(x_50, 10, x_48);
lean_ctor_set(x_6, 0, x_50);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_51 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocessProof(x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_array_get_size(x_52);
x_55 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_56 = x_52;
x_57 = lean_box(x_3);
x_58 = lean_box_usize(x_55);
x_59 = l_Lean_Meta_mkSimpLemmas___boxed__const__1;
x_60 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_mkSimpLemmas___spec__1___boxed), 12, 7);
lean_closure_set(x_60, 0, x_1);
lean_closure_set(x_60, 1, x_57);
lean_closure_set(x_60, 2, x_4);
lean_closure_set(x_60, 3, x_5);
lean_closure_set(x_60, 4, x_58);
lean_closure_set(x_60, 5, x_59);
lean_closure_set(x_60, 6, x_56);
x_61 = x_60;
x_62 = lean_apply_5(x_61, x_6, x_7, x_8, x_9, x_53);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_62, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_69 = x_62;
} else {
 lean_dec_ref(x_62);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_6);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_71 = lean_ctor_get(x_51, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_51, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_73 = x_51;
} else {
 lean_dec_ref(x_51);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_75 = lean_ctor_get(x_6, 0);
x_76 = lean_ctor_get(x_6, 1);
x_77 = lean_ctor_get(x_6, 2);
x_78 = lean_ctor_get(x_6, 3);
x_79 = lean_ctor_get(x_6, 4);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_6);
x_80 = lean_ctor_get_uint8(x_75, 0);
x_81 = lean_ctor_get_uint8(x_75, 1);
x_82 = lean_ctor_get_uint8(x_75, 2);
x_83 = lean_ctor_get_uint8(x_75, 3);
x_84 = lean_ctor_get_uint8(x_75, 4);
x_85 = lean_ctor_get_uint8(x_75, 6);
x_86 = lean_ctor_get_uint8(x_75, 7);
x_87 = lean_ctor_get_uint8(x_75, 8);
x_88 = lean_ctor_get_uint8(x_75, 9);
x_89 = lean_ctor_get_uint8(x_75, 10);
if (lean_is_exclusive(x_75)) {
 x_90 = x_75;
} else {
 lean_dec_ref(x_75);
 x_90 = lean_box(0);
}
x_91 = 2;
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 0, 11);
} else {
 x_92 = x_90;
}
lean_ctor_set_uint8(x_92, 0, x_80);
lean_ctor_set_uint8(x_92, 1, x_81);
lean_ctor_set_uint8(x_92, 2, x_82);
lean_ctor_set_uint8(x_92, 3, x_83);
lean_ctor_set_uint8(x_92, 4, x_84);
lean_ctor_set_uint8(x_92, 5, x_91);
lean_ctor_set_uint8(x_92, 6, x_85);
lean_ctor_set_uint8(x_92, 7, x_86);
lean_ctor_set_uint8(x_92, 8, x_87);
lean_ctor_set_uint8(x_92, 9, x_88);
lean_ctor_set_uint8(x_92, 10, x_89);
x_93 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_76);
lean_ctor_set(x_93, 2, x_77);
lean_ctor_set(x_93, 3, x_78);
lean_ctor_set(x_93, 4, x_79);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_93);
x_94 = l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocessProof(x_2, x_93, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; size_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_array_get_size(x_95);
x_98 = lean_usize_of_nat(x_97);
lean_dec(x_97);
x_99 = x_95;
x_100 = lean_box(x_3);
x_101 = lean_box_usize(x_98);
x_102 = l_Lean_Meta_mkSimpLemmas___boxed__const__1;
x_103 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_mkSimpLemmas___spec__1___boxed), 12, 7);
lean_closure_set(x_103, 0, x_1);
lean_closure_set(x_103, 1, x_100);
lean_closure_set(x_103, 2, x_4);
lean_closure_set(x_103, 3, x_5);
lean_closure_set(x_103, 4, x_101);
lean_closure_set(x_103, 5, x_102);
lean_closure_set(x_103, 6, x_99);
x_104 = x_103;
x_105 = lean_apply_5(x_104, x_93, x_7, x_8, x_9, x_96);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_112 = x_105;
} else {
 lean_dec_ref(x_105);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_93);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_114 = lean_ctor_get(x_94, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_94, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_116 = x_94;
} else {
 lean_dec_ref(x_94);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_mkSimpLemmas___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Meta_mkSimpLemmas___spec__1(x_1, x_13, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
lean_object* l_Lean_Meta_mkSimpLemmas___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_mkSimpLemmas(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Meta_SimpLemmas_add_getName_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_SimpLemmas_add_getName_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SimpLemmas_add_getName_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_SimpLemmas_add_getName_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Expr_getAppFn(x_2);
x_9 = l_Lean_Expr_isConst(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isFVar(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Meta_getFVarLocalDecl(x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_LocalDecl_userName(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = l_Lean_LocalDecl_userName(x_18);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
x_27 = l_Lean_Expr_constName_x21(x_8);
lean_dec(x_8);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_3);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_7);
return x_30;
}
}
}
lean_object* l_Lean_Meta_SimpLemmas_add_getName_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SimpLemmas_add_getName_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_SimpLemmas_add(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isConst(x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_7);
x_13 = l_Lean_Meta_SimpLemmas_add_getName_x3f(x_6, x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_mkSimpLemmas(x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_array_get_size(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_19, x_19);
if (x_22 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_25 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpLemmas_addConst___spec__1(x_18, x_23, x_24, x_1);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_array_get_size(x_26);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_lt(x_29, x_28);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_28, x_28);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_SimpLemmas_addConst___spec__1(x_26, x_34, x_35, x_1);
lean_dec(x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_6);
lean_dec(x_2);
x_46 = l_Lean_Expr_constName_x21(x_3);
lean_dec(x_3);
x_47 = l_Lean_Meta_SimpLemmas_addConst(x_1, x_46, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
return x_47;
}
}
}
lean_object* l_Lean_Meta_SimpLemmas_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_SimpLemmas_add(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_ScopedEnvExtension(lean_object*);
lean_object* initialize_Lean_Util_Recognizers(lean_object*);
lean_object* initialize_Lean_Meta_LevelDefEq(lean_object*);
lean_object* initialize_Lean_Meta_DiscrTree(lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_AuxLemma(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpLemmas(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LevelDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_AuxLemma(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_SimpLemma_name_x3f___default = _init_l_Lean_Meta_SimpLemma_name_x3f___default();
lean_mark_persistent(l_Lean_Meta_SimpLemma_name_x3f___default);
l_Lean_Meta_instInhabitedSimpLemma___closed__1 = _init_l_Lean_Meta_instInhabitedSimpLemma___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpLemma___closed__1);
l_Lean_Meta_instInhabitedSimpLemma___closed__2 = _init_l_Lean_Meta_instInhabitedSimpLemma___closed__2();
l_Lean_Meta_instInhabitedSimpLemma___closed__3 = _init_l_Lean_Meta_instInhabitedSimpLemma___closed__3();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpLemma___closed__3);
l_Lean_Meta_instInhabitedSimpLemma___closed__4 = _init_l_Lean_Meta_instInhabitedSimpLemma___closed__4();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpLemma___closed__4);
l_Lean_Meta_instInhabitedSimpLemma = _init_l_Lean_Meta_instInhabitedSimpLemma();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpLemma);
l_Lean_Meta_SimpLemma_getName___closed__1 = _init_l_Lean_Meta_SimpLemma_getName___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpLemma_getName___closed__1);
l_Lean_Meta_SimpLemma_getName___closed__2 = _init_l_Lean_Meta_SimpLemma_getName___closed__2();
lean_mark_persistent(l_Lean_Meta_SimpLemma_getName___closed__2);
l_Lean_Meta_instToFormatSimpLemma___closed__1 = _init_l_Lean_Meta_instToFormatSimpLemma___closed__1();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpLemma___closed__1);
l_Lean_Meta_instToFormatSimpLemma___closed__2 = _init_l_Lean_Meta_instToFormatSimpLemma___closed__2();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpLemma___closed__2);
l_Lean_Meta_instToFormatSimpLemma___closed__3 = _init_l_Lean_Meta_instToFormatSimpLemma___closed__3();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpLemma___closed__3);
l_Lean_Meta_instToFormatSimpLemma___closed__4 = _init_l_Lean_Meta_instToFormatSimpLemma___closed__4();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpLemma___closed__4);
l_Lean_Meta_instToFormatSimpLemma___closed__5 = _init_l_Lean_Meta_instToFormatSimpLemma___closed__5();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpLemma___closed__5);
l_Lean_Meta_instToFormatSimpLemma___closed__6 = _init_l_Lean_Meta_instToFormatSimpLemma___closed__6();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpLemma___closed__6);
l_Lean_Meta_SimpLemmas_pre___default___closed__1 = _init_l_Lean_Meta_SimpLemmas_pre___default___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpLemmas_pre___default___closed__1);
l_Lean_Meta_SimpLemmas_pre___default = _init_l_Lean_Meta_SimpLemmas_pre___default();
lean_mark_persistent(l_Lean_Meta_SimpLemmas_pre___default);
l_Lean_Meta_SimpLemmas_post___default = _init_l_Lean_Meta_SimpLemmas_post___default();
lean_mark_persistent(l_Lean_Meta_SimpLemmas_post___default);
l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__1 = _init_l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__1);
l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__2 = _init_l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__2();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__2);
l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__3 = _init_l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__3();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1___closed__3);
l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1 = _init_l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Meta_SimpLemmas_lemmaNames___default___spec__1);
l_Lean_Meta_SimpLemmas_lemmaNames___default = _init_l_Lean_Meta_SimpLemmas_lemmaNames___default();
lean_mark_persistent(l_Lean_Meta_SimpLemmas_lemmaNames___default);
l_Lean_Meta_SimpLemmas_toUnfold___default = _init_l_Lean_Meta_SimpLemmas_toUnfold___default();
lean_mark_persistent(l_Lean_Meta_SimpLemmas_toUnfold___default);
l_Lean_Meta_SimpLemmas_erased___default = _init_l_Lean_Meta_SimpLemmas_erased___default();
lean_mark_persistent(l_Lean_Meta_SimpLemmas_erased___default);
l_Lean_Meta_instInhabitedSimpLemmas___closed__1 = _init_l_Lean_Meta_instInhabitedSimpLemmas___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpLemmas___closed__1);
l_Lean_Meta_instInhabitedSimpLemmas___closed__2 = _init_l_Lean_Meta_instInhabitedSimpLemmas___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpLemmas___closed__2);
l_Lean_Meta_instInhabitedSimpLemmas = _init_l_Lean_Meta_instInhabitedSimpLemmas();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpLemmas);
l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7___closed__1 = _init_l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7___closed__1();
lean_mark_persistent(l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7___closed__1);
l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7___closed__2 = _init_l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7___closed__2();
lean_mark_persistent(l_Array_back___at_Lean_Meta_addSimpLemmaEntry___spec__7___closed__2);
l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__1 = _init_l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__1);
l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__2 = _init_l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__2);
l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__3 = _init_l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__3();
lean_mark_persistent(l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_addSimpLemmaEntry___spec__8___closed__3);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__1 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__1);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__2 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__2);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__3 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__3);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__4 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__4();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__4);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__5 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__5();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_addSimpLemmaEntry___spec__1___closed__5);
l_Lean_Meta_SimpLemmas_erase___rarg___closed__1 = _init_l_Lean_Meta_SimpLemmas_erase___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpLemmas_erase___rarg___closed__1);
l_Lean_Meta_SimpLemmas_erase___rarg___closed__2 = _init_l_Lean_Meta_SimpLemmas_erase___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_SimpLemmas_erase___rarg___closed__2);
l_Lean_Meta_SimpLemmas_erase___rarg___closed__3 = _init_l_Lean_Meta_SimpLemmas_erase___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_SimpLemmas_erase___rarg___closed__3);
l_Lean_Meta_SimpLemmas_erase___rarg___closed__4 = _init_l_Lean_Meta_SimpLemmas_erase___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_SimpLemmas_erase___rarg___closed__4);
l_Lean_Meta_instInhabitedSimpEntry___closed__1 = _init_l_Lean_Meta_instInhabitedSimpEntry___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpEntry___closed__1);
l_Lean_Meta_instInhabitedSimpEntry = _init_l_Lean_Meta_instInhabitedSimpEntry();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpEntry);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474____closed__6);
l_Lean_Meta_simpExtension___lambda__1___closed__1 = _init_l_Lean_Meta_simpExtension___lambda__1___closed__1();
l_Lean_Meta_simpExtension___lambda__1___closed__2 = _init_l_Lean_Meta_simpExtension___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_simpExtension___lambda__1___closed__2);
l_Lean_Meta_simpExtension___closed__1 = _init_l_Lean_Meta_simpExtension___closed__1();
lean_mark_persistent(l_Lean_Meta_simpExtension___closed__1);
l_Lean_Meta_simpExtension___closed__2 = _init_l_Lean_Meta_simpExtension___closed__2();
lean_mark_persistent(l_Lean_Meta_simpExtension___closed__2);
l_Lean_Meta_simpExtension___closed__3 = _init_l_Lean_Meta_simpExtension___closed__3();
lean_mark_persistent(l_Lean_Meta_simpExtension___closed__3);
l_Lean_Meta_simpExtension___closed__4 = _init_l_Lean_Meta_simpExtension___closed__4();
lean_mark_persistent(l_Lean_Meta_simpExtension___closed__4);
l_Lean_Meta_simpExtension___closed__5 = _init_l_Lean_Meta_simpExtension___closed__5();
lean_mark_persistent(l_Lean_Meta_simpExtension___closed__5);
l_Lean_Meta_simpExtension___closed__6 = _init_l_Lean_Meta_simpExtension___closed__6();
lean_mark_persistent(l_Lean_Meta_simpExtension___closed__6);
l_Lean_Meta_simpExtension___closed__7 = _init_l_Lean_Meta_simpExtension___closed__7();
lean_mark_persistent(l_Lean_Meta_simpExtension___closed__7);
l_Lean_Meta_simpExtension___closed__8 = _init_l_Lean_Meta_simpExtension___closed__8();
lean_mark_persistent(l_Lean_Meta_simpExtension___closed__8);
l_Lean_Meta_simpExtension___closed__9 = _init_l_Lean_Meta_simpExtension___closed__9();
lean_mark_persistent(l_Lean_Meta_simpExtension___closed__9);
l_Lean_Meta_simpExtension___closed__10 = _init_l_Lean_Meta_simpExtension___closed__10();
lean_mark_persistent(l_Lean_Meta_simpExtension___closed__10);
l_Lean_Meta_simpExtension___closed__11 = _init_l_Lean_Meta_simpExtension___closed__11();
lean_mark_persistent(l_Lean_Meta_simpExtension___closed__11);
l_Lean_Meta_simpExtension___closed__12 = _init_l_Lean_Meta_simpExtension___closed__12();
lean_mark_persistent(l_Lean_Meta_simpExtension___closed__12);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_474_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_simpExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_simpExtension);
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_shouldPreprocess___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__4);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__5);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__6);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__7 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__7);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__8 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__8);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__9 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__9);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__10 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__10);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__11 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__11);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__12 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__12);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__13 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__13);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__14 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_preprocess___closed__14);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_checkTypeIsProp___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__2);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__3);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmaCore___lambda__2___closed__4);
l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_SimpLemmas_0__Lean_Meta_mkSimpLemmasFromConst___closed__1);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__1 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__1();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__1);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__2 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__2();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__2);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__3 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__3();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__3);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__4 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__4();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__4);
l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__5 = _init_l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__5();
lean_mark_persistent(l_Lean_EnvExtensionInterfaceUnsafe_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__3___closed__5);
l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__1 = _init_l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__1);
l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__2 = _init_l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__2();
lean_mark_persistent(l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__2);
l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__3 = _init_l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__3();
lean_mark_persistent(l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__3);
l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__4 = _init_l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__4();
lean_mark_persistent(l_Lean_ScopedEnvExtension_getState___at_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____spec__1___closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__11 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__11();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__11);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__12 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__12();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__12);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__13 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__13();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__13);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__14 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__14();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__14);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__15 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__15();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__15);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__16 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__16();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__16);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__17 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__17();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__17);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__18 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__18();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__18);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__19 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__19();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__19);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__20 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__20();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__20);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__21 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__21();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__21);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__22 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__22();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__22);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__23 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__23();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__23);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__24 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__24();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__24);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__25 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__25();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__25);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__26 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__26();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____lambda__1___closed__26);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304____closed__7);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpLemmas___hyg_2304_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_SimpLemma_getValue___closed__1 = _init_l_Lean_Meta_SimpLemma_getValue___closed__1();
lean_mark_persistent(l_Lean_Meta_SimpLemma_getValue___closed__1);
l_Lean_Meta_SimpLemma_getValue___closed__2 = _init_l_Lean_Meta_SimpLemma_getValue___closed__2();
lean_mark_persistent(l_Lean_Meta_SimpLemma_getValue___closed__2);
l_Lean_Meta_SimpLemma_getValue___closed__3 = _init_l_Lean_Meta_SimpLemma_getValue___closed__3();
lean_mark_persistent(l_Lean_Meta_SimpLemma_getValue___closed__3);
l_Lean_Meta_SimpLemma_getValue___closed__4 = _init_l_Lean_Meta_SimpLemma_getValue___closed__4();
lean_mark_persistent(l_Lean_Meta_SimpLemma_getValue___closed__4);
l_Lean_Meta_SimpLemma_getValue___boxed__const__1 = _init_l_Lean_Meta_SimpLemma_getValue___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_SimpLemma_getValue___boxed__const__1);
l_Lean_Meta_mkSimpLemmas___boxed__const__1 = _init_l_Lean_Meta_mkSimpLemmas___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_mkSimpLemmas___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
