// Lean compiler output
// Module: Lean.Elab.InfoTree
// Imports: Init Lean.Data.Position Lean.Expr Lean.Message Lean.Data.Json Lean.Meta.Basic Lean.Meta.PPGoal
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
lean_object* l_Lean_Elab_withInfoHole___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Elab_Info_format(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoContext(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Elab_InfoTree_substitute_match__1(lean_object*);
lean_object* l_Std_fmt___at_Lean_Elab_TermInfo_format___spec__1(lean_object*);
extern lean_object* l_Lean_Meta_ppGoal_ppVars___closed__1;
extern lean_object* l_Lean_InternalExceptionId_toString___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_pushInfoTree___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_InfoTree_substitute___spec__6(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
lean_object* l_Lean_Elab_withInfoContext_x27(lean_object*);
lean_object* l_Lean_Elab_TacticInfo_format(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoContext_x27___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_TermInfo_format___lambda__1___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_assignInfoHoleId___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_getAux___at_Lean_Elab_withInfoHole___spec__2(lean_object*, size_t, size_t);
lean_object* l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__1;
lean_object* l_Lean_Elab_instInhabitedTermInfo;
lean_object* l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__4;
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_modifyInfoTrees___rarg(lean_object*, lean_object*);
extern lean_object* l_Std_Format_join___closed__1;
size_t l_USize_sub(size_t, size_t);
lean_object* l_Lean_Elab_InfoTree_format_match__1(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoContext_x27_match__1(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_enableInfoTree(lean_object*);
lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_modifyInfoTrees(lean_object*);
extern lean_object* l_instReprSigma___rarg___closed__1;
lean_object* l_Lean_Elab_ContextInfo_runMetaM_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_TermInfo_format___lambda__1___closed__3;
lean_object* l_Lean_Elab_Info_format_match__1(lean_object*);
lean_object* l_Lean_Elab_getInfoTrees___rarg___lambda__1(lean_object*, lean_object*);
extern lean_object* l_instReprSigma___rarg___closed__7;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_getAux___at_Lean_Elab_withInfoHole___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoContext_x27___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
lean_object* l_Lean_Elab_MacroExpansionInfo_format___closed__3;
lean_object* l_Lean_Elab_withInfoHole___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_format(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instInhabitedFieldInfo___closed__1;
lean_object* l_Lean_Elab_withInfoContext___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Elab_withInfoContext_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_options___default;
lean_object* l_Lean_Elab_instMonadInfoTree___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoContext___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_instInhabitedPersistentArray___closed__1;
lean_object* l_Lean_Elab_TacticInfo_format___closed__4;
lean_object* l_Std_PersistentArray_get_x21___at_Lean_Elab_withInfoHole___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_format_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Elab_InfoTree_format_match__2(lean_object*);
lean_object* l_Lean_Elab_withInfoContext_x27___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoHole(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedCache___closed__1;
lean_object* l_Lean_Meta_ppGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_mkEmpty___closed__1;
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Elab_assignInfoHoleId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
extern lean_object* l___private_Init_Meta_0__Lean_Meta_Simp_reprConfig____x40_Init_Meta___hyg_6324____closed__4;
lean_object* l_Lean_Elab_FieldInfo_format___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__1;
lean_object* l_Lean_Elab_mkInfoNode(lean_object*);
lean_object* l_Lean_Elab_pushInfoTree___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withMacroExpansionInfo___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_substitute_match__2(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_enableInfoTree___rarg(lean_object*, uint8_t);
lean_object* l_Lean_Elab_TacticInfo_format___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_insertAux___rarg___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Std_mkPersistentArray___rarg___closed__1;
lean_object* l_Lean_Elab_pushInfoTree___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_substitute_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoContext___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoHole___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Elab_assignInfoHoleId___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoContext_x27___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoContext___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_format_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__3;
lean_object* l_Lean_Elab_ContextInfo_mctx___default;
lean_object* l_Lean_Elab_withInfoHole___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instInhabitedInfoTree___closed__1;
lean_object* l_Lean_Elab_withInfoContext_x27_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_instInhabitedMetavarContext___closed__1;
lean_object* l_Lean_Elab_mkInfoNode___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object*);
lean_object* l_Lean_Elab_TermInfo_format___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_TermInfo_format___lambda__1___closed__1;
lean_object* l_Lean_Elab_TacticInfo_format___closed__1;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Elab_assignInfoHoleId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instInhabitedTacticInfo___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__5(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_instReprSigma___rarg___closed__5;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Elab_instInhabitedContextInfo___closed__1;
lean_object* l_Lean_Elab_withInfoHole_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoState_assignment___default;
lean_object* l_Lean_Elab_TermInfo_format___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instMonadInfoTree___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoContext_x27_match__2___rarg(lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
lean_object* l_Lean_Elab_mkInfoNode___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_MacroExpansionInfo_format___closed__2;
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Elab_assignInfoHoleId___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_TermInfo_format(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instInhabitedInfo;
lean_object* l_Lean_Elab_ContextInfo_openDecls___default;
lean_object* l_Lean_Elab_withInfoContext_x27___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoContext_x27___rarg___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Elab_assignInfoHoleId___spec__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__1;
lean_object* l_Lean_Elab_InfoTree_substitute_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_InfoTree_substitute___spec__7(lean_object*, size_t, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__5;
extern lean_object* l_Lean_Unhygienic_run___rarg___closed__2;
lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__2;
lean_object* l_Lean_Elab_getInfoTrees(lean_object*);
lean_object* l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__4;
lean_object* l_Lean_Elab_withInfoContext___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_enableInfoTree___rarg___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Elab_ContextInfo_currNamespace___default;
lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__1;
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_modifyInfoTrees___rarg___lambda__1(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Elab_MacroExpansionInfo_format___closed__4;
lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object*);
lean_object* l_Std_PersistentArray_toList___rarg(lean_object*);
lean_object* l_Std_fmt___at_Lean_Level_PP_Result_format___spec__1(lean_object*);
lean_object* l_Lean_Elab_withInfoContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_term_x2d_____closed__3;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__2;
lean_object* l_ReaderT_instMonadReaderT___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_instInhabitedInfoTree;
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_InfoTree_substitute___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_InfoTree_substitute___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg___lambda__2___closed__1;
lean_object* l_Lean_Elab_InfoTree_format___closed__2;
lean_object* l_Lean_Elab_ContextInfo_runMetaM_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_resetTraceState___rarg___lambda__1___closed__1;
lean_object* l_Std_PersistentArray_mapM___at_Lean_Elab_InfoTree_substitute___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_get_x21___at_Lean_Elab_withInfoHole___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_format___closed__1;
lean_object* l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__2;
lean_object* l_Lean_Elab_instInhabitedInfo___closed__1;
lean_object* l_Lean_Elab_assignInfoHoleId(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_MacroExpansionInfo_format___closed__1;
lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Elab_InfoTree_substitute___spec__2(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr___closed__1;
lean_object* l_List_mapM___at_Lean_Elab_InfoTree_format___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instInhabitedMacroExpansionInfo;
lean_object* l_Lean_Elab_ContextInfo_ppGoals___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_ppGoals___lambda__1___closed__1;
lean_object* l_Lean_Elab_enableInfoTree___rarg___lambda__1(uint8_t, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__4(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_instInhabitedLocalContext___closed__1;
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_InfoTree_substitute___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instMonadInfoTree(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_ppGoals___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Std_fmt___at_Lean_Level_PP_Result_format___spec__2(lean_object*);
lean_object* l_Lean_Elab_withInfoContext_x27___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap___closed__1;
lean_object* l_Lean_Elab_withInfoContext_x27_match__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_instInhabitedContextInfo;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_ppTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkInfoNode___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkInfoNode___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoContext_x27___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_enableInfoTree___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_InfoTree_substitute___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_instInhabitedInfoState;
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg___lambda__1(lean_object*);
lean_object* l_Lean_Elab_FieldInfo_format___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Context_config___default___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
lean_object* l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__3;
lean_object* l_Lean_Syntax_getTailPos(lean_object*);
extern lean_object* l_Lean_Core_instInhabitedState___closed__1;
lean_object* l_List_mapM___at_Lean_Elab_ContextInfo_ppGoals___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_pushInfoTree(lean_object*);
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withMacroExpansionInfo___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object*, lean_object*);
lean_object* l_Lean_Elab_assignInfoHoleId___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_pushInfoTree___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_prefixJoin___at_Lean_Elab_ContextInfo_ppGoals___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees(lean_object*);
extern lean_object* l_Lean_Core_State_ngen___default___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instantiateBetaRevRange___closed__1;
lean_object* l_Lean_Elab_getInfoTrees___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoContext___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_assignInfoHoleId___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instInhabitedTermInfo___closed__1;
lean_object* l_Std_Format_prefixJoin___at_Lean_Elab_ContextInfo_ppGoals___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_instInhabitedTacticInfo;
lean_object* l_Lean_Elab_TacticInfo_format___closed__3;
extern lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushNewline___closed__1;
lean_object* l_Lean_Elab_InfoState_trees___default;
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_InfoState_enabled___default;
lean_object* l_Lean_Elab_withInfoHole___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_tryFinally___rarg___closed__1;
lean_object* l_Lean_Elab_withInfoHole___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
lean_object* l_Lean_Elab_InfoTree_format_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instInhabitedFieldInfo;
lean_object* l_Std_Format_nestD(lean_object*);
lean_object* l_Lean_Elab_withInfoHole_match__1(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_ppGoals___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_instInhabitedInfoState___closed__1;
extern lean_object* l_Std_PersistentArray_getAux___rarg___closed__1;
lean_object* l_Lean_Elab_FieldInfo_format(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withInfoHole___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_ContextInfo_mctx___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MetavarContext_instInhabitedMetavarContext___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_options___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_currNamespace___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_openDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedContextInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_instInhabitedState___closed__1;
x_3 = l_Lean_instInhabitedFileMap___closed__1;
x_4 = l_Lean_MetavarContext_instInhabitedMetavarContext___closed__1;
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set(x_6, 5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedContextInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedContextInfo___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_instInhabitedLocalContext___closed__1;
x_2 = l_Lean_instInhabitedExpr___closed__1;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTermInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedTermInfo___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFieldInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_instInhabitedLocalContext___closed__1;
x_3 = l_Lean_instInhabitedExpr___closed__1;
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedFieldInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedFieldInfo___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_MetavarContext_instInhabitedMetavarContext___closed__1;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_2);
lean_ctor_set(x_4, 4, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedTacticInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedTacticInfo___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedLocalContext___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedMacroExpansionInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_instInhabitedTacticInfo___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedInfo___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_instInhabitedInfo___closed__1;
x_2 = l_Std_instInhabitedPersistentArray___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoTree() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedInfoTree___closed__1;
return x_1;
}
}
static uint8_t _init_l_Lean_Elab_InfoState_enabled___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_InfoState_assignment___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_InfoState_trees___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentArray_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_3 = l_Std_instInhabitedPersistentArray___closed__1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedInfoState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedInfoState___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_instMonadInfoTree___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_instMonadInfoTree___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_instMonadInfoTree___rarg___lambda__1), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_instMonadInfoTree(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_instMonadInfoTree___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_InfoTree_substitute_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_InfoTree_substitute_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_substitute_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_InfoTree_substitute_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_2(x_2, x_9, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_1(x_5, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Elab_InfoTree_substitute_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_substitute_match__2___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Std_PersistentArray_mapMAux___at_Lean_Elab_InfoTree_substitute___spec__2(x_1, x_10);
x_12 = 1;
x_13 = x_3 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_9, x_3, x_14);
x_3 = x_13;
x_4 = x_15;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Elab_InfoTree_substitute(x_10, x_1);
x_12 = 1;
x_13 = x_3 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_9, x_3, x_14);
x_3 = x_13;
x_4 = x_15;
goto _start;
}
}
}
lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Elab_InfoTree_substitute___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = x_4;
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__3(x_1, x_6, x_7, x_8);
x_10 = x_9;
lean_ctor_set(x_2, 0, x_10);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_array_get_size(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = x_11;
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__3(x_1, x_13, x_14, x_15);
x_17 = x_16;
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_array_get_size(x_20);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = x_20;
x_25 = l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__4(x_1, x_22, x_23, x_24);
x_26 = x_25;
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
else
{
lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_array_get_size(x_27);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = 0;
x_31 = x_27;
x_32 = l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__4(x_1, x_29, x_30, x_31);
x_33 = x_32;
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_Elab_InfoTree_substitute(x_10, x_1);
x_12 = 1;
x_13 = x_3 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_9, x_3, x_14);
x_3 = x_13;
x_4 = x_15;
goto _start;
}
}
}
lean_object* l_Std_PersistentArray_mapM___at_Lean_Elab_InfoTree_substitute___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_6 = l_Std_PersistentArray_mapMAux___at_Lean_Elab_InfoTree_substitute___spec__2(x_1, x_4);
x_7 = lean_array_get_size(x_5);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = x_5;
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__5(x_1, x_8, x_9, x_10);
x_12 = x_11;
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
x_16 = lean_ctor_get_usize(x_2, 4);
x_17 = lean_ctor_get(x_2, 3);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_1);
x_18 = l_Std_PersistentArray_mapMAux___at_Lean_Elab_InfoTree_substitute___spec__2(x_1, x_13);
x_19 = lean_array_get_size(x_14);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 0;
x_22 = x_14;
x_23 = l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__5(x_1, x_20, x_21, x_22);
x_24 = x_23;
x_25 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_15);
lean_ctor_set(x_25, 3, x_17);
lean_ctor_set_usize(x_25, 4, x_16);
return x_25;
}
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_InfoTree_substitute___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_InfoTree_substitute___spec__7(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_InfoTree_substitute___spec__8(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_InfoTree_substitute___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Elab_InfoTree_substitute___spec__7(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Elab_InfoTree_substitute(x_4, x_2);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = l_Lean_Elab_InfoTree_substitute(x_7, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
case 1:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Std_PersistentArray_mapM___at_Lean_Elab_InfoTree_substitute___spec__1(x_2, x_11);
lean_ctor_set(x_1, 1, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Std_PersistentArray_mapM___at_Lean_Elab_InfoTree_substitute___spec__1(x_2, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
case 2:
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
default: 
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_22 = l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_InfoTree_substitute___spec__6(x_2, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_23; 
lean_free_object(x_1);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_1 = x_23;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
lean_inc(x_2);
x_26 = l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_InfoTree_substitute___spec__6(x_2, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_2);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_1 = x_28;
goto _start;
}
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__3(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__4(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Elab_InfoTree_substitute___spec__5(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_InfoTree_substitute___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_InfoTree_substitute___spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_InfoTree_substitute___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Elab_InfoTree_substitute___spec__7(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_InfoTree_substitute___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_InfoTree_substitute___spec__6(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_ContextInfo_runMetaM_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Lean_Elab_ContextInfo_runMetaM_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM_match__1___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_ContextInfo_runMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_5 = l_Lean_Meta_Context_config___default___closed__1;
x_6 = l_Array_empty___closed__1;
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
x_13 = l_Lean_Meta_instInhabitedCache___closed__1;
x_14 = l_Lean_NameSet_empty;
x_15 = l_Std_PersistentArray_empty___closed__1;
lean_inc(x_9);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(1000u);
x_19 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
lean_ctor_set(x_20, 4, x_11);
lean_ctor_set(x_20, 5, x_12);
x_21 = l_Lean_Unhygienic_run___rarg___closed__2;
x_22 = l_Lean_Core_State_ngen___default___closed__1;
x_23 = l_Lean_resetTraceState___rarg___lambda__1___closed__1;
lean_inc(x_8);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
x_25 = lean_st_mk_ref(x_24, x_4);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_26, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_mk_ref(x_16, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_26);
lean_inc(x_31);
x_33 = lean_apply_5(x_3, x_7, x_31, x_20, x_26, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_26, x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_ref_get(x_31, x_37);
lean_dec(x_31);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_st_ref_get(x_26, x_39);
lean_dec(x_26);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_34);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; 
lean_dec(x_31);
lean_dec(x_26);
x_45 = lean_ctor_get(x_33, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_33, 1);
lean_inc(x_46);
lean_dec(x_33);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_MessageData_toString(x_47, x_46);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set_tag(x_48, 1);
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
x_54 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
uint8_t x_56; 
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
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_33);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_33, 0);
lean_dec(x_61);
x_62 = lean_ctor_get(x_45, 0);
lean_inc(x_62);
lean_dec(x_45);
x_63 = l_Nat_repr(x_62);
x_64 = l_Lean_InternalExceptionId_toString___closed__1;
x_65 = lean_string_append(x_64, x_63);
lean_dec(x_63);
x_66 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_33, 0, x_66);
return x_33;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_33, 1);
lean_inc(x_67);
lean_dec(x_33);
x_68 = lean_ctor_get(x_45, 0);
lean_inc(x_68);
lean_dec(x_45);
x_69 = l_Nat_repr(x_68);
x_70 = l_Lean_InternalExceptionId_toString___closed__1;
x_71 = lean_string_append(x_70, x_69);
lean_dec(x_69);
x_72 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_67);
return x_73;
}
}
}
}
}
lean_object* l_Lean_Elab_ContextInfo_runMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_runMetaM___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_ContextInfo_runMetaM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_ContextInfo_toPPContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get(x_1, 5);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_2);
lean_ctor_set(x_8, 3, x_5);
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set(x_8, 5, x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_ContextInfo_toPPContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_ContextInfo_toPPContext(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_ContextInfo_ppSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_ContextInfo_toPPContext(x_1, x_2);
x_6 = l_Lean_ppTerm(x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_ContextInfo_ppSyntax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_ContextInfo_ppSyntax(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Std_fmt___at_Lean_Elab_TermInfo_format___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_fmt___at_Lean_Level_PP_Result_format___spec__2(x_2);
x_5 = l_instReprSigma___rarg___closed__5;
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_instReprSigma___rarg___closed__1;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Std_fmt___at_Lean_Level_PP_Result_format___spec__2(x_3);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_instReprSigma___rarg___closed__7;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_TermInfo_format___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" @ ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_TermInfo_format___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_TermInfo_format___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_TermInfo_format___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_term_x2d_____closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_TermInfo_format___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_inferType(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_ppExpr(x_12, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Std_Format_join___closed__1;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
x_19 = l_Lean_Meta_ppGoal_ppVars___closed__1;
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = l_Lean_Elab_TermInfo_format___lambda__1___closed__2;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_ctor_get(x_2, 1);
x_25 = l_Lean_FileMap_toPosition(x_24, x_3);
x_26 = l_Std_fmt___at_Lean_Elab_TermInfo_format___spec__1(x_25);
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_TermInfo_format___lambda__1___closed__3;
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_FileMap_toPosition(x_24, x_4);
x_31 = l_Std_fmt___at_Lean_Elab_TermInfo_format___spec__1(x_30);
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_17);
lean_ctor_set(x_14, 0, x_33);
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = l_Std_Format_join___closed__1;
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_5);
x_38 = l_Lean_Meta_ppGoal_ppVars___closed__1;
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
x_41 = l_Lean_Elab_TermInfo_format___lambda__1___closed__2;
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_ctor_get(x_2, 1);
x_44 = l_Lean_FileMap_toPosition(x_43, x_3);
x_45 = l_Std_fmt___at_Lean_Elab_TermInfo_format___spec__1(x_44);
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Elab_TermInfo_format___lambda__1___closed__3;
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_FileMap_toPosition(x_43, x_4);
x_50 = l_Std_fmt___at_Lean_Elab_TermInfo_format___spec__1(x_49);
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_36);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_35);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_14);
if (x_54 == 0)
{
return x_14;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_14, 0);
x_56 = lean_ctor_get(x_14, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_11);
if (x_58 == 0)
{
return x_11;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_11, 0);
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_11);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
lean_object* l_Lean_Elab_TermInfo_format(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = l_Lean_Syntax_getPos(x_5);
x_7 = l_Lean_Syntax_getTailPos(x_5);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_ppExpr___boxed), 6, 1);
lean_closure_set(x_9, 0, x_8);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_18; 
x_18 = lean_unsigned_to_nat(0u);
x_10 = x_18;
goto block_17;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_dec(x_6);
x_10 = x_19;
goto block_17;
}
block_17:
{
lean_object* x_11; 
if (lean_obj_tag(x_7) == 0)
{
lean_inc(x_10);
x_11 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec(x_7);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_TermInfo_format___lambda__1___boxed), 10, 4);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_11);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_1, x_4, x_13, x_3);
lean_dec(x_1);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_TermInfo_format___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_TermInfo_format___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_FieldInfo_format___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_ppExpr(x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_ppExpr(x_1, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l_Std_fmt___at_Lean_Level_PP_Result_format___spec__1(x_18);
x_20 = l_Std_Format_join___closed__1;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Meta_ppGoal_ppVars___closed__1;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_13);
x_25 = l___private_Init_Meta_0__Lean_Meta_Simp_reprConfig____x40_Init_Meta___hyg_6324____closed__4;
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_17);
x_28 = l_Lean_Elab_TermInfo_format___lambda__1___closed__2;
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_ctor_get(x_3, 1);
x_31 = l_Lean_FileMap_toPosition(x_30, x_4);
x_32 = l_Std_fmt___at_Lean_Elab_TermInfo_format___spec__1(x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Elab_TermInfo_format___lambda__1___closed__3;
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_FileMap_toPosition(x_30, x_5);
x_37 = l_Std_fmt___at_Lean_Elab_TermInfo_format___spec__1(x_36);
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_20);
lean_ctor_set(x_15, 0, x_39);
return x_15;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_40 = lean_ctor_get(x_15, 0);
x_41 = lean_ctor_get(x_15, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_15);
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
lean_dec(x_2);
x_43 = l_Std_fmt___at_Lean_Level_PP_Result_format___spec__1(x_42);
x_44 = l_Std_Format_join___closed__1;
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Meta_ppGoal_ppVars___closed__1;
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_13);
x_49 = l___private_Init_Meta_0__Lean_Meta_Simp_reprConfig____x40_Init_Meta___hyg_6324____closed__4;
x_50 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_40);
x_52 = l_Lean_Elab_TermInfo_format___lambda__1___closed__2;
x_53 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_ctor_get(x_3, 1);
x_55 = l_Lean_FileMap_toPosition(x_54, x_4);
x_56 = l_Std_fmt___at_Lean_Elab_TermInfo_format___spec__1(x_55);
x_57 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Elab_TermInfo_format___lambda__1___closed__3;
x_59 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_FileMap_toPosition(x_54, x_5);
x_61 = l_Std_fmt___at_Lean_Elab_TermInfo_format___spec__1(x_60);
x_62 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_44);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_41);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_15);
if (x_65 == 0)
{
return x_15;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_15, 0);
x_67 = lean_ctor_get(x_15, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_12);
if (x_69 == 0)
{
return x_12;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_12, 0);
x_71 = lean_ctor_get(x_12, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_12);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
lean_object* l_Lean_Elab_FieldInfo_format(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = l_Lean_Syntax_getPos(x_5);
x_7 = l_Lean_Syntax_getTailPos(x_5);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_inferType), 6, 1);
lean_closure_set(x_9, 0, x_8);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_18; 
x_18 = lean_unsigned_to_nat(0u);
x_10 = x_18;
goto block_17;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_dec(x_6);
x_10 = x_19;
goto block_17;
}
block_17:
{
lean_object* x_11; 
if (lean_obj_tag(x_7) == 0)
{
lean_inc(x_10);
x_11 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
lean_dec(x_7);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_FieldInfo_format___lambda__1___boxed), 11, 5);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_1);
lean_closure_set(x_12, 3, x_10);
lean_closure_set(x_12, 4, x_11);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_1, x_4, x_13, x_3);
lean_dec(x_1);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_FieldInfo_format___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_FieldInfo_format___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_List_mapM___at_Lean_Elab_ContextInfo_ppGoals___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Meta_ppGoal(x_10, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_mapM___at_Lean_Elab_ContextInfo_ppGoals___spec__1(x_11, x_2, x_3, x_4, x_5, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_13);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_free_object(x_1);
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
uint8_t x_25; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_31 = l_Lean_Meta_ppGoal(x_29, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_List_mapM___at_Lean_Elab_ContextInfo_ppGoals___spec__1(x_30, x_2, x_3, x_4, x_5, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_35);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_32);
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_42 = x_34;
} else {
 lean_dec_ref(x_34);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_30);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_31, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_31, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_46 = x_31;
} else {
 lean_dec_ref(x_31);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
}
lean_object* l_Std_Format_prefixJoin___at_Lean_Elab_ContextInfo_ppGoals___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_inc(x_1);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Std_Format_prefixJoin___at_Lean_Elab_ContextInfo_ppGoals___spec__2(x_1, x_5);
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Format_Basic_0__Std_Format_pushNewline___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_ContextInfo_ppGoals___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Elab_ContextInfo_ppGoals___lambda__1___closed__1;
x_8 = l_Std_Format_prefixJoin___at_Lean_Elab_ContextInfo_ppGoals___spec__2(x_7, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_ContextInfo_ppGoals___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no goals");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ContextInfo_ppGoals___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_ContextInfo_ppGoals(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_List_isEmpty___rarg(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_alloc_closure((void*)(l_List_mapM___at_Lean_Elab_ContextInfo_ppGoals___spec__1), 6, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_Lean_Elab_ContextInfo_ppGoals___closed__1;
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
x_8 = l_Lean_LocalContext_mkEmpty___closed__1;
x_9 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_1, x_8, x_7, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = l_Lean_Elab_ContextInfo_ppGoals___closed__3;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
lean_object* l_Std_Format_prefixJoin___at_Lean_Elab_ContextInfo_ppGoals___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Format_prefixJoin___at_Lean_Elab_ContextInfo_ppGoals___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_ContextInfo_ppGoals___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_ContextInfo_ppGoals___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_ContextInfo_ppGoals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_ContextInfo_ppGoals(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_TacticInfo_format___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic\nbefore ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_TacticInfo_format___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_TacticInfo_format___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_TacticInfo_format___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nafter ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_TacticInfo_format___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_TacticInfo_format___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_TacticInfo_format(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_1, 5);
x_10 = lean_ctor_get(x_1, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_ctor_set(x_1, 2, x_11);
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_6);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_7);
lean_ctor_set(x_13, 4, x_8);
lean_ctor_set(x_13, 5, x_9);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = l_Lean_Elab_ContextInfo_ppGoals(x_1, x_14, x_3);
lean_dec(x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_2, 4);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l_Lean_Elab_ContextInfo_ppGoals(x_13, x_18, x_17);
lean_dec(x_13);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_Elab_TacticInfo_format___closed__2;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
x_24 = l_Lean_Elab_TacticInfo_format___closed__4;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
x_27 = l_Std_Format_join___closed__1;
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = l_Lean_Elab_TacticInfo_format___closed__2;
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_16);
x_33 = l_Lean_Elab_TacticInfo_format___closed__4;
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
x_36 = l_Std_Format_join___closed__1;
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_30);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_16);
x_39 = !lean_is_exclusive(x_19);
if (x_39 == 0)
{
return x_19;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_19, 0);
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_19);
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
lean_dec(x_13);
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
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_1, 0);
x_48 = lean_ctor_get(x_1, 1);
x_49 = lean_ctor_get(x_1, 3);
x_50 = lean_ctor_get(x_1, 4);
x_51 = lean_ctor_get(x_1, 5);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_1);
x_52 = lean_ctor_get(x_2, 0);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
x_53 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set(x_53, 3, x_49);
lean_ctor_set(x_53, 4, x_50);
lean_ctor_set(x_53, 5, x_51);
x_54 = lean_ctor_get(x_2, 3);
lean_inc(x_54);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_48);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set(x_55, 3, x_49);
lean_ctor_set(x_55, 4, x_50);
lean_ctor_set(x_55, 5, x_51);
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
x_57 = l_Lean_Elab_ContextInfo_ppGoals(x_53, x_56, x_3);
lean_dec(x_53);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_2, 4);
lean_inc(x_60);
lean_dec(x_2);
x_61 = l_Lean_Elab_ContextInfo_ppGoals(x_55, x_60, x_59);
lean_dec(x_55);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = l_Lean_Elab_TacticInfo_format___closed__2;
x_66 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_58);
x_67 = l_Lean_Elab_TacticInfo_format___closed__4;
x_68 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_62);
x_70 = l_Std_Format_join___closed__1;
x_71 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
if (lean_is_scalar(x_64)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_64;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_63);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_58);
x_73 = lean_ctor_get(x_61, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_61, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_75 = x_61;
} else {
 lean_dec_ref(x_61);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_55);
lean_dec(x_2);
x_77 = lean_ctor_get(x_57, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_57, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_79 = x_57;
} else {
 lean_dec_ref(x_57);
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
}
static lean_object* _init_l_Lean_Elab_MacroExpansionInfo_format___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Macro expansion\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_MacroExpansionInfo_format___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_MacroExpansionInfo_format___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_MacroExpansionInfo_format___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n===>\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_MacroExpansionInfo_format___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_MacroExpansionInfo_format___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_MacroExpansionInfo_format(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
x_6 = l_Lean_Elab_ContextInfo_ppSyntax(x_1, x_4, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Elab_ContextInfo_ppSyntax(x_1, x_4, x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Elab_MacroExpansionInfo_format___closed__2;
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
x_15 = l_Lean_Elab_MacroExpansionInfo_format___closed__4;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
x_18 = l_Std_Format_join___closed__1;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = l_Lean_Elab_MacroExpansionInfo_format___closed__2;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
x_24 = l_Lean_Elab_MacroExpansionInfo_format___closed__4;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
x_27 = l_Std_Format_join___closed__1;
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_7);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
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
lean_dec(x_4);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_6);
if (x_34 == 0)
{
return x_6;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_6, 0);
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_6);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_Elab_MacroExpansionInfo_format___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_MacroExpansionInfo_format(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Info_format_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_1(x_5, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Elab_Info_format_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Info_format_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Info_format(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Elab_TacticInfo_format(x_1, x_4, x_3);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Elab_TermInfo_format(x_1, x_6, x_3);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Elab_MacroExpansionInfo_format(x_1, x_8, x_3);
lean_dec(x_1);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Elab_FieldInfo_format(x_1, x_10, x_3);
return x_11;
}
}
}
}
lean_object* l_Lean_Elab_InfoTree_format_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_InfoTree_format_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_format_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_InfoTree_format_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_4, x_6, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_2(x_5, x_9, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_1(x_2, x_12);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_1(x_3, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Elab_InfoTree_format_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_format_match__2___rarg), 5, 0);
return x_2;
}
}
lean_object* l_List_mapM___at_Lean_Elab_InfoTree_format___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_9 = l_Lean_Elab_InfoTree_format(x_7, x_1, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_mapM___at_Lean_Elab_InfoTree_format___spec__1(x_1, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_2, 1, x_14);
lean_ctor_set(x_2, 0, x_10);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_2, 0, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_free_object(x_2);
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
else
{
uint8_t x_22; 
lean_free_object(x_2);
lean_dec(x_8);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
lean_inc(x_1);
x_28 = l_Lean_Elab_InfoTree_format(x_26, x_1, x_3);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_List_mapM___at_Lean_Elab_InfoTree_format___spec__1(x_1, x_27, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_32);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_29);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_39 = x_31;
} else {
 lean_dec_ref(x_31);
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
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_27);
lean_dec(x_1);
x_41 = lean_ctor_get(x_28, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_43 = x_28;
} else {
 lean_dec_ref(x_28);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_InfoTree_format___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<context-not-available>");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_InfoTree_format___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_InfoTree_format___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_InfoTree_format(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
case 1:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = l_Lean_Elab_InfoTree_format___closed__2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Info_format(x_12, x_10, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Std_PersistentArray_toList___rarg(x_11);
lean_dec(x_11);
x_20 = l_List_mapM___at_Lean_Elab_InfoTree_format___spec__1(x_2, x_19, x_18);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Std_Format_join___closed__1;
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Elab_ContextInfo_ppGoals___lambda__1___closed__1;
x_27 = l_Std_Format_prefixJoin___at_Lean_Elab_ContextInfo_ppGoals___spec__2(x_26, x_22);
lean_dec(x_22);
x_28 = l_Std_Format_nestD(x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_20, 0, x_30);
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = l_Std_Format_join___closed__1;
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_17);
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Elab_ContextInfo_ppGoals___lambda__1___closed__1;
x_37 = l_Std_Format_prefixJoin___at_Lean_Elab_ContextInfo_ppGoals___spec__2(x_36, x_31);
lean_dec(x_31);
x_38 = l_Std_Format_nestD(x_37);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_32);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_17);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_20, 0);
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_20);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_16);
if (x_46 == 0)
{
return x_16;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_16, 0);
x_48 = lean_ctor_get(x_16, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_16);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_11);
lean_dec(x_2);
x_50 = l_Lean_Elab_Info_format(x_12, x_10, x_3);
return x_50;
}
}
}
case 2:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
lean_dec(x_1);
x_52 = lean_unsigned_to_nat(80u);
x_53 = l_Lean_Json_pretty(x_51, x_52);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_3);
return x_55;
}
default: 
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_2);
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
lean_dec(x_1);
x_57 = l_Lean_Name_toString___closed__1;
x_58 = l_Lean_Name_toStringWithSep(x_57, x_56);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_3);
return x_60;
}
}
}
}
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_modifyInfoTrees___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_6);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_modifyInfoTrees___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_0__Lean_Elab_modifyInfoTrees___rarg___lambda__1), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_modifyInfoTrees(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_0__Lean_Elab_modifyInfoTrees___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Std_PersistentArray_empty___closed__1;
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Std_PersistentArray_empty___closed__1;
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_5);
return x_8;
}
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg___lambda__2___closed__1;
x_8 = lean_apply_1(x_6, x_7);
x_9 = lean_alloc_closure((void*)(l_ReaderT_instMonadReaderT___rarg___lambda__4___boxed), 3, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_5);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg___lambda__2), 4, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
lean_closure_set(x_5, 2, x_3);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_pushInfoTree___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Std_PersistentArray_push___rarg(x_4, x_1);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = l_Std_PersistentArray_push___rarg(x_8, x_1);
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_6);
return x_10;
}
}
}
lean_object* l_Lean_Elab_pushInfoTree___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___rarg___lambda__1), 2, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = lean_apply_1(x_10, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Elab_pushInfoTree___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___rarg___lambda__2___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_pushInfoTree(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_pushInfoTree___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_pushInfoTree___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoTree___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_mkInfoNode___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Std_mkPersistentArray___rarg___closed__1;
x_7 = l_Std_PersistentArray_push___rarg(x_6, x_5);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Std_mkPersistentArray___rarg___closed__1;
x_13 = l_Std_PersistentArray_push___rarg(x_12, x_11);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_8);
return x_14;
}
}
}
lean_object* l_Lean_Elab_mkInfoNode___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_mkInfoNode___rarg___lambda__1), 2, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = lean_apply_1(x_10, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Elab_mkInfoNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_mkInfoNode___rarg___lambda__2___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_mkInfoNode(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_mkInfoNode___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_mkInfoNode___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_mkInfoNode___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_withInfoContext_x27_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_withInfoContext_x27_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_withInfoContext_x27_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_withInfoContext_x27_match__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27_match__2___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_withInfoContext_x27___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
else
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_5);
return x_7;
}
}
}
lean_object* l_Lean_Elab_withInfoContext_x27___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Std_PersistentArray_push___rarg(x_2, x_7);
lean_ctor_set(x_3, 1, x_8);
return x_3;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Std_PersistentArray_push___rarg(x_2, x_13);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_9);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_3, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Std_PersistentArray_push___rarg(x_2, x_19);
lean_ctor_set(x_3, 1, x_20);
return x_3;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Std_PersistentArray_push___rarg(x_2, x_24);
x_26 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_21);
return x_26;
}
}
}
}
lean_object* l_Lean_Elab_withInfoContext_x27___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___rarg___lambda__2___boxed), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_withInfoContext_x27___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___rarg___lambda__1), 2, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = lean_apply_1(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_apply_1(x_3, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___rarg___lambda__3), 3, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Elab_withInfoContext_x27___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___rarg___lambda__4), 5, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_7);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_11);
x_13 = l_tryFinally___rarg___closed__1;
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_12);
return x_14;
}
}
lean_object* l_Lean_Elab_withInfoContext_x27___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg(x_2, x_3);
lean_inc(x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___rarg___lambda__5), 7, 6);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_5);
lean_closure_set(x_10, 4, x_6);
lean_closure_set(x_10, 5, x_1);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Elab_withInfoContext_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___rarg___lambda__6___boxed), 7, 6);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_6);
lean_closure_set(x_9, 4, x_7);
lean_closure_set(x_9, 5, x_4);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_withInfoContext_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_withInfoContext_x27___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_withInfoContext_x27___rarg___lambda__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_withInfoContext_x27___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_withInfoContext_x27___rarg___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_withInfoContext___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_withInfoContext___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___rarg___lambda__1), 2, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = lean_apply_1(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___rarg___lambda__1), 2, 1);
lean_closure_set(x_10, 0, x_3);
lean_inc(x_4);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___rarg___lambda__3), 3, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
}
lean_object* l_Lean_Elab_withInfoContext___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_7);
lean_closure_set(x_11, 2, x_8);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_11);
x_13 = l_tryFinally___rarg___closed__1;
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_12);
return x_14;
}
}
lean_object* l_Lean_Elab_withInfoContext___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg(x_2, x_3);
lean_inc(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___rarg___lambda__3), 7, 6);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_5);
lean_closure_set(x_10, 4, x_6);
lean_closure_set(x_10, 5, x_1);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Elab_withInfoContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___rarg___lambda__4___boxed), 7, 6);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_7);
lean_closure_set(x_9, 4, x_6);
lean_closure_set(x_9, 5, x_4);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_withInfoContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_withInfoContext___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_withInfoContext___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_withInfoContext___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_withInfoContext___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_InfoTree_substitute___spec__6(x_6, x_2);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_getInfoHoleIdAssignment_x3f___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getInfoHoleIdAssignment_x3f___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getInfoHoleIdAssignment_x3f___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Elab_assignInfoHoleId___spec__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_19 = l_Std_PersistentHashMap_insertAux___at_Lean_Elab_assignInfoHoleId___spec__2(x_6, x_16, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_18;
x_6 = x_19;
goto _start;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Elab_assignInfoHoleId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Elab_assignInfoHoleId___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_Elab_assignInfoHoleId___spec__2(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_Elab_assignInfoHoleId___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_Elab_assignInfoHoleId___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Elab_assignInfoHoleId___spec__4(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = x_85 <= x_3;
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Elab_assignInfoHoleId___spec__3(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Elab_assignInfoHoleId___spec__4(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = x_99 <= x_3;
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Elab_assignInfoHoleId___spec__3(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = 1;
x_9 = l_Std_PersistentHashMap_insertAux___at_Lean_Elab_assignInfoHoleId___spec__2(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Name_hash(x_2);
x_15 = 1;
x_16 = l_Std_PersistentHashMap_insertAux___at_Lean_Elab_assignInfoHoleId___spec__2(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l_Lean_Elab_assignInfoHoleId___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Std_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_5, x_1, x_2);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = l_Std_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_8, x_1, x_2);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_7);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("( a ).isNone\n  ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_instantiateBetaRevRange___closed__1;
x_2 = l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.InfoTree");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.assignInfoHoleId");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__3;
x_2 = l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__4;
x_3 = lean_unsigned_to_nat(199u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_assignInfoHoleId___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_apply_1(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = l_instInhabitedPUnit;
x_10 = l_instInhabited___rarg(x_4, x_9);
x_11 = l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__5;
x_12 = lean_panic_fn(x_10, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Elab_assignInfoHoleId___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Lean_Elab_getInfoHoleIdAssignment_x3f___rarg(x_1, x_2, x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_1);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_assignInfoHoleId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_assignInfoHoleId___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Elab_assignInfoHoleId___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Elab_assignInfoHoleId___spec__3(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Elab_assignInfoHoleId___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_Elab_assignInfoHoleId___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_assignInfoHoleId___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_withMacroExpansionInfo___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_withMacroExpansionInfo___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_6);
lean_inc(x_8);
x_10 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_4, x_9);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext___rarg___lambda__4___boxed), 7, 6);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_8);
lean_closure_set(x_12, 4, x_10);
lean_closure_set(x_12, 5, x_1);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_Elab_withMacroExpansionInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_withMacroExpansionInfo___rarg), 7, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_withInfoHole_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_withInfoHole_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Std_PersistentArray_getAux___at_Lean_Elab_withInfoHole___spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = x_2 >> x_3;
x_6 = lean_usize_to_nat(x_5);
x_7 = l_Std_PersistentArray_getAux___rarg___closed__1;
x_8 = lean_array_get(x_7, x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
x_9 = 1;
x_10 = x_9 << x_3;
x_11 = x_10 - x_9;
x_12 = x_2 & x_11;
x_13 = 5;
x_14 = x_3 - x_13;
x_1 = x_8;
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_usize_to_nat(x_2);
x_18 = l_Lean_Elab_instInhabitedInfoTree;
x_19 = lean_array_get(x_18, x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
return x_19;
}
}
}
lean_object* l_Std_PersistentArray_get_x21___at_Lean_Elab_withInfoHole___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_usize_of_nat(x_2);
x_7 = lean_ctor_get_usize(x_1, 4);
lean_dec(x_1);
x_8 = l_Std_PersistentArray_getAux___at_Lean_Elab_withInfoHole___spec__2(x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
x_11 = l_Lean_Elab_instInhabitedInfoTree;
x_12 = lean_array_get(x_11, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("s.trees.size == 1 -- if size is not one, then API is being misused.\n        ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_instantiateBetaRevRange___closed__1;
x_2 = l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.withInfoHole");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__3;
x_2 = l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__3;
x_3 = lean_unsigned_to_nat(219u);
x_4 = lean_unsigned_to_nat(8u);
x_5 = l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_withInfoHole___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_free_object(x_3);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_Elab_instInhabitedInfoState;
x_11 = l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__4;
x_12 = lean_panic_fn(x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Std_PersistentArray_get_x21___at_Lean_Elab_withInfoHole___spec__1(x_6, x_13);
x_15 = l_Std_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_5, x_1, x_14);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
}
else
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_Elab_instInhabitedInfoState;
x_23 = l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__4;
x_24 = lean_panic_fn(x_22, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Std_PersistentArray_get_x21___at_Lean_Elab_withInfoHole___spec__1(x_18, x_25);
x_27 = l_Std_PersistentHashMap_insert___at_Lean_Elab_assignInfoHoleId___spec__1(x_17, x_1, x_26);
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_16);
return x_28;
}
}
}
}
lean_object* l_Lean_Elab_withInfoHole___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoContext_x27___rarg___lambda__1), 2, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_apply_1(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___rarg___lambda__1), 3, 2);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_apply_1(x_8, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Elab_withInfoHole___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___rarg___lambda__2___boxed), 4, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_6);
lean_closure_set(x_10, 2, x_3);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_10);
x_12 = l_tryFinally___rarg___closed__1;
x_13 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_12, x_11);
return x_13;
}
}
lean_object* l_Lean_Elab_withInfoHole___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg(x_2, x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___rarg___lambda__3), 6, 5);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_5);
lean_closure_set(x_10, 4, x_1);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Elab_withInfoHole___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___rarg___lambda__4___boxed), 7, 6);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_1);
lean_closure_set(x_8, 5, x_6);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_withInfoHole(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_withInfoHole___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Std_PersistentArray_getAux___at_Lean_Elab_withInfoHole___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentArray_getAux___at_Lean_Elab_withInfoHole___spec__2(x_1, x_4, x_5);
return x_6;
}
}
lean_object* l_Std_PersistentArray_get_x21___at_Lean_Elab_withInfoHole___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentArray_get_x21___at_Lean_Elab_withInfoHole___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_withInfoHole___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_withInfoHole___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_withInfoHole___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_withInfoHole___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_enableInfoTree___rarg___lambda__1(uint8_t x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_2);
x_6 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_1);
return x_6;
}
}
}
lean_object* l_Lean_Elab_enableInfoTree___rarg(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_enableInfoTree(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_enableInfoTree___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_enableInfoTree___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Elab_enableInfoTree___rarg___lambda__1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_enableInfoTree___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Elab_enableInfoTree___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_getInfoTrees___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_getInfoTrees___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___rarg___lambda__1), 2, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_getInfoTrees(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_getInfoTrees___rarg), 2, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Position(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
lean_object* initialize_Lean_Message(lean_object*);
lean_object* initialize_Lean_Data_Json(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Lean_Meta_PPGoal(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_InfoTree(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Position(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_PPGoal(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_ContextInfo_mctx___default = _init_l_Lean_Elab_ContextInfo_mctx___default();
lean_mark_persistent(l_Lean_Elab_ContextInfo_mctx___default);
l_Lean_Elab_ContextInfo_options___default = _init_l_Lean_Elab_ContextInfo_options___default();
lean_mark_persistent(l_Lean_Elab_ContextInfo_options___default);
l_Lean_Elab_ContextInfo_currNamespace___default = _init_l_Lean_Elab_ContextInfo_currNamespace___default();
lean_mark_persistent(l_Lean_Elab_ContextInfo_currNamespace___default);
l_Lean_Elab_ContextInfo_openDecls___default = _init_l_Lean_Elab_ContextInfo_openDecls___default();
lean_mark_persistent(l_Lean_Elab_ContextInfo_openDecls___default);
l_Lean_Elab_instInhabitedContextInfo___closed__1 = _init_l_Lean_Elab_instInhabitedContextInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedContextInfo___closed__1);
l_Lean_Elab_instInhabitedContextInfo = _init_l_Lean_Elab_instInhabitedContextInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedContextInfo);
l_Lean_Elab_instInhabitedTermInfo___closed__1 = _init_l_Lean_Elab_instInhabitedTermInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo___closed__1);
l_Lean_Elab_instInhabitedTermInfo = _init_l_Lean_Elab_instInhabitedTermInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedTermInfo);
l_Lean_Elab_instInhabitedFieldInfo___closed__1 = _init_l_Lean_Elab_instInhabitedFieldInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedFieldInfo___closed__1);
l_Lean_Elab_instInhabitedFieldInfo = _init_l_Lean_Elab_instInhabitedFieldInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedFieldInfo);
l_Lean_Elab_instInhabitedTacticInfo___closed__1 = _init_l_Lean_Elab_instInhabitedTacticInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedTacticInfo___closed__1);
l_Lean_Elab_instInhabitedTacticInfo = _init_l_Lean_Elab_instInhabitedTacticInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedTacticInfo);
l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__1 = _init_l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedMacroExpansionInfo___closed__1);
l_Lean_Elab_instInhabitedMacroExpansionInfo = _init_l_Lean_Elab_instInhabitedMacroExpansionInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedMacroExpansionInfo);
l_Lean_Elab_instInhabitedInfo___closed__1 = _init_l_Lean_Elab_instInhabitedInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfo___closed__1);
l_Lean_Elab_instInhabitedInfo = _init_l_Lean_Elab_instInhabitedInfo();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfo);
l_Lean_Elab_instInhabitedInfoTree___closed__1 = _init_l_Lean_Elab_instInhabitedInfoTree___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoTree___closed__1);
l_Lean_Elab_instInhabitedInfoTree = _init_l_Lean_Elab_instInhabitedInfoTree();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoTree);
l_Lean_Elab_InfoState_enabled___default = _init_l_Lean_Elab_InfoState_enabled___default();
l_Lean_Elab_InfoState_assignment___default = _init_l_Lean_Elab_InfoState_assignment___default();
lean_mark_persistent(l_Lean_Elab_InfoState_assignment___default);
l_Lean_Elab_InfoState_trees___default = _init_l_Lean_Elab_InfoState_trees___default();
lean_mark_persistent(l_Lean_Elab_InfoState_trees___default);
l_Lean_Elab_instInhabitedInfoState___closed__1 = _init_l_Lean_Elab_instInhabitedInfoState___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoState___closed__1);
l_Lean_Elab_instInhabitedInfoState = _init_l_Lean_Elab_instInhabitedInfoState();
lean_mark_persistent(l_Lean_Elab_instInhabitedInfoState);
l_Lean_Elab_TermInfo_format___lambda__1___closed__1 = _init_l_Lean_Elab_TermInfo_format___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_TermInfo_format___lambda__1___closed__1);
l_Lean_Elab_TermInfo_format___lambda__1___closed__2 = _init_l_Lean_Elab_TermInfo_format___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_TermInfo_format___lambda__1___closed__2);
l_Lean_Elab_TermInfo_format___lambda__1___closed__3 = _init_l_Lean_Elab_TermInfo_format___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_TermInfo_format___lambda__1___closed__3);
l_Lean_Elab_ContextInfo_ppGoals___lambda__1___closed__1 = _init_l_Lean_Elab_ContextInfo_ppGoals___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_ContextInfo_ppGoals___lambda__1___closed__1);
l_Lean_Elab_ContextInfo_ppGoals___closed__1 = _init_l_Lean_Elab_ContextInfo_ppGoals___closed__1();
lean_mark_persistent(l_Lean_Elab_ContextInfo_ppGoals___closed__1);
l_Lean_Elab_ContextInfo_ppGoals___closed__2 = _init_l_Lean_Elab_ContextInfo_ppGoals___closed__2();
lean_mark_persistent(l_Lean_Elab_ContextInfo_ppGoals___closed__2);
l_Lean_Elab_ContextInfo_ppGoals___closed__3 = _init_l_Lean_Elab_ContextInfo_ppGoals___closed__3();
lean_mark_persistent(l_Lean_Elab_ContextInfo_ppGoals___closed__3);
l_Lean_Elab_TacticInfo_format___closed__1 = _init_l_Lean_Elab_TacticInfo_format___closed__1();
lean_mark_persistent(l_Lean_Elab_TacticInfo_format___closed__1);
l_Lean_Elab_TacticInfo_format___closed__2 = _init_l_Lean_Elab_TacticInfo_format___closed__2();
lean_mark_persistent(l_Lean_Elab_TacticInfo_format___closed__2);
l_Lean_Elab_TacticInfo_format___closed__3 = _init_l_Lean_Elab_TacticInfo_format___closed__3();
lean_mark_persistent(l_Lean_Elab_TacticInfo_format___closed__3);
l_Lean_Elab_TacticInfo_format___closed__4 = _init_l_Lean_Elab_TacticInfo_format___closed__4();
lean_mark_persistent(l_Lean_Elab_TacticInfo_format___closed__4);
l_Lean_Elab_MacroExpansionInfo_format___closed__1 = _init_l_Lean_Elab_MacroExpansionInfo_format___closed__1();
lean_mark_persistent(l_Lean_Elab_MacroExpansionInfo_format___closed__1);
l_Lean_Elab_MacroExpansionInfo_format___closed__2 = _init_l_Lean_Elab_MacroExpansionInfo_format___closed__2();
lean_mark_persistent(l_Lean_Elab_MacroExpansionInfo_format___closed__2);
l_Lean_Elab_MacroExpansionInfo_format___closed__3 = _init_l_Lean_Elab_MacroExpansionInfo_format___closed__3();
lean_mark_persistent(l_Lean_Elab_MacroExpansionInfo_format___closed__3);
l_Lean_Elab_MacroExpansionInfo_format___closed__4 = _init_l_Lean_Elab_MacroExpansionInfo_format___closed__4();
lean_mark_persistent(l_Lean_Elab_MacroExpansionInfo_format___closed__4);
l_Lean_Elab_InfoTree_format___closed__1 = _init_l_Lean_Elab_InfoTree_format___closed__1();
lean_mark_persistent(l_Lean_Elab_InfoTree_format___closed__1);
l_Lean_Elab_InfoTree_format___closed__2 = _init_l_Lean_Elab_InfoTree_format___closed__2();
lean_mark_persistent(l_Lean_Elab_InfoTree_format___closed__2);
l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg___lambda__2___closed__1 = _init_l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___rarg___lambda__2___closed__1);
l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__1 = _init_l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__1);
l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__2 = _init_l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__2);
l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__3 = _init_l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__3);
l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__4 = _init_l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__4);
l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__5 = _init_l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_assignInfoHoleId___rarg___lambda__2___closed__5);
l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__1);
l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__2);
l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__3 = _init_l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__3);
l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__4 = _init_l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_withInfoHole___rarg___lambda__1___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
