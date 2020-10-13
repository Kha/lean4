// Lean compiler output
// Module: Lean.Elab.StructInst
// Imports: Init Lean.Util.FindExpr Lean.Elab.App Lean.Elab.Binders Lean.Elab.Quotation
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFields(lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(lean_object*);
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_12__mkFieldMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__2;
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource___closed__3;
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_List_tail_x21___rarg(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7;
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___at_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__4;
lean_object* l___private_Lean_Expr_4__getAppRevArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___boxed(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4;
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
uint8_t l_Lean_Elab_Term_StructInst_Struct_allDefault(lean_object*);
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__7___boxed(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Format_joinSep___main___at_Lean_Elab_Term_StructInst_formatField___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_3__isModifyOp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_StructInst_14__getFieldIdx___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__2;
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5;
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__8;
lean_object* l_Lean_Elab_Term_StructInst_Struct_hasToString;
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3;
extern lean_object* l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__1;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__19;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__20;
lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__5;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__4;
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(size_t, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault___main___boxed(lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__1;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__5;
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__2;
uint8_t l_List_foldr___main___at_Lean_Elab_Term_StructInst_Struct_allDefault___main___spec__1(uint8_t, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1;
lean_object* l___private_Lean_Elab_StructInst_16__mkSubstructSource___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref(lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType(lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_setFields(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__2;
lean_object* l_Std_HashMap_toList___rarg(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__4;
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__2;
lean_object* l_List_map___main___rarg(lean_object*, lean_object*);
lean_object* l_Nat_max(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3;
extern lean_object* l_Lean_formatKVMap___closed__1;
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_formatField(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_8__expandCompositeFields___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11;
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__1;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__6;
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(lean_object*);
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_List_head_x21___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12;
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
lean_object* l___private_Lean_Elab_StructInst_26__regTraceClasses(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7;
extern lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__9;
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1___boxed(lean_object**);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__26;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l___private_Lean_Elab_StructInst_21__getForallBody(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Source_inhabited;
lean_object* l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__18;
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__1;
lean_object* l_Lean_Environment_getProjectionStructureName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple___rarg___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__7(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_13__isSimpleField_x3f___boxed(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_15__mkProjStx(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_hasFormat(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Source_isNone___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_inhabited;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_defaultMissing_x3f___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__2;
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__4;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11___boxed(lean_object**);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__28;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__1;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___boxed(lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
lean_object* l_Lean_Format_joinSep___main___at___private_Lean_Data_Trie_6__toStringAux___main___spec__1(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
lean_object* l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__22;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1;
lean_object* l___private_Lean_Elab_StructInst_24__elabStruct___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__8;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields___boxed(lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(uint8_t, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_22__propagateExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3___boxed(lean_object*);
extern lean_object* l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__2;
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatEntry___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__6;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_inhabited(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_22__propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_type_lparams(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___at_Lean_Elab_Term_savingMCtx___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__6___boxed(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__2;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth(lean_object*);
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_12__mkFieldMap___closed__1;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1;
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3;
lean_object* l___private_Lean_Elab_StructInst_7__mkStructView(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__24;
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__15;
lean_object* l_Lean_Meta_synthInstance_x3f___at_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__4___boxed(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__1;
lean_object* l_Array_iterateMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_23__mkCtorHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__10;
lean_object* l___private_Lean_Elab_StructInst_5__getStructName(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2;
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2___closed__1;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__16;
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__1;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__3(lean_object*);
uint8_t l_Lean_Elab_Term_StructInst_Struct_allDefault___main(lean_object*);
lean_object* l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1;
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__5;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6;
lean_object* l_Lean_Elab_Term_StructInst_findField_x3f(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_defaultMissing_x3f(lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1(lean_object*, lean_object*);
extern lean_object* l_List_head_x21___rarg___closed__2;
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__3;
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
uint8_t l_Array_contains___at_Lean_findField_x3f___main___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7;
lean_object* l___private_Lean_Elab_StructInst_8__expandCompositeFields(lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_10__expandParentFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(lean_object*);
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault___boxed(lean_object*);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__18;
extern lean_object* l_Id_Monad;
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName___boxed(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5;
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_setStructSourceSyntax(lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_141____closed__4;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_mkSepStx(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
extern lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l_fix1___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1(lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__15;
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Array_umapMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_HasRepr___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_Field_hasToString;
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__2;
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__7;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3;
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1;
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__2(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3;
lean_object* lean_instantiate_value_lparams(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__1;
lean_object* l_Lean_mkHole(lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__4;
lean_object* l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__22;
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5;
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__1;
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_foldr___main___at_Lean_Elab_Term_StructInst_Struct_allDefault___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_Struct_source___boxed(lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__2;
extern lean_object* l_Lean_Format_sbracket___closed__4;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__14;
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1;
lean_object* l___private_Lean_Elab_StructInst_19__expandStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_16__mkSubstructSource(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__13;
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_530____closed__8;
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref___boxed(lean_object*);
lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__6(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__25;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__9(lean_object*);
lean_object* l_Lean_Elab_Term_isExprMVarAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureCtor(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_source(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_StructInst_14__getFieldIdx___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1;
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__7;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9;
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__6;
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PUnit_Inhabited;
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__5(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__2(lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__8;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
lean_object* l___private_Lean_Elab_StructInst_24__elabStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_Struct_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_StructInst_Source_isNone(lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__6;
lean_object* l_Lean_Elab_Term_StructInst_Struct_hasFormat;
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__21;
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__5;
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__2;
extern lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__14;
lean_object* l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__6;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__13;
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(lean_object*);
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__3;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__23;
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__1;
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__2(lean_object*);
extern lean_object* l___private_Lean_Elab_Term_5__tryCoe___closed__3;
extern lean_object* l_Lean_Meta_CheckAssignment_checkFVar___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1;
lean_object* l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__3;
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__1;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8;
lean_object* l_Lean_Elab_Term_StructInst_Field_hasFormat;
extern lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_6__toFieldLHS(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField(lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__4;
lean_object* l_ReaderT_inhabited___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2;
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__8;
lean_object* l___private_Lean_Elab_StructInst_19__expandStruct___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3;
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_23__mkCtorHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2;
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9;
lean_object* l___private_Lean_Elab_StructInst_21__getForallBody___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5;
lean_object* l_Lean_findField_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___boxed(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource___closed__2;
extern lean_object* l_addParenHeuristic___closed__1;
lean_object* l___private_Lean_Elab_StructInst_3__isModifyOp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_findSome_x3f___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
extern lean_object* l___private_Lean_Elab_Util_6__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___boxed(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__27;
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_13__isSimpleField_x3f(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_isNone(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_5, x_7);
lean_dec(x_5);
x_9 = l_Lean_mkOptionalNode___closed__1;
x_10 = l_Lean_Syntax_setArg(x_1, x_4, x_9);
x_11 = l_Array_empty___closed__1;
x_12 = lean_array_push(x_11, x_10);
x_13 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__22;
x_14 = lean_array_push(x_13, x_8);
x_15 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__8;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_array_push(x_11, x_16);
x_18 = l_Lean_nullKind___closed__2;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_array_push(x_12, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__6;
x_23 = lean_array_push(x_22, x_21);
x_24 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__15;
x_25 = lean_array_push(x_23, x_24);
x_26 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_5);
lean_dec(x_1);
x_29 = lean_box(1);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
return x_30;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("src");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_250; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_isNone(x_10);
x_250 = lean_st_ref_take(x_7, x_8);
if (x_11 == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = 0;
x_12 = x_253;
x_13 = x_251;
x_14 = x_252;
goto block_249;
}
else
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_254 = lean_ctor_get(x_250, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_250, 1);
lean_inc(x_255);
lean_dec(x_250);
x_256 = 1;
x_12 = x_256;
x_13 = x_254;
x_14 = x_255;
goto block_249;
}
block_249:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_nat_add(x_16, x_9);
lean_ctor_set(x_13, 1, x_17);
x_18 = lean_st_ref_set(x_7, x_13, x_14);
if (x_12 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_2, 7);
lean_dec(x_21);
lean_ctor_set(x_2, 7, x_16);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_10, x_22);
lean_inc(x_4);
lean_inc(x_23);
x_24 = l_Lean_Elab_Term_isLocalIdent_x3f(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4;
x_34 = l_Lean_addMacroScope(x_31, x_33, x_28);
x_35 = lean_box(0);
x_36 = l_Lean_SourceInfo_inhabited___closed__1;
x_37 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3;
x_38 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_35);
x_39 = l_Lean_Syntax_setArg(x_10, x_22, x_38);
x_40 = l_Lean_Syntax_setArg(x_1, x_9, x_39);
x_41 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_32);
lean_dec(x_4);
lean_dec(x_2);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_43);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = l_Lean_addMacroScope(x_46, x_33, x_42);
x_48 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_37);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_35);
x_49 = l_Array_empty___closed__1;
x_50 = lean_array_push(x_49, x_48);
x_51 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
x_52 = lean_array_push(x_50, x_51);
x_53 = lean_array_push(x_52, x_51);
x_54 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__20;
x_55 = lean_array_push(x_53, x_54);
x_56 = lean_array_push(x_55, x_23);
x_57 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__8;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_array_push(x_49, x_58);
x_60 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__6;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__4;
x_63 = lean_array_push(x_62, x_61);
x_64 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__18;
x_65 = lean_array_push(x_63, x_64);
x_66 = lean_array_push(x_65, x_40);
x_67 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__2;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_44, 0, x_69);
return x_44;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_70 = lean_ctor_get(x_44, 0);
x_71 = lean_ctor_get(x_44, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_44);
x_72 = l_Lean_addMacroScope(x_70, x_33, x_42);
x_73 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_73, 0, x_36);
lean_ctor_set(x_73, 1, x_37);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_35);
x_74 = l_Array_empty___closed__1;
x_75 = lean_array_push(x_74, x_73);
x_76 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
x_77 = lean_array_push(x_75, x_76);
x_78 = lean_array_push(x_77, x_76);
x_79 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__20;
x_80 = lean_array_push(x_78, x_79);
x_81 = lean_array_push(x_80, x_23);
x_82 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__8;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_array_push(x_74, x_83);
x_85 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__6;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__4;
x_88 = lean_array_push(x_87, x_86);
x_89 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__18;
x_90 = lean_array_push(x_88, x_89);
x_91 = lean_array_push(x_90, x_40);
x_92 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__2;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_71);
return x_95;
}
}
else
{
uint8_t x_96; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_2);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_24);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_24, 0);
lean_dec(x_97);
x_98 = lean_box(0);
lean_ctor_set(x_24, 0, x_98);
return x_24;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_24, 1);
lean_inc(x_99);
lean_dec(x_24);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_102 = lean_ctor_get(x_2, 0);
x_103 = lean_ctor_get(x_2, 1);
x_104 = lean_ctor_get(x_2, 2);
x_105 = lean_ctor_get(x_2, 3);
x_106 = lean_ctor_get(x_2, 4);
x_107 = lean_ctor_get(x_2, 5);
x_108 = lean_ctor_get(x_2, 6);
x_109 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
x_110 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 1);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_2);
x_111 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_111, 0, x_102);
lean_ctor_set(x_111, 1, x_103);
lean_ctor_set(x_111, 2, x_104);
lean_ctor_set(x_111, 3, x_105);
lean_ctor_set(x_111, 4, x_106);
lean_ctor_set(x_111, 5, x_107);
lean_ctor_set(x_111, 6, x_108);
lean_ctor_set(x_111, 7, x_16);
lean_ctor_set_uint8(x_111, sizeof(void*)*8, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*8 + 1, x_110);
x_112 = lean_unsigned_to_nat(0u);
x_113 = l_Lean_Syntax_getArg(x_10, x_112);
lean_inc(x_4);
lean_inc(x_113);
x_114 = l_Lean_Elab_Term_isLocalIdent_x3f(x_113, x_111, x_3, x_4, x_5, x_6, x_7, x_19);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l_Lean_Elab_Term_getCurrMacroScope(x_111, x_3, x_4, x_5, x_6, x_7, x_116);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4;
x_124 = l_Lean_addMacroScope(x_121, x_123, x_118);
x_125 = lean_box(0);
x_126 = l_Lean_SourceInfo_inhabited___closed__1;
x_127 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3;
x_128 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_128, 2, x_124);
lean_ctor_set(x_128, 3, x_125);
x_129 = l_Lean_Syntax_setArg(x_10, x_112, x_128);
x_130 = l_Lean_Syntax_setArg(x_1, x_9, x_129);
x_131 = l_Lean_Elab_Term_getCurrMacroScope(x_111, x_3, x_4, x_5, x_6, x_7, x_122);
lean_dec(x_4);
lean_dec(x_111);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
x_138 = l_Lean_addMacroScope(x_135, x_123, x_132);
x_139 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_139, 0, x_126);
lean_ctor_set(x_139, 1, x_127);
lean_ctor_set(x_139, 2, x_138);
lean_ctor_set(x_139, 3, x_125);
x_140 = l_Array_empty___closed__1;
x_141 = lean_array_push(x_140, x_139);
x_142 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
x_143 = lean_array_push(x_141, x_142);
x_144 = lean_array_push(x_143, x_142);
x_145 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__20;
x_146 = lean_array_push(x_144, x_145);
x_147 = lean_array_push(x_146, x_113);
x_148 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__8;
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
x_150 = lean_array_push(x_140, x_149);
x_151 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__6;
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__4;
x_154 = lean_array_push(x_153, x_152);
x_155 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__18;
x_156 = lean_array_push(x_154, x_155);
x_157 = lean_array_push(x_156, x_130);
x_158 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__2;
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_159);
if (lean_is_scalar(x_137)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_137;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_136);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_162 = lean_ctor_get(x_114, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_163 = x_114;
} else {
 lean_dec_ref(x_114);
 x_163 = lean_box(0);
}
x_164 = lean_box(0);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_162);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_18);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_18, 0);
lean_dec(x_167);
x_168 = lean_box(0);
lean_ctor_set(x_18, 0, x_168);
return x_18;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_18, 1);
lean_inc(x_169);
lean_dec(x_18);
x_170 = lean_box(0);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_172 = lean_ctor_get(x_13, 0);
x_173 = lean_ctor_get(x_13, 1);
x_174 = lean_ctor_get(x_13, 2);
x_175 = lean_ctor_get(x_13, 3);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_13);
x_176 = lean_nat_add(x_173, x_9);
x_177 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_177, 0, x_172);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set(x_177, 2, x_174);
lean_ctor_set(x_177, 3, x_175);
x_178 = lean_st_ref_set(x_7, x_177, x_14);
if (x_12 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_180 = lean_ctor_get(x_2, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_2, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_2, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_2, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_2, 4);
lean_inc(x_184);
x_185 = lean_ctor_get(x_2, 5);
lean_inc(x_185);
x_186 = lean_ctor_get(x_2, 6);
lean_inc(x_186);
x_187 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
x_188 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 1);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 x_189 = x_2;
} else {
 lean_dec_ref(x_2);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 8, 2);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_180);
lean_ctor_set(x_190, 1, x_181);
lean_ctor_set(x_190, 2, x_182);
lean_ctor_set(x_190, 3, x_183);
lean_ctor_set(x_190, 4, x_184);
lean_ctor_set(x_190, 5, x_185);
lean_ctor_set(x_190, 6, x_186);
lean_ctor_set(x_190, 7, x_173);
lean_ctor_set_uint8(x_190, sizeof(void*)*8, x_187);
lean_ctor_set_uint8(x_190, sizeof(void*)*8 + 1, x_188);
x_191 = lean_unsigned_to_nat(0u);
x_192 = l_Lean_Syntax_getArg(x_10, x_191);
lean_inc(x_4);
lean_inc(x_192);
x_193 = l_Lean_Elab_Term_isLocalIdent_x3f(x_192, x_190, x_3, x_4, x_5, x_6, x_7, x_179);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l_Lean_Elab_Term_getCurrMacroScope(x_190, x_3, x_4, x_5, x_6, x_7, x_195);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4;
x_203 = l_Lean_addMacroScope(x_200, x_202, x_197);
x_204 = lean_box(0);
x_205 = l_Lean_SourceInfo_inhabited___closed__1;
x_206 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3;
x_207 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
lean_ctor_set(x_207, 2, x_203);
lean_ctor_set(x_207, 3, x_204);
x_208 = l_Lean_Syntax_setArg(x_10, x_191, x_207);
x_209 = l_Lean_Syntax_setArg(x_1, x_9, x_208);
x_210 = l_Lean_Elab_Term_getCurrMacroScope(x_190, x_3, x_4, x_5, x_6, x_7, x_201);
lean_dec(x_4);
lean_dec(x_190);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_212);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_216 = x_213;
} else {
 lean_dec_ref(x_213);
 x_216 = lean_box(0);
}
x_217 = l_Lean_addMacroScope(x_214, x_202, x_211);
x_218 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_218, 0, x_205);
lean_ctor_set(x_218, 1, x_206);
lean_ctor_set(x_218, 2, x_217);
lean_ctor_set(x_218, 3, x_204);
x_219 = l_Array_empty___closed__1;
x_220 = lean_array_push(x_219, x_218);
x_221 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
x_222 = lean_array_push(x_220, x_221);
x_223 = lean_array_push(x_222, x_221);
x_224 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__20;
x_225 = lean_array_push(x_223, x_224);
x_226 = lean_array_push(x_225, x_192);
x_227 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__8;
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
x_229 = lean_array_push(x_219, x_228);
x_230 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__6;
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_229);
x_232 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__4;
x_233 = lean_array_push(x_232, x_231);
x_234 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__18;
x_235 = lean_array_push(x_233, x_234);
x_236 = lean_array_push(x_235, x_209);
x_237 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__2;
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_238);
if (lean_is_scalar(x_216)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_216;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_215);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_190);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_241 = lean_ctor_get(x_193, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_242 = x_193;
} else {
 lean_dec_ref(x_193);
 x_242 = lean_box(0);
}
x_243 = lean_box(0);
if (lean_is_scalar(x_242)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_242;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_241);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_173);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_245 = lean_ctor_get(x_178, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_246 = x_178;
} else {
 lean_dec_ref(x_178);
 x_246 = lean_box(0);
}
x_247 = lean_box(0);
if (lean_is_scalar(x_246)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_246;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_245);
return x_248;
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Source_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
uint8_t l_Lean_Elab_Term_StructInst_Source_isNone(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_Source_isNone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_Source_isNone(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_setStructSourceSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_mkOptionalNode___closed__1;
x_5 = l_Lean_Syntax_setArg(x_1, x_3, x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = l_Lean_Syntax_setArg(x_5, x_6, x_4);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_mkOptionalNode___closed__1;
x_11 = l_Lean_Syntax_setArg(x_1, x_9, x_10);
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Syntax_setArg(x_11, x_12, x_8);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_setArg(x_1, x_15, x_14);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_mkOptionalNode___closed__1;
x_19 = l_Lean_Syntax_setArg(x_16, x_17, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_2__getStructSource___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid structure instance `with` and `..` cannot be used together");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_2__getStructSource___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_2__getStructSource___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_2__getStructSource___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_2__getStructSource___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isNone(x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_6, 3);
x_16 = l_Lean_replaceRef(x_1, x_15);
x_17 = l_Lean_replaceRef(x_16, x_15);
lean_dec(x_16);
x_18 = l_Lean_replaceRef(x_17, x_15);
lean_dec(x_15);
lean_dec(x_17);
lean_ctor_set(x_6, 3, x_18);
x_19 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
x_20 = l___private_Lean_Elab_StructInst_2__getStructSource___closed__3;
x_21 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_10, x_22);
lean_inc(x_4);
x_24 = l_Lean_Elab_Term_isLocalIdent_x3f(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_apply_7(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_26);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_24, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_24, 0, x_33);
return x_24;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_10);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_38 = lean_ctor_get(x_6, 0);
x_39 = lean_ctor_get(x_6, 1);
x_40 = lean_ctor_get(x_6, 2);
x_41 = lean_ctor_get(x_6, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_6);
x_42 = l_Lean_replaceRef(x_1, x_41);
x_43 = l_Lean_replaceRef(x_42, x_41);
lean_dec(x_42);
x_44 = l_Lean_replaceRef(x_43, x_41);
lean_dec(x_41);
lean_dec(x_43);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_39);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set(x_45, 3, x_44);
x_46 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_10);
x_47 = l___private_Lean_Elab_StructInst_2__getStructSource___closed__3;
x_48 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_47, x_2, x_3, x_4, x_5, x_45, x_7, x_8);
lean_dec(x_7);
lean_dec(x_45);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Lean_Syntax_getArg(x_10, x_49);
lean_inc(x_4);
x_51 = l_Lean_Elab_Term_isLocalIdent_x3f(x_50, x_2, x_3, x_4, x_5, x_45, x_7, x_8);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_10);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_55 = l_unreachable_x21___rarg(x_54);
x_56 = lean_apply_7(x_55, x_2, x_3, x_4, x_5, x_45, x_7, x_53);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_45);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_58 = x_51;
} else {
 lean_dec_ref(x_51);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_10);
lean_ctor_set(x_60, 1, x_59);
if (lean_is_scalar(x_58)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_58;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = l_Lean_Syntax_isNone(x_12);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_12);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_8);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_12);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_8);
return x_66;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_StructInst_2__getStructSource(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structInstArrayRef");
return x_1;
}
}
static lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, can't mix field and `[..]` at a given level");
return x_1;
}
}
static lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, at most one `[..]` at a given level");
return x_1;
}
}
static lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_array_fget(x_2, x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_15, x_16);
x_18 = l_Lean_Syntax_getKind(x_17);
x_19 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2;
x_20 = lean_name_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_15);
x_22 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_22;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
x_25 = l_Lean_Syntax_getKind(x_24);
x_26 = lean_name_eq(x_25, x_19);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_15);
x_27 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_4);
lean_dec(x_3);
x_29 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5;
x_30 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_15, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_15);
x_36 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_36;
x_4 = x_35;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_3);
x_38 = lean_ctor_get(x_4, 0);
lean_inc(x_38);
lean_dec(x_4);
x_39 = l_Lean_Syntax_getKind(x_38);
x_40 = lean_name_eq(x_39, x_19);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5;
x_42 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_15, x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
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
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__8;
x_48 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_15, x_47, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
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
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_3__isModifyOp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1(x_9, x_11, x_13, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_14, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
x_23 = l_Lean_Syntax_getArg(x_22, x_13);
lean_dec(x_22);
x_24 = l_Lean_Syntax_getKind(x_23);
x_25 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2;
x_26 = lean_name_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
return x_14;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
x_29 = l_Lean_Syntax_getArg(x_28, x_13);
lean_dec(x_28);
x_30 = l_Lean_Syntax_getKind(x_29);
x_31 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2;
x_32 = lean_name_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_15);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
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
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_StructInst_3__isModifyOp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_StructInst_3__isModifyOp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("struct");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_6__regTraceClasses___closed__1;
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("modifyOp");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2;
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("s");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_141____closed__4;
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__15;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n===>\n");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__18;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nval: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__21;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nSource: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__25;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__26;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_303 = lean_ctor_get(x_9, 0);
lean_inc(x_303);
x_304 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
x_305 = l_Lean_checkTraceOption(x_303, x_304);
lean_dec(x_303);
if (x_305 == 0)
{
x_12 = x_11;
goto block_302;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_inc(x_2);
x_306 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_306, 0, x_2);
x_307 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__27;
x_308 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
lean_inc(x_3);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_3);
x_310 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
x_311 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_304, x_310, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
lean_dec(x_311);
x_12 = x_312;
goto block_302;
}
block_302:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = l_Lean_Syntax_isNone(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_16 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8;
x_23 = l_Lean_addMacroScope(x_20, x_22, x_17);
x_24 = lean_box(0);
x_25 = l_Lean_SourceInfo_inhabited___closed__1;
x_26 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7;
x_27 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_24);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_Syntax_getArg(x_14, x_28);
lean_inc(x_29);
x_30 = l_Lean_Syntax_getKind(x_29);
x_31 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2;
x_32 = lean_name_eq(x_30, x_31);
lean_dec(x_30);
x_33 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_34 = lean_array_get_size(x_33);
x_35 = l_Array_extract___rarg(x_33, x_13, x_34);
x_36 = l_Lean_nullKind;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_ctor_get(x_9, 0);
lean_inc(x_38);
x_39 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
x_40 = l_Lean_checkTraceOption(x_38, x_39);
lean_dec(x_38);
if (x_32 == 0)
{
lean_object* x_181; 
x_181 = l_Lean_Syntax_getArg(x_29, x_13);
lean_dec(x_29);
x_41 = x_181;
goto block_180;
}
else
{
x_41 = x_29;
goto block_180;
}
block_180:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_inc(x_2);
x_42 = l_Lean_Syntax_setArg(x_2, x_28, x_41);
x_43 = l_Lean_Syntax_setArg(x_42, x_13, x_37);
x_44 = l_Lean_mkOptionalNode___closed__2;
x_45 = lean_array_push(x_44, x_43);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_171 = lean_ctor_get(x_3, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_3, 1);
lean_inc(x_172);
x_173 = lean_array_get_size(x_172);
x_174 = lean_nat_dec_lt(x_28, x_173);
lean_dec(x_173);
if (x_174 == 0)
{
lean_object* x_175; 
lean_dec(x_27);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_172);
x_47 = x_175;
goto block_170;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_box(0);
x_177 = lean_array_fset(x_172, x_28, x_176);
x_178 = lean_array_fset(x_177, x_28, x_27);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_171);
lean_ctor_set(x_179, 1, x_178);
x_47 = x_179;
goto block_170;
}
}
else
{
lean_dec(x_27);
lean_inc(x_3);
x_47 = x_3;
goto block_170;
}
block_170:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_inc(x_1);
x_48 = l_Lean_Syntax_setArg(x_1, x_13, x_47);
x_49 = lean_unsigned_to_nat(2u);
x_50 = l_Lean_Syntax_setArg(x_48, x_49, x_46);
if (x_40 == 0)
{
x_51 = x_21;
goto block_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_inc(x_1);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_1);
x_164 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__22;
x_165 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
lean_inc(x_50);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_50);
x_167 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_39, x_167, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_51 = x_169;
goto block_162;
}
block_162:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_52 = l_Lean_Syntax_getArg(x_2, x_28);
lean_dec(x_2);
x_53 = l_Lean_Syntax_getArg(x_52, x_13);
lean_dec(x_52);
x_54 = l_Lean_Syntax_getArg(x_3, x_28);
lean_dec(x_3);
x_55 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_51);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Array_empty___closed__1;
x_62 = lean_array_push(x_61, x_54);
x_63 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__14;
x_64 = lean_array_push(x_62, x_63);
x_65 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11;
lean_inc(x_56);
lean_inc(x_59);
x_66 = l_Lean_addMacroScope(x_59, x_65, x_56);
x_67 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__10;
x_68 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__14;
x_69 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_69, 0, x_25);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_68);
x_70 = lean_array_push(x_64, x_69);
x_71 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__9;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_array_push(x_61, x_72);
x_74 = l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__2;
lean_inc(x_56);
lean_inc(x_59);
x_75 = l_Lean_addMacroScope(x_59, x_74, x_56);
x_76 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__16;
x_77 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_77, 0, x_25);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_24);
x_78 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__6;
x_79 = lean_array_push(x_78, x_77);
x_80 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__20;
x_81 = lean_array_push(x_79, x_80);
x_82 = lean_array_push(x_81, x_53);
x_83 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__15;
x_84 = lean_array_push(x_82, x_83);
x_85 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = lean_array_push(x_61, x_86);
x_88 = l_Lean_addMacroScope(x_59, x_22, x_56);
x_89 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_89, 0, x_25);
lean_ctor_set(x_89, 1, x_26);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_24);
x_90 = lean_array_push(x_61, x_89);
x_91 = l_Lean_nullKind___closed__2;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_94 = lean_array_push(x_93, x_92);
x_95 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_96 = lean_array_push(x_94, x_95);
x_97 = lean_array_push(x_96, x_50);
x_98 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_array_push(x_61, x_99);
x_101 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
x_102 = lean_array_push(x_100, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_91);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_array_push(x_78, x_103);
x_105 = lean_array_push(x_104, x_83);
x_106 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_array_push(x_87, x_107);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_91);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_array_push(x_73, x_109);
x_111 = l_Lean_mkAppStx___closed__8;
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
if (x_40 == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_5);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_5, 6);
lean_inc(x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_1);
lean_ctor_set(x_115, 1, x_112);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
lean_ctor_set(x_5, 6, x_116);
x_117 = 1;
x_118 = l_Lean_Elab_Term_elabTerm(x_112, x_4, x_117, x_5, x_6, x_7, x_8, x_9, x_10, x_60);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_119 = lean_ctor_get(x_5, 0);
x_120 = lean_ctor_get(x_5, 1);
x_121 = lean_ctor_get(x_5, 2);
x_122 = lean_ctor_get(x_5, 3);
x_123 = lean_ctor_get(x_5, 4);
x_124 = lean_ctor_get(x_5, 5);
x_125 = lean_ctor_get(x_5, 6);
x_126 = lean_ctor_get(x_5, 7);
x_127 = lean_ctor_get_uint8(x_5, sizeof(void*)*8);
x_128 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 1);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_5);
lean_inc(x_112);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_1);
lean_ctor_set(x_129, 1, x_112);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_125);
x_131 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_131, 0, x_119);
lean_ctor_set(x_131, 1, x_120);
lean_ctor_set(x_131, 2, x_121);
lean_ctor_set(x_131, 3, x_122);
lean_ctor_set(x_131, 4, x_123);
lean_ctor_set(x_131, 5, x_124);
lean_ctor_set(x_131, 6, x_130);
lean_ctor_set(x_131, 7, x_126);
lean_ctor_set_uint8(x_131, sizeof(void*)*8, x_127);
lean_ctor_set_uint8(x_131, sizeof(void*)*8 + 1, x_128);
x_132 = 1;
x_133 = l_Lean_Elab_Term_elabTerm(x_112, x_4, x_132, x_131, x_6, x_7, x_8, x_9, x_10, x_60);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
lean_inc(x_1);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_1);
x_135 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__19;
x_136 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
lean_inc(x_112);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_112);
x_138 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_39, x_138, x_5, x_6, x_7, x_8, x_9, x_10, x_60);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = !lean_is_exclusive(x_5);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_5, 6);
lean_inc(x_112);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_1);
lean_ctor_set(x_143, 1, x_112);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
lean_ctor_set(x_5, 6, x_144);
x_145 = 1;
x_146 = l_Lean_Elab_Term_elabTerm(x_112, x_4, x_145, x_5, x_6, x_7, x_8, x_9, x_10, x_140);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; 
x_147 = lean_ctor_get(x_5, 0);
x_148 = lean_ctor_get(x_5, 1);
x_149 = lean_ctor_get(x_5, 2);
x_150 = lean_ctor_get(x_5, 3);
x_151 = lean_ctor_get(x_5, 4);
x_152 = lean_ctor_get(x_5, 5);
x_153 = lean_ctor_get(x_5, 6);
x_154 = lean_ctor_get(x_5, 7);
x_155 = lean_ctor_get_uint8(x_5, sizeof(void*)*8);
x_156 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 1);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_5);
lean_inc(x_112);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_1);
lean_ctor_set(x_157, 1, x_112);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_153);
x_159 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_159, 0, x_147);
lean_ctor_set(x_159, 1, x_148);
lean_ctor_set(x_159, 2, x_149);
lean_ctor_set(x_159, 3, x_150);
lean_ctor_set(x_159, 4, x_151);
lean_ctor_set(x_159, 5, x_152);
lean_ctor_set(x_159, 6, x_158);
lean_ctor_set(x_159, 7, x_154);
lean_ctor_set_uint8(x_159, sizeof(void*)*8, x_155);
lean_ctor_set_uint8(x_159, sizeof(void*)*8 + 1, x_156);
x_160 = 1;
x_161 = l_Lean_Elab_Term_elabTerm(x_112, x_4, x_160, x_159, x_6, x_7, x_8, x_9, x_10, x_140);
return x_161;
}
}
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
lean_dec(x_14);
x_182 = lean_unsigned_to_nat(3u);
x_183 = l_Lean_Syntax_getArg(x_2, x_182);
x_184 = lean_unsigned_to_nat(0u);
x_185 = l_Lean_Syntax_getArg(x_2, x_184);
lean_dec(x_2);
x_186 = l_Lean_Syntax_getArg(x_185, x_13);
lean_dec(x_185);
x_187 = l_Lean_Syntax_getArg(x_3, x_184);
lean_dec(x_3);
x_188 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_12);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = l_Array_empty___closed__1;
x_195 = lean_array_push(x_194, x_187);
x_196 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__14;
x_197 = lean_array_push(x_195, x_196);
x_198 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11;
lean_inc(x_189);
lean_inc(x_192);
x_199 = l_Lean_addMacroScope(x_192, x_198, x_189);
x_200 = lean_box(0);
x_201 = l_Lean_SourceInfo_inhabited___closed__1;
x_202 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__10;
x_203 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__24;
x_204 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
lean_ctor_set(x_204, 2, x_199);
lean_ctor_set(x_204, 3, x_203);
x_205 = lean_array_push(x_197, x_204);
x_206 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__9;
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
x_208 = lean_array_push(x_194, x_207);
x_209 = l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__2;
lean_inc(x_189);
lean_inc(x_192);
x_210 = l_Lean_addMacroScope(x_192, x_209, x_189);
x_211 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__16;
x_212 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_212, 0, x_201);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set(x_212, 2, x_210);
lean_ctor_set(x_212, 3, x_200);
x_213 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__6;
x_214 = lean_array_push(x_213, x_212);
x_215 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__20;
x_216 = lean_array_push(x_214, x_215);
x_217 = lean_array_push(x_216, x_186);
x_218 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__15;
x_219 = lean_array_push(x_217, x_218);
x_220 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
x_222 = lean_array_push(x_194, x_221);
x_223 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8;
x_224 = l_Lean_addMacroScope(x_192, x_223, x_189);
x_225 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7;
x_226 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_226, 0, x_201);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set(x_226, 2, x_224);
lean_ctor_set(x_226, 3, x_200);
x_227 = lean_array_push(x_194, x_226);
x_228 = l_Lean_nullKind___closed__2;
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
x_230 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__9;
x_231 = lean_array_push(x_230, x_229);
x_232 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__17;
x_233 = lean_array_push(x_231, x_232);
x_234 = lean_array_push(x_233, x_183);
x_235 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__7;
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_234);
x_237 = lean_array_push(x_194, x_236);
x_238 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
x_239 = lean_array_push(x_237, x_238);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_228);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_array_push(x_213, x_240);
x_242 = lean_array_push(x_241, x_218);
x_243 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_242);
x_245 = lean_array_push(x_222, x_244);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_228);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_array_push(x_208, x_246);
x_248 = l_Lean_mkAppStx___closed__8;
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = lean_ctor_get(x_9, 0);
lean_inc(x_250);
x_251 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
x_252 = l_Lean_checkTraceOption(x_250, x_251);
lean_dec(x_250);
if (x_252 == 0)
{
uint8_t x_253; 
x_253 = !lean_is_exclusive(x_5);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; 
x_254 = lean_ctor_get(x_5, 6);
lean_inc(x_249);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_1);
lean_ctor_set(x_255, 1, x_249);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_254);
lean_ctor_set(x_5, 6, x_256);
x_257 = 1;
x_258 = l_Lean_Elab_Term_elabTerm(x_249, x_4, x_257, x_5, x_6, x_7, x_8, x_9, x_10, x_193);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; 
x_259 = lean_ctor_get(x_5, 0);
x_260 = lean_ctor_get(x_5, 1);
x_261 = lean_ctor_get(x_5, 2);
x_262 = lean_ctor_get(x_5, 3);
x_263 = lean_ctor_get(x_5, 4);
x_264 = lean_ctor_get(x_5, 5);
x_265 = lean_ctor_get(x_5, 6);
x_266 = lean_ctor_get(x_5, 7);
x_267 = lean_ctor_get_uint8(x_5, sizeof(void*)*8);
x_268 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 1);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_5);
lean_inc(x_249);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_1);
lean_ctor_set(x_269, 1, x_249);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_265);
x_271 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_271, 0, x_259);
lean_ctor_set(x_271, 1, x_260);
lean_ctor_set(x_271, 2, x_261);
lean_ctor_set(x_271, 3, x_262);
lean_ctor_set(x_271, 4, x_263);
lean_ctor_set(x_271, 5, x_264);
lean_ctor_set(x_271, 6, x_270);
lean_ctor_set(x_271, 7, x_266);
lean_ctor_set_uint8(x_271, sizeof(void*)*8, x_267);
lean_ctor_set_uint8(x_271, sizeof(void*)*8 + 1, x_268);
x_272 = 1;
x_273 = l_Lean_Elab_Term_elabTerm(x_249, x_4, x_272, x_271, x_6, x_7, x_8, x_9, x_10, x_193);
return x_273;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
lean_inc(x_1);
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_1);
x_275 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__19;
x_276 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
lean_inc(x_249);
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_249);
x_278 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
x_279 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_251, x_278, x_5, x_6, x_7, x_8, x_9, x_10, x_193);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec(x_279);
x_281 = !lean_is_exclusive(x_5);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; 
x_282 = lean_ctor_get(x_5, 6);
lean_inc(x_249);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_1);
lean_ctor_set(x_283, 1, x_249);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_282);
lean_ctor_set(x_5, 6, x_284);
x_285 = 1;
x_286 = l_Lean_Elab_Term_elabTerm(x_249, x_4, x_285, x_5, x_6, x_7, x_8, x_9, x_10, x_280);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; uint8_t x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; lean_object* x_301; 
x_287 = lean_ctor_get(x_5, 0);
x_288 = lean_ctor_get(x_5, 1);
x_289 = lean_ctor_get(x_5, 2);
x_290 = lean_ctor_get(x_5, 3);
x_291 = lean_ctor_get(x_5, 4);
x_292 = lean_ctor_get(x_5, 5);
x_293 = lean_ctor_get(x_5, 6);
x_294 = lean_ctor_get(x_5, 7);
x_295 = lean_ctor_get_uint8(x_5, sizeof(void*)*8);
x_296 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 1);
lean_inc(x_294);
lean_inc(x_293);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_5);
lean_inc(x_249);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_1);
lean_ctor_set(x_297, 1, x_249);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_293);
x_299 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_299, 0, x_287);
lean_ctor_set(x_299, 1, x_288);
lean_ctor_set(x_299, 2, x_289);
lean_ctor_set(x_299, 3, x_290);
lean_ctor_set(x_299, 4, x_291);
lean_ctor_set(x_299, 5, x_292);
lean_ctor_set(x_299, 6, x_298);
lean_ctor_set(x_299, 7, x_294);
lean_ctor_set_uint8(x_299, sizeof(void*)*8, x_295);
lean_ctor_set_uint8(x_299, sizeof(void*)*8 + 1, x_296);
x_300 = 1;
x_301 = l_Lean_Elab_Term_elabTerm(x_249, x_4, x_300, x_299, x_6, x_7, x_8, x_9, x_10, x_280);
return x_301;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, expected type must be known");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, expected type is not of the form (C ...)");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, source type is not of the form (C ...)");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_26);
x_28 = l_Lean_Elab_Term_tryPostponeIfMVar(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_38; 
x_30 = lean_ctor_get(x_28, 1);
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_38 = l_Lean_Expr_getAppFn___main(x_26);
if (lean_obj_tag(x_38) == 4)
{
lean_object* x_39; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
lean_ctor_set(x_28, 0, x_39);
return x_28;
}
else
{
lean_object* x_40; 
lean_dec(x_38);
lean_free_object(x_28);
x_40 = lean_box(0);
x_32 = x_40;
goto block_37;
}
block_37:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
x_33 = l_Lean_indentExpr(x_26);
x_34 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_36;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_48; 
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_dec(x_28);
x_48 = l_Lean_Expr_getAppFn___main(x_26);
if (lean_obj_tag(x_48) == 4)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_48);
x_51 = lean_box(0);
x_42 = x_51;
goto block_47;
}
block_47:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
x_43 = l_Lean_indentExpr(x_26);
x_44 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_46;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_28);
if (x_52 == 0)
{
return x_28;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_28, 0);
x_54 = lean_ctor_get(x_28, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_28);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_25);
if (x_56 == 0)
{
return x_25;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_25, 0);
x_58 = lean_ctor_get(x_25, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_25);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_22);
if (x_60 == 0)
{
return x_22;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_22, 0);
x_62 = lean_ctor_get(x_22, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_22);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_2);
x_64 = lean_box(0);
x_12 = x_64;
goto block_20;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_65);
x_66 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_76; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
x_76 = l_Lean_Expr_getAppFn___main(x_68);
lean_dec(x_68);
switch (lean_obj_tag(x_76)) {
case 0:
{
lean_dec(x_76);
lean_free_object(x_66);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_65);
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_78 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_77, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_81 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_82);
x_84 = l_Lean_Elab_Term_tryPostponeIfMVar(x_82, x_3, x_4, x_5, x_6, x_7, x_8, x_83);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_94; 
x_86 = lean_ctor_get(x_84, 1);
x_87 = lean_ctor_get(x_84, 0);
lean_dec(x_87);
x_94 = l_Lean_Expr_getAppFn___main(x_82);
if (lean_obj_tag(x_94) == 4)
{
lean_object* x_95; 
lean_dec(x_82);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec(x_94);
lean_ctor_set(x_84, 0, x_95);
return x_84;
}
else
{
lean_object* x_96; 
lean_dec(x_94);
lean_free_object(x_84);
x_96 = lean_box(0);
x_88 = x_96;
goto block_93;
}
block_93:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_88);
x_89 = l_Lean_indentExpr(x_82);
x_90 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_91 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_91, x_3, x_4, x_5, x_6, x_7, x_8, x_86);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_92;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_104; 
x_97 = lean_ctor_get(x_84, 1);
lean_inc(x_97);
lean_dec(x_84);
x_104 = l_Lean_Expr_getAppFn___main(x_82);
if (lean_obj_tag(x_104) == 4)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_82);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_97);
return x_106;
}
else
{
lean_object* x_107; 
lean_dec(x_104);
x_107 = lean_box(0);
x_98 = x_107;
goto block_103;
}
block_103:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_98);
x_99 = l_Lean_indentExpr(x_82);
x_100 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_101, x_3, x_4, x_5, x_6, x_7, x_8, x_97);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_102;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_82);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_108 = !lean_is_exclusive(x_84);
if (x_108 == 0)
{
return x_84;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_84, 0);
x_110 = lean_ctor_get(x_84, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_84);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_81);
if (x_112 == 0)
{
return x_81;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_81, 0);
x_114 = lean_ctor_get(x_81, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_81);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_116 = !lean_is_exclusive(x_78);
if (x_116 == 0)
{
return x_78;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_78, 0);
x_118 = lean_ctor_get(x_78, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_78);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_2);
x_120 = lean_box(0);
x_70 = x_120;
goto block_75;
}
}
case 1:
{
lean_dec(x_76);
lean_free_object(x_66);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_65);
x_121 = lean_ctor_get(x_2, 1);
lean_inc(x_121);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_122 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_121, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_125 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_123, x_3, x_4, x_5, x_6, x_7, x_8, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
lean_inc(x_126);
x_128 = l_Lean_Elab_Term_tryPostponeIfMVar(x_126, x_3, x_4, x_5, x_6, x_7, x_8, x_127);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_138; 
x_130 = lean_ctor_get(x_128, 1);
x_131 = lean_ctor_get(x_128, 0);
lean_dec(x_131);
x_138 = l_Lean_Expr_getAppFn___main(x_126);
if (lean_obj_tag(x_138) == 4)
{
lean_object* x_139; 
lean_dec(x_126);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec(x_138);
lean_ctor_set(x_128, 0, x_139);
return x_128;
}
else
{
lean_object* x_140; 
lean_dec(x_138);
lean_free_object(x_128);
x_140 = lean_box(0);
x_132 = x_140;
goto block_137;
}
block_137:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_132);
x_133 = l_Lean_indentExpr(x_126);
x_134 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_135 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_135, x_3, x_4, x_5, x_6, x_7, x_8, x_130);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_136;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_148; 
x_141 = lean_ctor_get(x_128, 1);
lean_inc(x_141);
lean_dec(x_128);
x_148 = l_Lean_Expr_getAppFn___main(x_126);
if (lean_obj_tag(x_148) == 4)
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_126);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec(x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_141);
return x_150;
}
else
{
lean_object* x_151; 
lean_dec(x_148);
x_151 = lean_box(0);
x_142 = x_151;
goto block_147;
}
block_147:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_142);
x_143 = l_Lean_indentExpr(x_126);
x_144 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_145 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_146 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_145, x_3, x_4, x_5, x_6, x_7, x_8, x_141);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_146;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_126);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_152 = !lean_is_exclusive(x_128);
if (x_152 == 0)
{
return x_128;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_128, 0);
x_154 = lean_ctor_get(x_128, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_128);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_156 = !lean_is_exclusive(x_125);
if (x_156 == 0)
{
return x_125;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_125, 0);
x_158 = lean_ctor_get(x_125, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_125);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_160 = !lean_is_exclusive(x_122);
if (x_160 == 0)
{
return x_122;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_122, 0);
x_162 = lean_ctor_get(x_122, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_122);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
else
{
lean_object* x_164; 
lean_dec(x_2);
x_164 = lean_box(0);
x_70 = x_164;
goto block_75;
}
}
case 2:
{
lean_dec(x_76);
lean_free_object(x_66);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_65);
x_165 = lean_ctor_get(x_2, 1);
lean_inc(x_165);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_166 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_165, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_169 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_167, x_3, x_4, x_5, x_6, x_7, x_8, x_168);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
lean_inc(x_170);
x_172 = l_Lean_Elab_Term_tryPostponeIfMVar(x_170, x_3, x_4, x_5, x_6, x_7, x_8, x_171);
if (lean_obj_tag(x_172) == 0)
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_182; 
x_174 = lean_ctor_get(x_172, 1);
x_175 = lean_ctor_get(x_172, 0);
lean_dec(x_175);
x_182 = l_Lean_Expr_getAppFn___main(x_170);
if (lean_obj_tag(x_182) == 4)
{
lean_object* x_183; 
lean_dec(x_170);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec(x_182);
lean_ctor_set(x_172, 0, x_183);
return x_172;
}
else
{
lean_object* x_184; 
lean_dec(x_182);
lean_free_object(x_172);
x_184 = lean_box(0);
x_176 = x_184;
goto block_181;
}
block_181:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_176);
x_177 = l_Lean_indentExpr(x_170);
x_178 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_179 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
x_180 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_179, x_3, x_4, x_5, x_6, x_7, x_8, x_174);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_180;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_192; 
x_185 = lean_ctor_get(x_172, 1);
lean_inc(x_185);
lean_dec(x_172);
x_192 = l_Lean_Expr_getAppFn___main(x_170);
if (lean_obj_tag(x_192) == 4)
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_170);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_185);
return x_194;
}
else
{
lean_object* x_195; 
lean_dec(x_192);
x_195 = lean_box(0);
x_186 = x_195;
goto block_191;
}
block_191:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_186);
x_187 = l_Lean_indentExpr(x_170);
x_188 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_189 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_187);
x_190 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_189, x_3, x_4, x_5, x_6, x_7, x_8, x_185);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_190;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_170);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_196 = !lean_is_exclusive(x_172);
if (x_196 == 0)
{
return x_172;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_172, 0);
x_198 = lean_ctor_get(x_172, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_172);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
uint8_t x_200; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_200 = !lean_is_exclusive(x_169);
if (x_200 == 0)
{
return x_169;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_169, 0);
x_202 = lean_ctor_get(x_169, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_169);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_204 = !lean_is_exclusive(x_166);
if (x_204 == 0)
{
return x_166;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_166, 0);
x_206 = lean_ctor_get(x_166, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_166);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
else
{
lean_object* x_208; 
lean_dec(x_2);
x_208 = lean_box(0);
x_70 = x_208;
goto block_75;
}
}
case 3:
{
lean_dec(x_76);
lean_free_object(x_66);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_65);
x_209 = lean_ctor_get(x_2, 1);
lean_inc(x_209);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_210 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_209, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_213 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_211, x_3, x_4, x_5, x_6, x_7, x_8, x_212);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
lean_inc(x_214);
x_216 = l_Lean_Elab_Term_tryPostponeIfMVar(x_214, x_3, x_4, x_5, x_6, x_7, x_8, x_215);
if (lean_obj_tag(x_216) == 0)
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_226; 
x_218 = lean_ctor_get(x_216, 1);
x_219 = lean_ctor_get(x_216, 0);
lean_dec(x_219);
x_226 = l_Lean_Expr_getAppFn___main(x_214);
if (lean_obj_tag(x_226) == 4)
{
lean_object* x_227; 
lean_dec(x_214);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec(x_226);
lean_ctor_set(x_216, 0, x_227);
return x_216;
}
else
{
lean_object* x_228; 
lean_dec(x_226);
lean_free_object(x_216);
x_228 = lean_box(0);
x_220 = x_228;
goto block_225;
}
block_225:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_220);
x_221 = l_Lean_indentExpr(x_214);
x_222 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_223 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_221);
x_224 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_223, x_3, x_4, x_5, x_6, x_7, x_8, x_218);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_224;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_236; 
x_229 = lean_ctor_get(x_216, 1);
lean_inc(x_229);
lean_dec(x_216);
x_236 = l_Lean_Expr_getAppFn___main(x_214);
if (lean_obj_tag(x_236) == 4)
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_214);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec(x_236);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_229);
return x_238;
}
else
{
lean_object* x_239; 
lean_dec(x_236);
x_239 = lean_box(0);
x_230 = x_239;
goto block_235;
}
block_235:
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_230);
x_231 = l_Lean_indentExpr(x_214);
x_232 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_233 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
x_234 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_233, x_3, x_4, x_5, x_6, x_7, x_8, x_229);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_234;
}
}
}
else
{
uint8_t x_240; 
lean_dec(x_214);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_240 = !lean_is_exclusive(x_216);
if (x_240 == 0)
{
return x_216;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_216, 0);
x_242 = lean_ctor_get(x_216, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_216);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
}
else
{
uint8_t x_244; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_244 = !lean_is_exclusive(x_213);
if (x_244 == 0)
{
return x_213;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_213, 0);
x_246 = lean_ctor_get(x_213, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_213);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
}
else
{
uint8_t x_248; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_248 = !lean_is_exclusive(x_210);
if (x_248 == 0)
{
return x_210;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_210, 0);
x_250 = lean_ctor_get(x_210, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_210);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
}
else
{
lean_object* x_252; 
lean_dec(x_2);
x_252 = lean_box(0);
x_70 = x_252;
goto block_75;
}
}
case 4:
{
lean_object* x_253; 
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_253 = lean_ctor_get(x_76, 0);
lean_inc(x_253);
lean_dec(x_76);
lean_ctor_set(x_66, 0, x_253);
return x_66;
}
case 5:
{
lean_dec(x_76);
lean_free_object(x_66);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_65);
x_254 = lean_ctor_get(x_2, 1);
lean_inc(x_254);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_255 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_254, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_258 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_256, x_3, x_4, x_5, x_6, x_7, x_8, x_257);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
lean_inc(x_259);
x_261 = l_Lean_Elab_Term_tryPostponeIfMVar(x_259, x_3, x_4, x_5, x_6, x_7, x_8, x_260);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_271; 
x_263 = lean_ctor_get(x_261, 1);
x_264 = lean_ctor_get(x_261, 0);
lean_dec(x_264);
x_271 = l_Lean_Expr_getAppFn___main(x_259);
if (lean_obj_tag(x_271) == 4)
{
lean_object* x_272; 
lean_dec(x_259);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
lean_dec(x_271);
lean_ctor_set(x_261, 0, x_272);
return x_261;
}
else
{
lean_object* x_273; 
lean_dec(x_271);
lean_free_object(x_261);
x_273 = lean_box(0);
x_265 = x_273;
goto block_270;
}
block_270:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_265);
x_266 = l_Lean_indentExpr(x_259);
x_267 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_268 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_266);
x_269 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_268, x_3, x_4, x_5, x_6, x_7, x_8, x_263);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_269;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_281; 
x_274 = lean_ctor_get(x_261, 1);
lean_inc(x_274);
lean_dec(x_261);
x_281 = l_Lean_Expr_getAppFn___main(x_259);
if (lean_obj_tag(x_281) == 4)
{
lean_object* x_282; lean_object* x_283; 
lean_dec(x_259);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
lean_dec(x_281);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_274);
return x_283;
}
else
{
lean_object* x_284; 
lean_dec(x_281);
x_284 = lean_box(0);
x_275 = x_284;
goto block_280;
}
block_280:
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_275);
x_276 = l_Lean_indentExpr(x_259);
x_277 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_278 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_276);
x_279 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_278, x_3, x_4, x_5, x_6, x_7, x_8, x_274);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_279;
}
}
}
else
{
uint8_t x_285; 
lean_dec(x_259);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_285 = !lean_is_exclusive(x_261);
if (x_285 == 0)
{
return x_261;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_261, 0);
x_287 = lean_ctor_get(x_261, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_261);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
}
else
{
uint8_t x_289; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_289 = !lean_is_exclusive(x_258);
if (x_289 == 0)
{
return x_258;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_258, 0);
x_291 = lean_ctor_get(x_258, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_258);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
else
{
uint8_t x_293; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_293 = !lean_is_exclusive(x_255);
if (x_293 == 0)
{
return x_255;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_255, 0);
x_295 = lean_ctor_get(x_255, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_255);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
else
{
lean_object* x_297; 
lean_dec(x_2);
x_297 = lean_box(0);
x_70 = x_297;
goto block_75;
}
}
case 6:
{
lean_dec(x_76);
lean_free_object(x_66);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_65);
x_298 = lean_ctor_get(x_2, 1);
lean_inc(x_298);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_299 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_298, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_302 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_300, x_3, x_4, x_5, x_6, x_7, x_8, x_301);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
lean_inc(x_303);
x_305 = l_Lean_Elab_Term_tryPostponeIfMVar(x_303, x_3, x_4, x_5, x_6, x_7, x_8, x_304);
if (lean_obj_tag(x_305) == 0)
{
uint8_t x_306; 
x_306 = !lean_is_exclusive(x_305);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_315; 
x_307 = lean_ctor_get(x_305, 1);
x_308 = lean_ctor_get(x_305, 0);
lean_dec(x_308);
x_315 = l_Lean_Expr_getAppFn___main(x_303);
if (lean_obj_tag(x_315) == 4)
{
lean_object* x_316; 
lean_dec(x_303);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec(x_315);
lean_ctor_set(x_305, 0, x_316);
return x_305;
}
else
{
lean_object* x_317; 
lean_dec(x_315);
lean_free_object(x_305);
x_317 = lean_box(0);
x_309 = x_317;
goto block_314;
}
block_314:
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_309);
x_310 = l_Lean_indentExpr(x_303);
x_311 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_312 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_310);
x_313 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_312, x_3, x_4, x_5, x_6, x_7, x_8, x_307);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_313;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_325; 
x_318 = lean_ctor_get(x_305, 1);
lean_inc(x_318);
lean_dec(x_305);
x_325 = l_Lean_Expr_getAppFn___main(x_303);
if (lean_obj_tag(x_325) == 4)
{
lean_object* x_326; lean_object* x_327; 
lean_dec(x_303);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
lean_dec(x_325);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_318);
return x_327;
}
else
{
lean_object* x_328; 
lean_dec(x_325);
x_328 = lean_box(0);
x_319 = x_328;
goto block_324;
}
block_324:
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_319);
x_320 = l_Lean_indentExpr(x_303);
x_321 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_322 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_320);
x_323 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_322, x_3, x_4, x_5, x_6, x_7, x_8, x_318);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_323;
}
}
}
else
{
uint8_t x_329; 
lean_dec(x_303);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_329 = !lean_is_exclusive(x_305);
if (x_329 == 0)
{
return x_305;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_305, 0);
x_331 = lean_ctor_get(x_305, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_305);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
return x_332;
}
}
}
else
{
uint8_t x_333; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_333 = !lean_is_exclusive(x_302);
if (x_333 == 0)
{
return x_302;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_302, 0);
x_335 = lean_ctor_get(x_302, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_302);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
else
{
uint8_t x_337; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_337 = !lean_is_exclusive(x_299);
if (x_337 == 0)
{
return x_299;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_299, 0);
x_339 = lean_ctor_get(x_299, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_299);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
return x_340;
}
}
}
else
{
lean_object* x_341; 
lean_dec(x_2);
x_341 = lean_box(0);
x_70 = x_341;
goto block_75;
}
}
case 7:
{
lean_dec(x_76);
lean_free_object(x_66);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_342; lean_object* x_343; 
lean_dec(x_65);
x_342 = lean_ctor_get(x_2, 1);
lean_inc(x_342);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_343 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_342, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_346 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_344, x_3, x_4, x_5, x_6, x_7, x_8, x_345);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
lean_inc(x_347);
x_349 = l_Lean_Elab_Term_tryPostponeIfMVar(x_347, x_3, x_4, x_5, x_6, x_7, x_8, x_348);
if (lean_obj_tag(x_349) == 0)
{
uint8_t x_350; 
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_359; 
x_351 = lean_ctor_get(x_349, 1);
x_352 = lean_ctor_get(x_349, 0);
lean_dec(x_352);
x_359 = l_Lean_Expr_getAppFn___main(x_347);
if (lean_obj_tag(x_359) == 4)
{
lean_object* x_360; 
lean_dec(x_347);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
lean_dec(x_359);
lean_ctor_set(x_349, 0, x_360);
return x_349;
}
else
{
lean_object* x_361; 
lean_dec(x_359);
lean_free_object(x_349);
x_361 = lean_box(0);
x_353 = x_361;
goto block_358;
}
block_358:
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_353);
x_354 = l_Lean_indentExpr(x_347);
x_355 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_356 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_354);
x_357 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_356, x_3, x_4, x_5, x_6, x_7, x_8, x_351);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_357;
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_369; 
x_362 = lean_ctor_get(x_349, 1);
lean_inc(x_362);
lean_dec(x_349);
x_369 = l_Lean_Expr_getAppFn___main(x_347);
if (lean_obj_tag(x_369) == 4)
{
lean_object* x_370; lean_object* x_371; 
lean_dec(x_347);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
lean_dec(x_369);
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_362);
return x_371;
}
else
{
lean_object* x_372; 
lean_dec(x_369);
x_372 = lean_box(0);
x_363 = x_372;
goto block_368;
}
block_368:
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_363);
x_364 = l_Lean_indentExpr(x_347);
x_365 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_366 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_364);
x_367 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_366, x_3, x_4, x_5, x_6, x_7, x_8, x_362);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_367;
}
}
}
else
{
uint8_t x_373; 
lean_dec(x_347);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_373 = !lean_is_exclusive(x_349);
if (x_373 == 0)
{
return x_349;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_349, 0);
x_375 = lean_ctor_get(x_349, 1);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_349);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
}
}
else
{
uint8_t x_377; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_377 = !lean_is_exclusive(x_346);
if (x_377 == 0)
{
return x_346;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_346, 0);
x_379 = lean_ctor_get(x_346, 1);
lean_inc(x_379);
lean_inc(x_378);
lean_dec(x_346);
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
return x_380;
}
}
}
else
{
uint8_t x_381; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_381 = !lean_is_exclusive(x_343);
if (x_381 == 0)
{
return x_343;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_343, 0);
x_383 = lean_ctor_get(x_343, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_343);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
else
{
lean_object* x_385; 
lean_dec(x_2);
x_385 = lean_box(0);
x_70 = x_385;
goto block_75;
}
}
case 8:
{
lean_dec(x_76);
lean_free_object(x_66);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_386; lean_object* x_387; 
lean_dec(x_65);
x_386 = lean_ctor_get(x_2, 1);
lean_inc(x_386);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_387 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_386, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_390 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_388, x_3, x_4, x_5, x_6, x_7, x_8, x_389);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
lean_inc(x_391);
x_393 = l_Lean_Elab_Term_tryPostponeIfMVar(x_391, x_3, x_4, x_5, x_6, x_7, x_8, x_392);
if (lean_obj_tag(x_393) == 0)
{
uint8_t x_394; 
x_394 = !lean_is_exclusive(x_393);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_403; 
x_395 = lean_ctor_get(x_393, 1);
x_396 = lean_ctor_get(x_393, 0);
lean_dec(x_396);
x_403 = l_Lean_Expr_getAppFn___main(x_391);
if (lean_obj_tag(x_403) == 4)
{
lean_object* x_404; 
lean_dec(x_391);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
lean_dec(x_403);
lean_ctor_set(x_393, 0, x_404);
return x_393;
}
else
{
lean_object* x_405; 
lean_dec(x_403);
lean_free_object(x_393);
x_405 = lean_box(0);
x_397 = x_405;
goto block_402;
}
block_402:
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_397);
x_398 = l_Lean_indentExpr(x_391);
x_399 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_400 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_398);
x_401 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_400, x_3, x_4, x_5, x_6, x_7, x_8, x_395);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_401;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_413; 
x_406 = lean_ctor_get(x_393, 1);
lean_inc(x_406);
lean_dec(x_393);
x_413 = l_Lean_Expr_getAppFn___main(x_391);
if (lean_obj_tag(x_413) == 4)
{
lean_object* x_414; lean_object* x_415; 
lean_dec(x_391);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
lean_dec(x_413);
x_415 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_406);
return x_415;
}
else
{
lean_object* x_416; 
lean_dec(x_413);
x_416 = lean_box(0);
x_407 = x_416;
goto block_412;
}
block_412:
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_407);
x_408 = l_Lean_indentExpr(x_391);
x_409 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_410 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_408);
x_411 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_410, x_3, x_4, x_5, x_6, x_7, x_8, x_406);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_411;
}
}
}
else
{
uint8_t x_417; 
lean_dec(x_391);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_417 = !lean_is_exclusive(x_393);
if (x_417 == 0)
{
return x_393;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_393, 0);
x_419 = lean_ctor_get(x_393, 1);
lean_inc(x_419);
lean_inc(x_418);
lean_dec(x_393);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
return x_420;
}
}
}
else
{
uint8_t x_421; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_421 = !lean_is_exclusive(x_390);
if (x_421 == 0)
{
return x_390;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_422 = lean_ctor_get(x_390, 0);
x_423 = lean_ctor_get(x_390, 1);
lean_inc(x_423);
lean_inc(x_422);
lean_dec(x_390);
x_424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
return x_424;
}
}
}
else
{
uint8_t x_425; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_425 = !lean_is_exclusive(x_387);
if (x_425 == 0)
{
return x_387;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_426 = lean_ctor_get(x_387, 0);
x_427 = lean_ctor_get(x_387, 1);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_387);
x_428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
return x_428;
}
}
}
else
{
lean_object* x_429; 
lean_dec(x_2);
x_429 = lean_box(0);
x_70 = x_429;
goto block_75;
}
}
case 9:
{
lean_dec(x_76);
lean_free_object(x_66);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_430; lean_object* x_431; 
lean_dec(x_65);
x_430 = lean_ctor_get(x_2, 1);
lean_inc(x_430);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_431 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_430, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_434 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_432, x_3, x_4, x_5, x_6, x_7, x_8, x_433);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
lean_dec(x_434);
lean_inc(x_435);
x_437 = l_Lean_Elab_Term_tryPostponeIfMVar(x_435, x_3, x_4, x_5, x_6, x_7, x_8, x_436);
if (lean_obj_tag(x_437) == 0)
{
uint8_t x_438; 
x_438 = !lean_is_exclusive(x_437);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_447; 
x_439 = lean_ctor_get(x_437, 1);
x_440 = lean_ctor_get(x_437, 0);
lean_dec(x_440);
x_447 = l_Lean_Expr_getAppFn___main(x_435);
if (lean_obj_tag(x_447) == 4)
{
lean_object* x_448; 
lean_dec(x_435);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
lean_dec(x_447);
lean_ctor_set(x_437, 0, x_448);
return x_437;
}
else
{
lean_object* x_449; 
lean_dec(x_447);
lean_free_object(x_437);
x_449 = lean_box(0);
x_441 = x_449;
goto block_446;
}
block_446:
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_441);
x_442 = l_Lean_indentExpr(x_435);
x_443 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_444 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_442);
x_445 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_444, x_3, x_4, x_5, x_6, x_7, x_8, x_439);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_445;
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_457; 
x_450 = lean_ctor_get(x_437, 1);
lean_inc(x_450);
lean_dec(x_437);
x_457 = l_Lean_Expr_getAppFn___main(x_435);
if (lean_obj_tag(x_457) == 4)
{
lean_object* x_458; lean_object* x_459; 
lean_dec(x_435);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
lean_dec(x_457);
x_459 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_450);
return x_459;
}
else
{
lean_object* x_460; 
lean_dec(x_457);
x_460 = lean_box(0);
x_451 = x_460;
goto block_456;
}
block_456:
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_dec(x_451);
x_452 = l_Lean_indentExpr(x_435);
x_453 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_454 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_452);
x_455 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_454, x_3, x_4, x_5, x_6, x_7, x_8, x_450);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_455;
}
}
}
else
{
uint8_t x_461; 
lean_dec(x_435);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_461 = !lean_is_exclusive(x_437);
if (x_461 == 0)
{
return x_437;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_462 = lean_ctor_get(x_437, 0);
x_463 = lean_ctor_get(x_437, 1);
lean_inc(x_463);
lean_inc(x_462);
lean_dec(x_437);
x_464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_464, 0, x_462);
lean_ctor_set(x_464, 1, x_463);
return x_464;
}
}
}
else
{
uint8_t x_465; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_465 = !lean_is_exclusive(x_434);
if (x_465 == 0)
{
return x_434;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_466 = lean_ctor_get(x_434, 0);
x_467 = lean_ctor_get(x_434, 1);
lean_inc(x_467);
lean_inc(x_466);
lean_dec(x_434);
x_468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set(x_468, 1, x_467);
return x_468;
}
}
}
else
{
uint8_t x_469; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_469 = !lean_is_exclusive(x_431);
if (x_469 == 0)
{
return x_431;
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_470 = lean_ctor_get(x_431, 0);
x_471 = lean_ctor_get(x_431, 1);
lean_inc(x_471);
lean_inc(x_470);
lean_dec(x_431);
x_472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_471);
return x_472;
}
}
}
else
{
lean_object* x_473; 
lean_dec(x_2);
x_473 = lean_box(0);
x_70 = x_473;
goto block_75;
}
}
case 10:
{
lean_dec(x_76);
lean_free_object(x_66);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_474; lean_object* x_475; 
lean_dec(x_65);
x_474 = lean_ctor_get(x_2, 1);
lean_inc(x_474);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_475 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_474, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
lean_dec(x_475);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_478 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_476, x_3, x_4, x_5, x_6, x_7, x_8, x_477);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
lean_dec(x_478);
lean_inc(x_479);
x_481 = l_Lean_Elab_Term_tryPostponeIfMVar(x_479, x_3, x_4, x_5, x_6, x_7, x_8, x_480);
if (lean_obj_tag(x_481) == 0)
{
uint8_t x_482; 
x_482 = !lean_is_exclusive(x_481);
if (x_482 == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_491; 
x_483 = lean_ctor_get(x_481, 1);
x_484 = lean_ctor_get(x_481, 0);
lean_dec(x_484);
x_491 = l_Lean_Expr_getAppFn___main(x_479);
if (lean_obj_tag(x_491) == 4)
{
lean_object* x_492; 
lean_dec(x_479);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
lean_dec(x_491);
lean_ctor_set(x_481, 0, x_492);
return x_481;
}
else
{
lean_object* x_493; 
lean_dec(x_491);
lean_free_object(x_481);
x_493 = lean_box(0);
x_485 = x_493;
goto block_490;
}
block_490:
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
lean_dec(x_485);
x_486 = l_Lean_indentExpr(x_479);
x_487 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_488 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_486);
x_489 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_488, x_3, x_4, x_5, x_6, x_7, x_8, x_483);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_489;
}
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_501; 
x_494 = lean_ctor_get(x_481, 1);
lean_inc(x_494);
lean_dec(x_481);
x_501 = l_Lean_Expr_getAppFn___main(x_479);
if (lean_obj_tag(x_501) == 4)
{
lean_object* x_502; lean_object* x_503; 
lean_dec(x_479);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
lean_dec(x_501);
x_503 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_503, 0, x_502);
lean_ctor_set(x_503, 1, x_494);
return x_503;
}
else
{
lean_object* x_504; 
lean_dec(x_501);
x_504 = lean_box(0);
x_495 = x_504;
goto block_500;
}
block_500:
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
lean_dec(x_495);
x_496 = l_Lean_indentExpr(x_479);
x_497 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_498 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_496);
x_499 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_498, x_3, x_4, x_5, x_6, x_7, x_8, x_494);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_499;
}
}
}
else
{
uint8_t x_505; 
lean_dec(x_479);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_505 = !lean_is_exclusive(x_481);
if (x_505 == 0)
{
return x_481;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_506 = lean_ctor_get(x_481, 0);
x_507 = lean_ctor_get(x_481, 1);
lean_inc(x_507);
lean_inc(x_506);
lean_dec(x_481);
x_508 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_508, 0, x_506);
lean_ctor_set(x_508, 1, x_507);
return x_508;
}
}
}
else
{
uint8_t x_509; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_509 = !lean_is_exclusive(x_478);
if (x_509 == 0)
{
return x_478;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_510 = lean_ctor_get(x_478, 0);
x_511 = lean_ctor_get(x_478, 1);
lean_inc(x_511);
lean_inc(x_510);
lean_dec(x_478);
x_512 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_512, 0, x_510);
lean_ctor_set(x_512, 1, x_511);
return x_512;
}
}
}
else
{
uint8_t x_513; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_513 = !lean_is_exclusive(x_475);
if (x_513 == 0)
{
return x_475;
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_475, 0);
x_515 = lean_ctor_get(x_475, 1);
lean_inc(x_515);
lean_inc(x_514);
lean_dec(x_475);
x_516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
return x_516;
}
}
}
else
{
lean_object* x_517; 
lean_dec(x_2);
x_517 = lean_box(0);
x_70 = x_517;
goto block_75;
}
}
case 11:
{
lean_dec(x_76);
lean_free_object(x_66);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_518; lean_object* x_519; 
lean_dec(x_65);
x_518 = lean_ctor_get(x_2, 1);
lean_inc(x_518);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_519 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_518, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_519, 1);
lean_inc(x_521);
lean_dec(x_519);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_522 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_520, x_3, x_4, x_5, x_6, x_7, x_8, x_521);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
lean_dec(x_522);
lean_inc(x_523);
x_525 = l_Lean_Elab_Term_tryPostponeIfMVar(x_523, x_3, x_4, x_5, x_6, x_7, x_8, x_524);
if (lean_obj_tag(x_525) == 0)
{
uint8_t x_526; 
x_526 = !lean_is_exclusive(x_525);
if (x_526 == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_535; 
x_527 = lean_ctor_get(x_525, 1);
x_528 = lean_ctor_get(x_525, 0);
lean_dec(x_528);
x_535 = l_Lean_Expr_getAppFn___main(x_523);
if (lean_obj_tag(x_535) == 4)
{
lean_object* x_536; 
lean_dec(x_523);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
lean_dec(x_535);
lean_ctor_set(x_525, 0, x_536);
return x_525;
}
else
{
lean_object* x_537; 
lean_dec(x_535);
lean_free_object(x_525);
x_537 = lean_box(0);
x_529 = x_537;
goto block_534;
}
block_534:
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_529);
x_530 = l_Lean_indentExpr(x_523);
x_531 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_532 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_530);
x_533 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_532, x_3, x_4, x_5, x_6, x_7, x_8, x_527);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_533;
}
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_545; 
x_538 = lean_ctor_get(x_525, 1);
lean_inc(x_538);
lean_dec(x_525);
x_545 = l_Lean_Expr_getAppFn___main(x_523);
if (lean_obj_tag(x_545) == 4)
{
lean_object* x_546; lean_object* x_547; 
lean_dec(x_523);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
lean_dec(x_545);
x_547 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_547, 0, x_546);
lean_ctor_set(x_547, 1, x_538);
return x_547;
}
else
{
lean_object* x_548; 
lean_dec(x_545);
x_548 = lean_box(0);
x_539 = x_548;
goto block_544;
}
block_544:
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_539);
x_540 = l_Lean_indentExpr(x_523);
x_541 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_542 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_542, 0, x_541);
lean_ctor_set(x_542, 1, x_540);
x_543 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_542, x_3, x_4, x_5, x_6, x_7, x_8, x_538);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_543;
}
}
}
else
{
uint8_t x_549; 
lean_dec(x_523);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_549 = !lean_is_exclusive(x_525);
if (x_549 == 0)
{
return x_525;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_525, 0);
x_551 = lean_ctor_get(x_525, 1);
lean_inc(x_551);
lean_inc(x_550);
lean_dec(x_525);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
return x_552;
}
}
}
else
{
uint8_t x_553; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_553 = !lean_is_exclusive(x_522);
if (x_553 == 0)
{
return x_522;
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_554 = lean_ctor_get(x_522, 0);
x_555 = lean_ctor_get(x_522, 1);
lean_inc(x_555);
lean_inc(x_554);
lean_dec(x_522);
x_556 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_556, 0, x_554);
lean_ctor_set(x_556, 1, x_555);
return x_556;
}
}
}
else
{
uint8_t x_557; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_557 = !lean_is_exclusive(x_519);
if (x_557 == 0)
{
return x_519;
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_558 = lean_ctor_get(x_519, 0);
x_559 = lean_ctor_get(x_519, 1);
lean_inc(x_559);
lean_inc(x_558);
lean_dec(x_519);
x_560 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_560, 0, x_558);
lean_ctor_set(x_560, 1, x_559);
return x_560;
}
}
}
else
{
lean_object* x_561; 
lean_dec(x_2);
x_561 = lean_box(0);
x_70 = x_561;
goto block_75;
}
}
default: 
{
lean_dec(x_76);
lean_free_object(x_66);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_562; lean_object* x_563; 
lean_dec(x_65);
x_562 = lean_ctor_get(x_2, 1);
lean_inc(x_562);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_563 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_562, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
if (lean_obj_tag(x_563) == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_563, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_563, 1);
lean_inc(x_565);
lean_dec(x_563);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_566 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_564, x_3, x_4, x_5, x_6, x_7, x_8, x_565);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
lean_dec(x_566);
lean_inc(x_567);
x_569 = l_Lean_Elab_Term_tryPostponeIfMVar(x_567, x_3, x_4, x_5, x_6, x_7, x_8, x_568);
if (lean_obj_tag(x_569) == 0)
{
uint8_t x_570; 
x_570 = !lean_is_exclusive(x_569);
if (x_570 == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_579; 
x_571 = lean_ctor_get(x_569, 1);
x_572 = lean_ctor_get(x_569, 0);
lean_dec(x_572);
x_579 = l_Lean_Expr_getAppFn___main(x_567);
if (lean_obj_tag(x_579) == 4)
{
lean_object* x_580; 
lean_dec(x_567);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
lean_dec(x_579);
lean_ctor_set(x_569, 0, x_580);
return x_569;
}
else
{
lean_object* x_581; 
lean_dec(x_579);
lean_free_object(x_569);
x_581 = lean_box(0);
x_573 = x_581;
goto block_578;
}
block_578:
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
lean_dec(x_573);
x_574 = l_Lean_indentExpr(x_567);
x_575 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_576 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_574);
x_577 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_576, x_3, x_4, x_5, x_6, x_7, x_8, x_571);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_577;
}
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_589; 
x_582 = lean_ctor_get(x_569, 1);
lean_inc(x_582);
lean_dec(x_569);
x_589 = l_Lean_Expr_getAppFn___main(x_567);
if (lean_obj_tag(x_589) == 4)
{
lean_object* x_590; lean_object* x_591; 
lean_dec(x_567);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
lean_dec(x_589);
x_591 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_582);
return x_591;
}
else
{
lean_object* x_592; 
lean_dec(x_589);
x_592 = lean_box(0);
x_583 = x_592;
goto block_588;
}
block_588:
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_583);
x_584 = l_Lean_indentExpr(x_567);
x_585 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_586 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_584);
x_587 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_586, x_3, x_4, x_5, x_6, x_7, x_8, x_582);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_587;
}
}
}
else
{
uint8_t x_593; 
lean_dec(x_567);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_593 = !lean_is_exclusive(x_569);
if (x_593 == 0)
{
return x_569;
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_594 = lean_ctor_get(x_569, 0);
x_595 = lean_ctor_get(x_569, 1);
lean_inc(x_595);
lean_inc(x_594);
lean_dec(x_569);
x_596 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_596, 0, x_594);
lean_ctor_set(x_596, 1, x_595);
return x_596;
}
}
}
else
{
uint8_t x_597; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_597 = !lean_is_exclusive(x_566);
if (x_597 == 0)
{
return x_566;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_598 = lean_ctor_get(x_566, 0);
x_599 = lean_ctor_get(x_566, 1);
lean_inc(x_599);
lean_inc(x_598);
lean_dec(x_566);
x_600 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_600, 0, x_598);
lean_ctor_set(x_600, 1, x_599);
return x_600;
}
}
}
else
{
uint8_t x_601; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_601 = !lean_is_exclusive(x_563);
if (x_601 == 0)
{
return x_563;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_563, 0);
x_603 = lean_ctor_get(x_563, 1);
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_563);
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
return x_604;
}
}
}
else
{
lean_object* x_605; 
lean_dec(x_2);
x_605 = lean_box(0);
x_70 = x_605;
goto block_75;
}
}
}
block_75:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_70);
x_71 = l_Lean_indentExpr(x_65);
x_72 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_73, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_74;
}
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_614; 
x_606 = lean_ctor_get(x_66, 0);
x_607 = lean_ctor_get(x_66, 1);
lean_inc(x_607);
lean_inc(x_606);
lean_dec(x_66);
x_614 = l_Lean_Expr_getAppFn___main(x_606);
lean_dec(x_606);
switch (lean_obj_tag(x_614)) {
case 0:
{
lean_dec(x_614);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_615; lean_object* x_616; 
lean_dec(x_65);
x_615 = lean_ctor_get(x_2, 1);
lean_inc(x_615);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_616 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_615, x_3, x_4, x_5, x_6, x_7, x_8, x_607);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
lean_dec(x_616);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_619 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_617, x_3, x_4, x_5, x_6, x_7, x_8, x_618);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
lean_dec(x_619);
lean_inc(x_620);
x_622 = l_Lean_Elab_Term_tryPostponeIfMVar(x_620, x_3, x_4, x_5, x_6, x_7, x_8, x_621);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_631; 
x_623 = lean_ctor_get(x_622, 1);
lean_inc(x_623);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 x_624 = x_622;
} else {
 lean_dec_ref(x_622);
 x_624 = lean_box(0);
}
x_631 = l_Lean_Expr_getAppFn___main(x_620);
if (lean_obj_tag(x_631) == 4)
{
lean_object* x_632; lean_object* x_633; 
lean_dec(x_620);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
lean_dec(x_631);
if (lean_is_scalar(x_624)) {
 x_633 = lean_alloc_ctor(0, 2, 0);
} else {
 x_633 = x_624;
}
lean_ctor_set(x_633, 0, x_632);
lean_ctor_set(x_633, 1, x_623);
return x_633;
}
else
{
lean_object* x_634; 
lean_dec(x_631);
lean_dec(x_624);
x_634 = lean_box(0);
x_625 = x_634;
goto block_630;
}
block_630:
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_625);
x_626 = l_Lean_indentExpr(x_620);
x_627 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_628 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_628, 0, x_627);
lean_ctor_set(x_628, 1, x_626);
x_629 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_628, x_3, x_4, x_5, x_6, x_7, x_8, x_623);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_629;
}
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
lean_dec(x_620);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_635 = lean_ctor_get(x_622, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_622, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_622)) {
 lean_ctor_release(x_622, 0);
 lean_ctor_release(x_622, 1);
 x_637 = x_622;
} else {
 lean_dec_ref(x_622);
 x_637 = lean_box(0);
}
if (lean_is_scalar(x_637)) {
 x_638 = lean_alloc_ctor(1, 2, 0);
} else {
 x_638 = x_637;
}
lean_ctor_set(x_638, 0, x_635);
lean_ctor_set(x_638, 1, x_636);
return x_638;
}
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_639 = lean_ctor_get(x_619, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_619, 1);
lean_inc(x_640);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_641 = x_619;
} else {
 lean_dec_ref(x_619);
 x_641 = lean_box(0);
}
if (lean_is_scalar(x_641)) {
 x_642 = lean_alloc_ctor(1, 2, 0);
} else {
 x_642 = x_641;
}
lean_ctor_set(x_642, 0, x_639);
lean_ctor_set(x_642, 1, x_640);
return x_642;
}
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_643 = lean_ctor_get(x_616, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_616, 1);
lean_inc(x_644);
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 lean_ctor_release(x_616, 1);
 x_645 = x_616;
} else {
 lean_dec_ref(x_616);
 x_645 = lean_box(0);
}
if (lean_is_scalar(x_645)) {
 x_646 = lean_alloc_ctor(1, 2, 0);
} else {
 x_646 = x_645;
}
lean_ctor_set(x_646, 0, x_643);
lean_ctor_set(x_646, 1, x_644);
return x_646;
}
}
else
{
lean_object* x_647; 
lean_dec(x_2);
x_647 = lean_box(0);
x_608 = x_647;
goto block_613;
}
}
case 1:
{
lean_dec(x_614);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_648; lean_object* x_649; 
lean_dec(x_65);
x_648 = lean_ctor_get(x_2, 1);
lean_inc(x_648);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_649 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_648, x_3, x_4, x_5, x_6, x_7, x_8, x_607);
if (lean_obj_tag(x_649) == 0)
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_649, 1);
lean_inc(x_651);
lean_dec(x_649);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_652 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_650, x_3, x_4, x_5, x_6, x_7, x_8, x_651);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
lean_dec(x_652);
lean_inc(x_653);
x_655 = l_Lean_Elab_Term_tryPostponeIfMVar(x_653, x_3, x_4, x_5, x_6, x_7, x_8, x_654);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_664; 
x_656 = lean_ctor_get(x_655, 1);
lean_inc(x_656);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_657 = x_655;
} else {
 lean_dec_ref(x_655);
 x_657 = lean_box(0);
}
x_664 = l_Lean_Expr_getAppFn___main(x_653);
if (lean_obj_tag(x_664) == 4)
{
lean_object* x_665; lean_object* x_666; 
lean_dec(x_653);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
lean_dec(x_664);
if (lean_is_scalar(x_657)) {
 x_666 = lean_alloc_ctor(0, 2, 0);
} else {
 x_666 = x_657;
}
lean_ctor_set(x_666, 0, x_665);
lean_ctor_set(x_666, 1, x_656);
return x_666;
}
else
{
lean_object* x_667; 
lean_dec(x_664);
lean_dec(x_657);
x_667 = lean_box(0);
x_658 = x_667;
goto block_663;
}
block_663:
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; 
lean_dec(x_658);
x_659 = l_Lean_indentExpr(x_653);
x_660 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_661 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_661, 0, x_660);
lean_ctor_set(x_661, 1, x_659);
x_662 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_661, x_3, x_4, x_5, x_6, x_7, x_8, x_656);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_662;
}
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
lean_dec(x_653);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_668 = lean_ctor_get(x_655, 0);
lean_inc(x_668);
x_669 = lean_ctor_get(x_655, 1);
lean_inc(x_669);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_670 = x_655;
} else {
 lean_dec_ref(x_655);
 x_670 = lean_box(0);
}
if (lean_is_scalar(x_670)) {
 x_671 = lean_alloc_ctor(1, 2, 0);
} else {
 x_671 = x_670;
}
lean_ctor_set(x_671, 0, x_668);
lean_ctor_set(x_671, 1, x_669);
return x_671;
}
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_672 = lean_ctor_get(x_652, 0);
lean_inc(x_672);
x_673 = lean_ctor_get(x_652, 1);
lean_inc(x_673);
if (lean_is_exclusive(x_652)) {
 lean_ctor_release(x_652, 0);
 lean_ctor_release(x_652, 1);
 x_674 = x_652;
} else {
 lean_dec_ref(x_652);
 x_674 = lean_box(0);
}
if (lean_is_scalar(x_674)) {
 x_675 = lean_alloc_ctor(1, 2, 0);
} else {
 x_675 = x_674;
}
lean_ctor_set(x_675, 0, x_672);
lean_ctor_set(x_675, 1, x_673);
return x_675;
}
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_676 = lean_ctor_get(x_649, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_649, 1);
lean_inc(x_677);
if (lean_is_exclusive(x_649)) {
 lean_ctor_release(x_649, 0);
 lean_ctor_release(x_649, 1);
 x_678 = x_649;
} else {
 lean_dec_ref(x_649);
 x_678 = lean_box(0);
}
if (lean_is_scalar(x_678)) {
 x_679 = lean_alloc_ctor(1, 2, 0);
} else {
 x_679 = x_678;
}
lean_ctor_set(x_679, 0, x_676);
lean_ctor_set(x_679, 1, x_677);
return x_679;
}
}
else
{
lean_object* x_680; 
lean_dec(x_2);
x_680 = lean_box(0);
x_608 = x_680;
goto block_613;
}
}
case 2:
{
lean_dec(x_614);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_681; lean_object* x_682; 
lean_dec(x_65);
x_681 = lean_ctor_get(x_2, 1);
lean_inc(x_681);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_682 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_681, x_3, x_4, x_5, x_6, x_7, x_8, x_607);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_682, 1);
lean_inc(x_684);
lean_dec(x_682);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_685 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_683, x_3, x_4, x_5, x_6, x_7, x_8, x_684);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_685, 1);
lean_inc(x_687);
lean_dec(x_685);
lean_inc(x_686);
x_688 = l_Lean_Elab_Term_tryPostponeIfMVar(x_686, x_3, x_4, x_5, x_6, x_7, x_8, x_687);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_697; 
x_689 = lean_ctor_get(x_688, 1);
lean_inc(x_689);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 lean_ctor_release(x_688, 1);
 x_690 = x_688;
} else {
 lean_dec_ref(x_688);
 x_690 = lean_box(0);
}
x_697 = l_Lean_Expr_getAppFn___main(x_686);
if (lean_obj_tag(x_697) == 4)
{
lean_object* x_698; lean_object* x_699; 
lean_dec(x_686);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_698 = lean_ctor_get(x_697, 0);
lean_inc(x_698);
lean_dec(x_697);
if (lean_is_scalar(x_690)) {
 x_699 = lean_alloc_ctor(0, 2, 0);
} else {
 x_699 = x_690;
}
lean_ctor_set(x_699, 0, x_698);
lean_ctor_set(x_699, 1, x_689);
return x_699;
}
else
{
lean_object* x_700; 
lean_dec(x_697);
lean_dec(x_690);
x_700 = lean_box(0);
x_691 = x_700;
goto block_696;
}
block_696:
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
lean_dec(x_691);
x_692 = l_Lean_indentExpr(x_686);
x_693 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_694 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_694, 0, x_693);
lean_ctor_set(x_694, 1, x_692);
x_695 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_694, x_3, x_4, x_5, x_6, x_7, x_8, x_689);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_695;
}
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
lean_dec(x_686);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_701 = lean_ctor_get(x_688, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_688, 1);
lean_inc(x_702);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 lean_ctor_release(x_688, 1);
 x_703 = x_688;
} else {
 lean_dec_ref(x_688);
 x_703 = lean_box(0);
}
if (lean_is_scalar(x_703)) {
 x_704 = lean_alloc_ctor(1, 2, 0);
} else {
 x_704 = x_703;
}
lean_ctor_set(x_704, 0, x_701);
lean_ctor_set(x_704, 1, x_702);
return x_704;
}
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_705 = lean_ctor_get(x_685, 0);
lean_inc(x_705);
x_706 = lean_ctor_get(x_685, 1);
lean_inc(x_706);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 x_707 = x_685;
} else {
 lean_dec_ref(x_685);
 x_707 = lean_box(0);
}
if (lean_is_scalar(x_707)) {
 x_708 = lean_alloc_ctor(1, 2, 0);
} else {
 x_708 = x_707;
}
lean_ctor_set(x_708, 0, x_705);
lean_ctor_set(x_708, 1, x_706);
return x_708;
}
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_709 = lean_ctor_get(x_682, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_682, 1);
lean_inc(x_710);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 lean_ctor_release(x_682, 1);
 x_711 = x_682;
} else {
 lean_dec_ref(x_682);
 x_711 = lean_box(0);
}
if (lean_is_scalar(x_711)) {
 x_712 = lean_alloc_ctor(1, 2, 0);
} else {
 x_712 = x_711;
}
lean_ctor_set(x_712, 0, x_709);
lean_ctor_set(x_712, 1, x_710);
return x_712;
}
}
else
{
lean_object* x_713; 
lean_dec(x_2);
x_713 = lean_box(0);
x_608 = x_713;
goto block_613;
}
}
case 3:
{
lean_dec(x_614);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_714; lean_object* x_715; 
lean_dec(x_65);
x_714 = lean_ctor_get(x_2, 1);
lean_inc(x_714);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_715 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_714, x_3, x_4, x_5, x_6, x_7, x_8, x_607);
if (lean_obj_tag(x_715) == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
lean_dec(x_715);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_718 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_716, x_3, x_4, x_5, x_6, x_7, x_8, x_717);
if (lean_obj_tag(x_718) == 0)
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
lean_dec(x_718);
lean_inc(x_719);
x_721 = l_Lean_Elab_Term_tryPostponeIfMVar(x_719, x_3, x_4, x_5, x_6, x_7, x_8, x_720);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_730; 
x_722 = lean_ctor_get(x_721, 1);
lean_inc(x_722);
if (lean_is_exclusive(x_721)) {
 lean_ctor_release(x_721, 0);
 lean_ctor_release(x_721, 1);
 x_723 = x_721;
} else {
 lean_dec_ref(x_721);
 x_723 = lean_box(0);
}
x_730 = l_Lean_Expr_getAppFn___main(x_719);
if (lean_obj_tag(x_730) == 4)
{
lean_object* x_731; lean_object* x_732; 
lean_dec(x_719);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
lean_dec(x_730);
if (lean_is_scalar(x_723)) {
 x_732 = lean_alloc_ctor(0, 2, 0);
} else {
 x_732 = x_723;
}
lean_ctor_set(x_732, 0, x_731);
lean_ctor_set(x_732, 1, x_722);
return x_732;
}
else
{
lean_object* x_733; 
lean_dec(x_730);
lean_dec(x_723);
x_733 = lean_box(0);
x_724 = x_733;
goto block_729;
}
block_729:
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
lean_dec(x_724);
x_725 = l_Lean_indentExpr(x_719);
x_726 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_727 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_725);
x_728 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_727, x_3, x_4, x_5, x_6, x_7, x_8, x_722);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_728;
}
}
else
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
lean_dec(x_719);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_734 = lean_ctor_get(x_721, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_721, 1);
lean_inc(x_735);
if (lean_is_exclusive(x_721)) {
 lean_ctor_release(x_721, 0);
 lean_ctor_release(x_721, 1);
 x_736 = x_721;
} else {
 lean_dec_ref(x_721);
 x_736 = lean_box(0);
}
if (lean_is_scalar(x_736)) {
 x_737 = lean_alloc_ctor(1, 2, 0);
} else {
 x_737 = x_736;
}
lean_ctor_set(x_737, 0, x_734);
lean_ctor_set(x_737, 1, x_735);
return x_737;
}
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_738 = lean_ctor_get(x_718, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_718, 1);
lean_inc(x_739);
if (lean_is_exclusive(x_718)) {
 lean_ctor_release(x_718, 0);
 lean_ctor_release(x_718, 1);
 x_740 = x_718;
} else {
 lean_dec_ref(x_718);
 x_740 = lean_box(0);
}
if (lean_is_scalar(x_740)) {
 x_741 = lean_alloc_ctor(1, 2, 0);
} else {
 x_741 = x_740;
}
lean_ctor_set(x_741, 0, x_738);
lean_ctor_set(x_741, 1, x_739);
return x_741;
}
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_742 = lean_ctor_get(x_715, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_715, 1);
lean_inc(x_743);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_744 = x_715;
} else {
 lean_dec_ref(x_715);
 x_744 = lean_box(0);
}
if (lean_is_scalar(x_744)) {
 x_745 = lean_alloc_ctor(1, 2, 0);
} else {
 x_745 = x_744;
}
lean_ctor_set(x_745, 0, x_742);
lean_ctor_set(x_745, 1, x_743);
return x_745;
}
}
else
{
lean_object* x_746; 
lean_dec(x_2);
x_746 = lean_box(0);
x_608 = x_746;
goto block_613;
}
}
case 4:
{
lean_object* x_747; lean_object* x_748; 
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_747 = lean_ctor_get(x_614, 0);
lean_inc(x_747);
lean_dec(x_614);
x_748 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_748, 0, x_747);
lean_ctor_set(x_748, 1, x_607);
return x_748;
}
case 5:
{
lean_dec(x_614);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_749; lean_object* x_750; 
lean_dec(x_65);
x_749 = lean_ctor_get(x_2, 1);
lean_inc(x_749);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_750 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_749, x_3, x_4, x_5, x_6, x_7, x_8, x_607);
if (lean_obj_tag(x_750) == 0)
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_751 = lean_ctor_get(x_750, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_750, 1);
lean_inc(x_752);
lean_dec(x_750);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_753 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_751, x_3, x_4, x_5, x_6, x_7, x_8, x_752);
if (lean_obj_tag(x_753) == 0)
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_754 = lean_ctor_get(x_753, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_753, 1);
lean_inc(x_755);
lean_dec(x_753);
lean_inc(x_754);
x_756 = l_Lean_Elab_Term_tryPostponeIfMVar(x_754, x_3, x_4, x_5, x_6, x_7, x_8, x_755);
if (lean_obj_tag(x_756) == 0)
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_765; 
x_757 = lean_ctor_get(x_756, 1);
lean_inc(x_757);
if (lean_is_exclusive(x_756)) {
 lean_ctor_release(x_756, 0);
 lean_ctor_release(x_756, 1);
 x_758 = x_756;
} else {
 lean_dec_ref(x_756);
 x_758 = lean_box(0);
}
x_765 = l_Lean_Expr_getAppFn___main(x_754);
if (lean_obj_tag(x_765) == 4)
{
lean_object* x_766; lean_object* x_767; 
lean_dec(x_754);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_766 = lean_ctor_get(x_765, 0);
lean_inc(x_766);
lean_dec(x_765);
if (lean_is_scalar(x_758)) {
 x_767 = lean_alloc_ctor(0, 2, 0);
} else {
 x_767 = x_758;
}
lean_ctor_set(x_767, 0, x_766);
lean_ctor_set(x_767, 1, x_757);
return x_767;
}
else
{
lean_object* x_768; 
lean_dec(x_765);
lean_dec(x_758);
x_768 = lean_box(0);
x_759 = x_768;
goto block_764;
}
block_764:
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; 
lean_dec(x_759);
x_760 = l_Lean_indentExpr(x_754);
x_761 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_762 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_762, 0, x_761);
lean_ctor_set(x_762, 1, x_760);
x_763 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_762, x_3, x_4, x_5, x_6, x_7, x_8, x_757);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_763;
}
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; 
lean_dec(x_754);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_769 = lean_ctor_get(x_756, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_756, 1);
lean_inc(x_770);
if (lean_is_exclusive(x_756)) {
 lean_ctor_release(x_756, 0);
 lean_ctor_release(x_756, 1);
 x_771 = x_756;
} else {
 lean_dec_ref(x_756);
 x_771 = lean_box(0);
}
if (lean_is_scalar(x_771)) {
 x_772 = lean_alloc_ctor(1, 2, 0);
} else {
 x_772 = x_771;
}
lean_ctor_set(x_772, 0, x_769);
lean_ctor_set(x_772, 1, x_770);
return x_772;
}
}
else
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_773 = lean_ctor_get(x_753, 0);
lean_inc(x_773);
x_774 = lean_ctor_get(x_753, 1);
lean_inc(x_774);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 lean_ctor_release(x_753, 1);
 x_775 = x_753;
} else {
 lean_dec_ref(x_753);
 x_775 = lean_box(0);
}
if (lean_is_scalar(x_775)) {
 x_776 = lean_alloc_ctor(1, 2, 0);
} else {
 x_776 = x_775;
}
lean_ctor_set(x_776, 0, x_773);
lean_ctor_set(x_776, 1, x_774);
return x_776;
}
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_777 = lean_ctor_get(x_750, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_750, 1);
lean_inc(x_778);
if (lean_is_exclusive(x_750)) {
 lean_ctor_release(x_750, 0);
 lean_ctor_release(x_750, 1);
 x_779 = x_750;
} else {
 lean_dec_ref(x_750);
 x_779 = lean_box(0);
}
if (lean_is_scalar(x_779)) {
 x_780 = lean_alloc_ctor(1, 2, 0);
} else {
 x_780 = x_779;
}
lean_ctor_set(x_780, 0, x_777);
lean_ctor_set(x_780, 1, x_778);
return x_780;
}
}
else
{
lean_object* x_781; 
lean_dec(x_2);
x_781 = lean_box(0);
x_608 = x_781;
goto block_613;
}
}
case 6:
{
lean_dec(x_614);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_782; lean_object* x_783; 
lean_dec(x_65);
x_782 = lean_ctor_get(x_2, 1);
lean_inc(x_782);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_783 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_782, x_3, x_4, x_5, x_6, x_7, x_8, x_607);
if (lean_obj_tag(x_783) == 0)
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; 
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
lean_dec(x_783);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_786 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_784, x_3, x_4, x_5, x_6, x_7, x_8, x_785);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_787 = lean_ctor_get(x_786, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_786, 1);
lean_inc(x_788);
lean_dec(x_786);
lean_inc(x_787);
x_789 = l_Lean_Elab_Term_tryPostponeIfMVar(x_787, x_3, x_4, x_5, x_6, x_7, x_8, x_788);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_798; 
x_790 = lean_ctor_get(x_789, 1);
lean_inc(x_790);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_791 = x_789;
} else {
 lean_dec_ref(x_789);
 x_791 = lean_box(0);
}
x_798 = l_Lean_Expr_getAppFn___main(x_787);
if (lean_obj_tag(x_798) == 4)
{
lean_object* x_799; lean_object* x_800; 
lean_dec(x_787);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_799 = lean_ctor_get(x_798, 0);
lean_inc(x_799);
lean_dec(x_798);
if (lean_is_scalar(x_791)) {
 x_800 = lean_alloc_ctor(0, 2, 0);
} else {
 x_800 = x_791;
}
lean_ctor_set(x_800, 0, x_799);
lean_ctor_set(x_800, 1, x_790);
return x_800;
}
else
{
lean_object* x_801; 
lean_dec(x_798);
lean_dec(x_791);
x_801 = lean_box(0);
x_792 = x_801;
goto block_797;
}
block_797:
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
lean_dec(x_792);
x_793 = l_Lean_indentExpr(x_787);
x_794 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_795 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set(x_795, 1, x_793);
x_796 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_795, x_3, x_4, x_5, x_6, x_7, x_8, x_790);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_796;
}
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; 
lean_dec(x_787);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_802 = lean_ctor_get(x_789, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_789, 1);
lean_inc(x_803);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_804 = x_789;
} else {
 lean_dec_ref(x_789);
 x_804 = lean_box(0);
}
if (lean_is_scalar(x_804)) {
 x_805 = lean_alloc_ctor(1, 2, 0);
} else {
 x_805 = x_804;
}
lean_ctor_set(x_805, 0, x_802);
lean_ctor_set(x_805, 1, x_803);
return x_805;
}
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_806 = lean_ctor_get(x_786, 0);
lean_inc(x_806);
x_807 = lean_ctor_get(x_786, 1);
lean_inc(x_807);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 x_808 = x_786;
} else {
 lean_dec_ref(x_786);
 x_808 = lean_box(0);
}
if (lean_is_scalar(x_808)) {
 x_809 = lean_alloc_ctor(1, 2, 0);
} else {
 x_809 = x_808;
}
lean_ctor_set(x_809, 0, x_806);
lean_ctor_set(x_809, 1, x_807);
return x_809;
}
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_810 = lean_ctor_get(x_783, 0);
lean_inc(x_810);
x_811 = lean_ctor_get(x_783, 1);
lean_inc(x_811);
if (lean_is_exclusive(x_783)) {
 lean_ctor_release(x_783, 0);
 lean_ctor_release(x_783, 1);
 x_812 = x_783;
} else {
 lean_dec_ref(x_783);
 x_812 = lean_box(0);
}
if (lean_is_scalar(x_812)) {
 x_813 = lean_alloc_ctor(1, 2, 0);
} else {
 x_813 = x_812;
}
lean_ctor_set(x_813, 0, x_810);
lean_ctor_set(x_813, 1, x_811);
return x_813;
}
}
else
{
lean_object* x_814; 
lean_dec(x_2);
x_814 = lean_box(0);
x_608 = x_814;
goto block_613;
}
}
case 7:
{
lean_dec(x_614);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_815; lean_object* x_816; 
lean_dec(x_65);
x_815 = lean_ctor_get(x_2, 1);
lean_inc(x_815);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_816 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_815, x_3, x_4, x_5, x_6, x_7, x_8, x_607);
if (lean_obj_tag(x_816) == 0)
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_817 = lean_ctor_get(x_816, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_816, 1);
lean_inc(x_818);
lean_dec(x_816);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_819 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_817, x_3, x_4, x_5, x_6, x_7, x_8, x_818);
if (lean_obj_tag(x_819) == 0)
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_819, 1);
lean_inc(x_821);
lean_dec(x_819);
lean_inc(x_820);
x_822 = l_Lean_Elab_Term_tryPostponeIfMVar(x_820, x_3, x_4, x_5, x_6, x_7, x_8, x_821);
if (lean_obj_tag(x_822) == 0)
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_831; 
x_823 = lean_ctor_get(x_822, 1);
lean_inc(x_823);
if (lean_is_exclusive(x_822)) {
 lean_ctor_release(x_822, 0);
 lean_ctor_release(x_822, 1);
 x_824 = x_822;
} else {
 lean_dec_ref(x_822);
 x_824 = lean_box(0);
}
x_831 = l_Lean_Expr_getAppFn___main(x_820);
if (lean_obj_tag(x_831) == 4)
{
lean_object* x_832; lean_object* x_833; 
lean_dec(x_820);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_832 = lean_ctor_get(x_831, 0);
lean_inc(x_832);
lean_dec(x_831);
if (lean_is_scalar(x_824)) {
 x_833 = lean_alloc_ctor(0, 2, 0);
} else {
 x_833 = x_824;
}
lean_ctor_set(x_833, 0, x_832);
lean_ctor_set(x_833, 1, x_823);
return x_833;
}
else
{
lean_object* x_834; 
lean_dec(x_831);
lean_dec(x_824);
x_834 = lean_box(0);
x_825 = x_834;
goto block_830;
}
block_830:
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; 
lean_dec(x_825);
x_826 = l_Lean_indentExpr(x_820);
x_827 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_828 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_828, 0, x_827);
lean_ctor_set(x_828, 1, x_826);
x_829 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_828, x_3, x_4, x_5, x_6, x_7, x_8, x_823);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_829;
}
}
else
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; 
lean_dec(x_820);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_835 = lean_ctor_get(x_822, 0);
lean_inc(x_835);
x_836 = lean_ctor_get(x_822, 1);
lean_inc(x_836);
if (lean_is_exclusive(x_822)) {
 lean_ctor_release(x_822, 0);
 lean_ctor_release(x_822, 1);
 x_837 = x_822;
} else {
 lean_dec_ref(x_822);
 x_837 = lean_box(0);
}
if (lean_is_scalar(x_837)) {
 x_838 = lean_alloc_ctor(1, 2, 0);
} else {
 x_838 = x_837;
}
lean_ctor_set(x_838, 0, x_835);
lean_ctor_set(x_838, 1, x_836);
return x_838;
}
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_839 = lean_ctor_get(x_819, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_819, 1);
lean_inc(x_840);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 x_841 = x_819;
} else {
 lean_dec_ref(x_819);
 x_841 = lean_box(0);
}
if (lean_is_scalar(x_841)) {
 x_842 = lean_alloc_ctor(1, 2, 0);
} else {
 x_842 = x_841;
}
lean_ctor_set(x_842, 0, x_839);
lean_ctor_set(x_842, 1, x_840);
return x_842;
}
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_843 = lean_ctor_get(x_816, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_816, 1);
lean_inc(x_844);
if (lean_is_exclusive(x_816)) {
 lean_ctor_release(x_816, 0);
 lean_ctor_release(x_816, 1);
 x_845 = x_816;
} else {
 lean_dec_ref(x_816);
 x_845 = lean_box(0);
}
if (lean_is_scalar(x_845)) {
 x_846 = lean_alloc_ctor(1, 2, 0);
} else {
 x_846 = x_845;
}
lean_ctor_set(x_846, 0, x_843);
lean_ctor_set(x_846, 1, x_844);
return x_846;
}
}
else
{
lean_object* x_847; 
lean_dec(x_2);
x_847 = lean_box(0);
x_608 = x_847;
goto block_613;
}
}
case 8:
{
lean_dec(x_614);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_848; lean_object* x_849; 
lean_dec(x_65);
x_848 = lean_ctor_get(x_2, 1);
lean_inc(x_848);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_849 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_848, x_3, x_4, x_5, x_6, x_7, x_8, x_607);
if (lean_obj_tag(x_849) == 0)
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; 
x_850 = lean_ctor_get(x_849, 0);
lean_inc(x_850);
x_851 = lean_ctor_get(x_849, 1);
lean_inc(x_851);
lean_dec(x_849);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_852 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_850, x_3, x_4, x_5, x_6, x_7, x_8, x_851);
if (lean_obj_tag(x_852) == 0)
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; 
x_853 = lean_ctor_get(x_852, 0);
lean_inc(x_853);
x_854 = lean_ctor_get(x_852, 1);
lean_inc(x_854);
lean_dec(x_852);
lean_inc(x_853);
x_855 = l_Lean_Elab_Term_tryPostponeIfMVar(x_853, x_3, x_4, x_5, x_6, x_7, x_8, x_854);
if (lean_obj_tag(x_855) == 0)
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_864; 
x_856 = lean_ctor_get(x_855, 1);
lean_inc(x_856);
if (lean_is_exclusive(x_855)) {
 lean_ctor_release(x_855, 0);
 lean_ctor_release(x_855, 1);
 x_857 = x_855;
} else {
 lean_dec_ref(x_855);
 x_857 = lean_box(0);
}
x_864 = l_Lean_Expr_getAppFn___main(x_853);
if (lean_obj_tag(x_864) == 4)
{
lean_object* x_865; lean_object* x_866; 
lean_dec(x_853);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
lean_dec(x_864);
if (lean_is_scalar(x_857)) {
 x_866 = lean_alloc_ctor(0, 2, 0);
} else {
 x_866 = x_857;
}
lean_ctor_set(x_866, 0, x_865);
lean_ctor_set(x_866, 1, x_856);
return x_866;
}
else
{
lean_object* x_867; 
lean_dec(x_864);
lean_dec(x_857);
x_867 = lean_box(0);
x_858 = x_867;
goto block_863;
}
block_863:
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; 
lean_dec(x_858);
x_859 = l_Lean_indentExpr(x_853);
x_860 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_861 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_861, 0, x_860);
lean_ctor_set(x_861, 1, x_859);
x_862 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_861, x_3, x_4, x_5, x_6, x_7, x_8, x_856);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_862;
}
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; 
lean_dec(x_853);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_868 = lean_ctor_get(x_855, 0);
lean_inc(x_868);
x_869 = lean_ctor_get(x_855, 1);
lean_inc(x_869);
if (lean_is_exclusive(x_855)) {
 lean_ctor_release(x_855, 0);
 lean_ctor_release(x_855, 1);
 x_870 = x_855;
} else {
 lean_dec_ref(x_855);
 x_870 = lean_box(0);
}
if (lean_is_scalar(x_870)) {
 x_871 = lean_alloc_ctor(1, 2, 0);
} else {
 x_871 = x_870;
}
lean_ctor_set(x_871, 0, x_868);
lean_ctor_set(x_871, 1, x_869);
return x_871;
}
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_872 = lean_ctor_get(x_852, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_852, 1);
lean_inc(x_873);
if (lean_is_exclusive(x_852)) {
 lean_ctor_release(x_852, 0);
 lean_ctor_release(x_852, 1);
 x_874 = x_852;
} else {
 lean_dec_ref(x_852);
 x_874 = lean_box(0);
}
if (lean_is_scalar(x_874)) {
 x_875 = lean_alloc_ctor(1, 2, 0);
} else {
 x_875 = x_874;
}
lean_ctor_set(x_875, 0, x_872);
lean_ctor_set(x_875, 1, x_873);
return x_875;
}
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_876 = lean_ctor_get(x_849, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_849, 1);
lean_inc(x_877);
if (lean_is_exclusive(x_849)) {
 lean_ctor_release(x_849, 0);
 lean_ctor_release(x_849, 1);
 x_878 = x_849;
} else {
 lean_dec_ref(x_849);
 x_878 = lean_box(0);
}
if (lean_is_scalar(x_878)) {
 x_879 = lean_alloc_ctor(1, 2, 0);
} else {
 x_879 = x_878;
}
lean_ctor_set(x_879, 0, x_876);
lean_ctor_set(x_879, 1, x_877);
return x_879;
}
}
else
{
lean_object* x_880; 
lean_dec(x_2);
x_880 = lean_box(0);
x_608 = x_880;
goto block_613;
}
}
case 9:
{
lean_dec(x_614);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_881; lean_object* x_882; 
lean_dec(x_65);
x_881 = lean_ctor_get(x_2, 1);
lean_inc(x_881);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_882 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_881, x_3, x_4, x_5, x_6, x_7, x_8, x_607);
if (lean_obj_tag(x_882) == 0)
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; 
x_883 = lean_ctor_get(x_882, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_882, 1);
lean_inc(x_884);
lean_dec(x_882);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_885 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_883, x_3, x_4, x_5, x_6, x_7, x_8, x_884);
if (lean_obj_tag(x_885) == 0)
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; 
x_886 = lean_ctor_get(x_885, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_885, 1);
lean_inc(x_887);
lean_dec(x_885);
lean_inc(x_886);
x_888 = l_Lean_Elab_Term_tryPostponeIfMVar(x_886, x_3, x_4, x_5, x_6, x_7, x_8, x_887);
if (lean_obj_tag(x_888) == 0)
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_897; 
x_889 = lean_ctor_get(x_888, 1);
lean_inc(x_889);
if (lean_is_exclusive(x_888)) {
 lean_ctor_release(x_888, 0);
 lean_ctor_release(x_888, 1);
 x_890 = x_888;
} else {
 lean_dec_ref(x_888);
 x_890 = lean_box(0);
}
x_897 = l_Lean_Expr_getAppFn___main(x_886);
if (lean_obj_tag(x_897) == 4)
{
lean_object* x_898; lean_object* x_899; 
lean_dec(x_886);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_898 = lean_ctor_get(x_897, 0);
lean_inc(x_898);
lean_dec(x_897);
if (lean_is_scalar(x_890)) {
 x_899 = lean_alloc_ctor(0, 2, 0);
} else {
 x_899 = x_890;
}
lean_ctor_set(x_899, 0, x_898);
lean_ctor_set(x_899, 1, x_889);
return x_899;
}
else
{
lean_object* x_900; 
lean_dec(x_897);
lean_dec(x_890);
x_900 = lean_box(0);
x_891 = x_900;
goto block_896;
}
block_896:
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; 
lean_dec(x_891);
x_892 = l_Lean_indentExpr(x_886);
x_893 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_894 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_894, 0, x_893);
lean_ctor_set(x_894, 1, x_892);
x_895 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_894, x_3, x_4, x_5, x_6, x_7, x_8, x_889);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_895;
}
}
else
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; 
lean_dec(x_886);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_901 = lean_ctor_get(x_888, 0);
lean_inc(x_901);
x_902 = lean_ctor_get(x_888, 1);
lean_inc(x_902);
if (lean_is_exclusive(x_888)) {
 lean_ctor_release(x_888, 0);
 lean_ctor_release(x_888, 1);
 x_903 = x_888;
} else {
 lean_dec_ref(x_888);
 x_903 = lean_box(0);
}
if (lean_is_scalar(x_903)) {
 x_904 = lean_alloc_ctor(1, 2, 0);
} else {
 x_904 = x_903;
}
lean_ctor_set(x_904, 0, x_901);
lean_ctor_set(x_904, 1, x_902);
return x_904;
}
}
else
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_905 = lean_ctor_get(x_885, 0);
lean_inc(x_905);
x_906 = lean_ctor_get(x_885, 1);
lean_inc(x_906);
if (lean_is_exclusive(x_885)) {
 lean_ctor_release(x_885, 0);
 lean_ctor_release(x_885, 1);
 x_907 = x_885;
} else {
 lean_dec_ref(x_885);
 x_907 = lean_box(0);
}
if (lean_is_scalar(x_907)) {
 x_908 = lean_alloc_ctor(1, 2, 0);
} else {
 x_908 = x_907;
}
lean_ctor_set(x_908, 0, x_905);
lean_ctor_set(x_908, 1, x_906);
return x_908;
}
}
else
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_909 = lean_ctor_get(x_882, 0);
lean_inc(x_909);
x_910 = lean_ctor_get(x_882, 1);
lean_inc(x_910);
if (lean_is_exclusive(x_882)) {
 lean_ctor_release(x_882, 0);
 lean_ctor_release(x_882, 1);
 x_911 = x_882;
} else {
 lean_dec_ref(x_882);
 x_911 = lean_box(0);
}
if (lean_is_scalar(x_911)) {
 x_912 = lean_alloc_ctor(1, 2, 0);
} else {
 x_912 = x_911;
}
lean_ctor_set(x_912, 0, x_909);
lean_ctor_set(x_912, 1, x_910);
return x_912;
}
}
else
{
lean_object* x_913; 
lean_dec(x_2);
x_913 = lean_box(0);
x_608 = x_913;
goto block_613;
}
}
case 10:
{
lean_dec(x_614);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_914; lean_object* x_915; 
lean_dec(x_65);
x_914 = lean_ctor_get(x_2, 1);
lean_inc(x_914);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_915 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_914, x_3, x_4, x_5, x_6, x_7, x_8, x_607);
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
x_917 = lean_ctor_get(x_915, 1);
lean_inc(x_917);
lean_dec(x_915);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_918 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_916, x_3, x_4, x_5, x_6, x_7, x_8, x_917);
if (lean_obj_tag(x_918) == 0)
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; 
x_919 = lean_ctor_get(x_918, 0);
lean_inc(x_919);
x_920 = lean_ctor_get(x_918, 1);
lean_inc(x_920);
lean_dec(x_918);
lean_inc(x_919);
x_921 = l_Lean_Elab_Term_tryPostponeIfMVar(x_919, x_3, x_4, x_5, x_6, x_7, x_8, x_920);
if (lean_obj_tag(x_921) == 0)
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_930; 
x_922 = lean_ctor_get(x_921, 1);
lean_inc(x_922);
if (lean_is_exclusive(x_921)) {
 lean_ctor_release(x_921, 0);
 lean_ctor_release(x_921, 1);
 x_923 = x_921;
} else {
 lean_dec_ref(x_921);
 x_923 = lean_box(0);
}
x_930 = l_Lean_Expr_getAppFn___main(x_919);
if (lean_obj_tag(x_930) == 4)
{
lean_object* x_931; lean_object* x_932; 
lean_dec(x_919);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_931 = lean_ctor_get(x_930, 0);
lean_inc(x_931);
lean_dec(x_930);
if (lean_is_scalar(x_923)) {
 x_932 = lean_alloc_ctor(0, 2, 0);
} else {
 x_932 = x_923;
}
lean_ctor_set(x_932, 0, x_931);
lean_ctor_set(x_932, 1, x_922);
return x_932;
}
else
{
lean_object* x_933; 
lean_dec(x_930);
lean_dec(x_923);
x_933 = lean_box(0);
x_924 = x_933;
goto block_929;
}
block_929:
{
lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; 
lean_dec(x_924);
x_925 = l_Lean_indentExpr(x_919);
x_926 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_927 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_927, 0, x_926);
lean_ctor_set(x_927, 1, x_925);
x_928 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_927, x_3, x_4, x_5, x_6, x_7, x_8, x_922);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_928;
}
}
else
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; 
lean_dec(x_919);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_934 = lean_ctor_get(x_921, 0);
lean_inc(x_934);
x_935 = lean_ctor_get(x_921, 1);
lean_inc(x_935);
if (lean_is_exclusive(x_921)) {
 lean_ctor_release(x_921, 0);
 lean_ctor_release(x_921, 1);
 x_936 = x_921;
} else {
 lean_dec_ref(x_921);
 x_936 = lean_box(0);
}
if (lean_is_scalar(x_936)) {
 x_937 = lean_alloc_ctor(1, 2, 0);
} else {
 x_937 = x_936;
}
lean_ctor_set(x_937, 0, x_934);
lean_ctor_set(x_937, 1, x_935);
return x_937;
}
}
else
{
lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_938 = lean_ctor_get(x_918, 0);
lean_inc(x_938);
x_939 = lean_ctor_get(x_918, 1);
lean_inc(x_939);
if (lean_is_exclusive(x_918)) {
 lean_ctor_release(x_918, 0);
 lean_ctor_release(x_918, 1);
 x_940 = x_918;
} else {
 lean_dec_ref(x_918);
 x_940 = lean_box(0);
}
if (lean_is_scalar(x_940)) {
 x_941 = lean_alloc_ctor(1, 2, 0);
} else {
 x_941 = x_940;
}
lean_ctor_set(x_941, 0, x_938);
lean_ctor_set(x_941, 1, x_939);
return x_941;
}
}
else
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_942 = lean_ctor_get(x_915, 0);
lean_inc(x_942);
x_943 = lean_ctor_get(x_915, 1);
lean_inc(x_943);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 x_944 = x_915;
} else {
 lean_dec_ref(x_915);
 x_944 = lean_box(0);
}
if (lean_is_scalar(x_944)) {
 x_945 = lean_alloc_ctor(1, 2, 0);
} else {
 x_945 = x_944;
}
lean_ctor_set(x_945, 0, x_942);
lean_ctor_set(x_945, 1, x_943);
return x_945;
}
}
else
{
lean_object* x_946; 
lean_dec(x_2);
x_946 = lean_box(0);
x_608 = x_946;
goto block_613;
}
}
case 11:
{
lean_dec(x_614);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_947; lean_object* x_948; 
lean_dec(x_65);
x_947 = lean_ctor_get(x_2, 1);
lean_inc(x_947);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_948 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_947, x_3, x_4, x_5, x_6, x_7, x_8, x_607);
if (lean_obj_tag(x_948) == 0)
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; 
x_949 = lean_ctor_get(x_948, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_948, 1);
lean_inc(x_950);
lean_dec(x_948);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_951 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_949, x_3, x_4, x_5, x_6, x_7, x_8, x_950);
if (lean_obj_tag(x_951) == 0)
{
lean_object* x_952; lean_object* x_953; lean_object* x_954; 
x_952 = lean_ctor_get(x_951, 0);
lean_inc(x_952);
x_953 = lean_ctor_get(x_951, 1);
lean_inc(x_953);
lean_dec(x_951);
lean_inc(x_952);
x_954 = l_Lean_Elab_Term_tryPostponeIfMVar(x_952, x_3, x_4, x_5, x_6, x_7, x_8, x_953);
if (lean_obj_tag(x_954) == 0)
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_963; 
x_955 = lean_ctor_get(x_954, 1);
lean_inc(x_955);
if (lean_is_exclusive(x_954)) {
 lean_ctor_release(x_954, 0);
 lean_ctor_release(x_954, 1);
 x_956 = x_954;
} else {
 lean_dec_ref(x_954);
 x_956 = lean_box(0);
}
x_963 = l_Lean_Expr_getAppFn___main(x_952);
if (lean_obj_tag(x_963) == 4)
{
lean_object* x_964; lean_object* x_965; 
lean_dec(x_952);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_964 = lean_ctor_get(x_963, 0);
lean_inc(x_964);
lean_dec(x_963);
if (lean_is_scalar(x_956)) {
 x_965 = lean_alloc_ctor(0, 2, 0);
} else {
 x_965 = x_956;
}
lean_ctor_set(x_965, 0, x_964);
lean_ctor_set(x_965, 1, x_955);
return x_965;
}
else
{
lean_object* x_966; 
lean_dec(x_963);
lean_dec(x_956);
x_966 = lean_box(0);
x_957 = x_966;
goto block_962;
}
block_962:
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; 
lean_dec(x_957);
x_958 = l_Lean_indentExpr(x_952);
x_959 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_960 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_960, 0, x_959);
lean_ctor_set(x_960, 1, x_958);
x_961 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_960, x_3, x_4, x_5, x_6, x_7, x_8, x_955);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_961;
}
}
else
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; 
lean_dec(x_952);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_967 = lean_ctor_get(x_954, 0);
lean_inc(x_967);
x_968 = lean_ctor_get(x_954, 1);
lean_inc(x_968);
if (lean_is_exclusive(x_954)) {
 lean_ctor_release(x_954, 0);
 lean_ctor_release(x_954, 1);
 x_969 = x_954;
} else {
 lean_dec_ref(x_954);
 x_969 = lean_box(0);
}
if (lean_is_scalar(x_969)) {
 x_970 = lean_alloc_ctor(1, 2, 0);
} else {
 x_970 = x_969;
}
lean_ctor_set(x_970, 0, x_967);
lean_ctor_set(x_970, 1, x_968);
return x_970;
}
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_971 = lean_ctor_get(x_951, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_951, 1);
lean_inc(x_972);
if (lean_is_exclusive(x_951)) {
 lean_ctor_release(x_951, 0);
 lean_ctor_release(x_951, 1);
 x_973 = x_951;
} else {
 lean_dec_ref(x_951);
 x_973 = lean_box(0);
}
if (lean_is_scalar(x_973)) {
 x_974 = lean_alloc_ctor(1, 2, 0);
} else {
 x_974 = x_973;
}
lean_ctor_set(x_974, 0, x_971);
lean_ctor_set(x_974, 1, x_972);
return x_974;
}
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_975 = lean_ctor_get(x_948, 0);
lean_inc(x_975);
x_976 = lean_ctor_get(x_948, 1);
lean_inc(x_976);
if (lean_is_exclusive(x_948)) {
 lean_ctor_release(x_948, 0);
 lean_ctor_release(x_948, 1);
 x_977 = x_948;
} else {
 lean_dec_ref(x_948);
 x_977 = lean_box(0);
}
if (lean_is_scalar(x_977)) {
 x_978 = lean_alloc_ctor(1, 2, 0);
} else {
 x_978 = x_977;
}
lean_ctor_set(x_978, 0, x_975);
lean_ctor_set(x_978, 1, x_976);
return x_978;
}
}
else
{
lean_object* x_979; 
lean_dec(x_2);
x_979 = lean_box(0);
x_608 = x_979;
goto block_613;
}
}
default: 
{
lean_dec(x_614);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_980; lean_object* x_981; 
lean_dec(x_65);
x_980 = lean_ctor_get(x_2, 1);
lean_inc(x_980);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_981 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_980, x_3, x_4, x_5, x_6, x_7, x_8, x_607);
if (lean_obj_tag(x_981) == 0)
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; 
x_982 = lean_ctor_get(x_981, 0);
lean_inc(x_982);
x_983 = lean_ctor_get(x_981, 1);
lean_inc(x_983);
lean_dec(x_981);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_984 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_6__isTypeApp_x3f___spec__1(x_982, x_3, x_4, x_5, x_6, x_7, x_8, x_983);
if (lean_obj_tag(x_984) == 0)
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_985 = lean_ctor_get(x_984, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_984, 1);
lean_inc(x_986);
lean_dec(x_984);
lean_inc(x_985);
x_987 = l_Lean_Elab_Term_tryPostponeIfMVar(x_985, x_3, x_4, x_5, x_6, x_7, x_8, x_986);
if (lean_obj_tag(x_987) == 0)
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_996; 
x_988 = lean_ctor_get(x_987, 1);
lean_inc(x_988);
if (lean_is_exclusive(x_987)) {
 lean_ctor_release(x_987, 0);
 lean_ctor_release(x_987, 1);
 x_989 = x_987;
} else {
 lean_dec_ref(x_987);
 x_989 = lean_box(0);
}
x_996 = l_Lean_Expr_getAppFn___main(x_985);
if (lean_obj_tag(x_996) == 4)
{
lean_object* x_997; lean_object* x_998; 
lean_dec(x_985);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_997 = lean_ctor_get(x_996, 0);
lean_inc(x_997);
lean_dec(x_996);
if (lean_is_scalar(x_989)) {
 x_998 = lean_alloc_ctor(0, 2, 0);
} else {
 x_998 = x_989;
}
lean_ctor_set(x_998, 0, x_997);
lean_ctor_set(x_998, 1, x_988);
return x_998;
}
else
{
lean_object* x_999; 
lean_dec(x_996);
lean_dec(x_989);
x_999 = lean_box(0);
x_990 = x_999;
goto block_995;
}
block_995:
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; 
lean_dec(x_990);
x_991 = l_Lean_indentExpr(x_985);
x_992 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9;
x_993 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_993, 0, x_992);
lean_ctor_set(x_993, 1, x_991);
x_994 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_993, x_3, x_4, x_5, x_6, x_7, x_8, x_988);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_994;
}
}
else
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; 
lean_dec(x_985);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1000 = lean_ctor_get(x_987, 0);
lean_inc(x_1000);
x_1001 = lean_ctor_get(x_987, 1);
lean_inc(x_1001);
if (lean_is_exclusive(x_987)) {
 lean_ctor_release(x_987, 0);
 lean_ctor_release(x_987, 1);
 x_1002 = x_987;
} else {
 lean_dec_ref(x_987);
 x_1002 = lean_box(0);
}
if (lean_is_scalar(x_1002)) {
 x_1003 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1003 = x_1002;
}
lean_ctor_set(x_1003, 0, x_1000);
lean_ctor_set(x_1003, 1, x_1001);
return x_1003;
}
}
else
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1004 = lean_ctor_get(x_984, 0);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_984, 1);
lean_inc(x_1005);
if (lean_is_exclusive(x_984)) {
 lean_ctor_release(x_984, 0);
 lean_ctor_release(x_984, 1);
 x_1006 = x_984;
} else {
 lean_dec_ref(x_984);
 x_1006 = lean_box(0);
}
if (lean_is_scalar(x_1006)) {
 x_1007 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1007 = x_1006;
}
lean_ctor_set(x_1007, 0, x_1004);
lean_ctor_set(x_1007, 1, x_1005);
return x_1007;
}
}
else
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1008 = lean_ctor_get(x_981, 0);
lean_inc(x_1008);
x_1009 = lean_ctor_get(x_981, 1);
lean_inc(x_1009);
if (lean_is_exclusive(x_981)) {
 lean_ctor_release(x_981, 0);
 lean_ctor_release(x_981, 1);
 x_1010 = x_981;
} else {
 lean_dec_ref(x_981);
 x_1010 = lean_box(0);
}
if (lean_is_scalar(x_1010)) {
 x_1011 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1011 = x_1010;
}
lean_ctor_set(x_1011, 0, x_1008);
lean_ctor_set(x_1011, 1, x_1009);
return x_1011;
}
}
else
{
lean_object* x_1012; 
lean_dec(x_2);
x_1012 = lean_box(0);
x_608 = x_1012;
goto block_613;
}
}
}
block_613:
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_608);
x_609 = l_Lean_indentExpr(x_65);
x_610 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_611 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_611, 0, x_610);
lean_ctor_set(x_611, 1, x_609);
x_612 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_611, x_3, x_4, x_5, x_6, x_7, x_8, x_607);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_612;
}
}
}
else
{
uint8_t x_1013; 
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_1013 = !lean_is_exclusive(x_66);
if (x_1013 == 0)
{
return x_66;
}
else
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1014 = lean_ctor_get(x_66, 0);
x_1015 = lean_ctor_get(x_66, 1);
lean_inc(x_1015);
lean_inc(x_1014);
lean_dec(x_66);
x_1016 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1016, 0, x_1014);
lean_ctor_set(x_1016, 1, x_1015);
return x_1016;
}
}
}
block_20:
{
lean_dec(x_12);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3;
x_14 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_indentExpr(x_15);
x_17 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
}
}
else
{
uint8_t x_1017; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1017 = !lean_is_exclusive(x_10);
if (x_1017 == 0)
{
return x_10;
}
else
{
lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
x_1018 = lean_ctor_get(x_10, 0);
x_1019 = lean_ctor_get(x_10, 1);
lean_inc(x_1019);
lean_inc(x_1018);
lean_dec(x_10);
x_1020 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1020, 0, x_1018);
lean_ctor_set(x_1020, 1, x_1019);
return x_1020;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_5__getStructName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_5__getStructName___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_5__getStructName___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_StructInst_5__getStructName(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1() {
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
static lean_object* _init_l_Lean_Elab_Term_StructInst_FieldLHS_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_hasFormat(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_4);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Syntax_prettyPrint(x_6);
x_8 = l_Lean_Format_sbracket___closed__3;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_Format_sbracket___closed__4;
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Field_inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2;
return x_2;
}
}
uint8_t l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Field_isSimple___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Struct_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Struct_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Struct_inhabited___closed__1;
return x_1;
}
}
uint8_t l_List_foldr___main___at_Lean_Elab_Term_StructInst_Struct_allDefault___main___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___main___at_Lean_Elab_Term_StructInst_Struct_allDefault___main___spec__1(x_1, x_4);
x_6 = lean_ctor_get(x_3, 2);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
case 1:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_Elab_Term_StructInst_Struct_allDefault___main(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
return x_5;
}
}
default: 
{
return x_5;
}
}
}
}
}
uint8_t l_Lean_Elab_Term_StructInst_Struct_allDefault___main(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 1;
x_4 = l_List_foldr___main___at_Lean_Elab_Term_StructInst_Struct_allDefault___main___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___main___at_Lean_Elab_Term_StructInst_Struct_allDefault___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___main___at_Lean_Elab_Term_StructInst_Struct_allDefault___main___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_allDefault___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Elab_Term_StructInst_Struct_allDefault(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_allDefault___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_allDefault(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_source(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_source___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Format_joinSep___main___at_Lean_Elab_Term_StructInst_formatField___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Lean_Syntax_prettyPrint(x_10);
x_12 = l_Lean_Format_sbracket___closed__3;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Format_sbracket___closed__4;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_2);
x_17 = l_Lean_Format_joinSep___main___at_Lean_Elab_Term_StructInst_formatField___spec__1(x_4, x_2);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
case 1:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
default: 
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = l_Lean_Syntax_prettyPrint(x_26);
x_28 = l_Lean_Format_sbracket___closed__3;
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Format_sbracket___closed__4;
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_2);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_17);
return x_33;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatField___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" . ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatField___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_formatField___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatField___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<default>");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatField___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_formatField___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_formatField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Elab_Term_StructInst_formatField___closed__2;
x_5 = l_Lean_Format_joinSep___main___at_Lean_Elab_Term_StructInst_formatField___spec__1(x_3, x_4);
x_6 = l_Lean_formatEntry___closed__2;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Syntax_prettyPrint(x_9);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_apply_1(x_1, x_12);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = l_Lean_Elab_Term_StructInst_formatField___closed__4;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_formatStruct___main), 1, 0);
return x_1;
}
}
lean_object* l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1;
x_7 = l_Lean_Elab_Term_StructInst_formatField(x_6, x_4);
x_8 = l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1(x_5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1;
x_12 = l_Lean_Elab_Term_StructInst_formatField(x_11, x_9);
x_13 = l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_addParenHeuristic___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__28;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" .. }");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Binders_17__expandMatchAltsIntoMatchAux___main___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1(x_2);
x_5 = l_Lean_formatKVMap___closed__1;
x_6 = l_Lean_Format_joinSep___main___at___private_Lean_Data_Trie_6__toStringAux___main___spec__1(x_4, x_5);
lean_dec(x_4);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_11 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
x_13 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__4;
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_expr_dbg_to_string(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__5;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
x_23 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2;
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_formatStruct(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_formatStruct___main(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_formatStruct), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Struct_hasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Struct_hasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_formatField), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Field_hasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Field_hasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_System_FilePath_dirName___closed__1;
x_6 = l_Lean_mkAtomFrom(x_3, x_5);
x_7 = l_Lean_mkIdentFrom(x_3, x_4);
lean_dec(x_3);
x_8 = l_Lean_mkAppStx___closed__9;
x_9 = lean_array_push(x_8, x_6);
x_10 = lean_array_push(x_9, x_7);
x_11 = l_Lean_nullKind;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_mkIdentFrom(x_13, x_14);
lean_dec(x_13);
return x_15;
}
}
case 1:
{
if (x_1 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_System_FilePath_dirName___closed__1;
x_18 = l_Lean_mkAtomFrom(x_16, x_17);
x_19 = l_Lean_mkAppStx___closed__9;
x_20 = lean_array_push(x_19, x_18);
x_21 = lean_array_push(x_20, x_16);
x_22 = l_Lean_nullKind;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
lean_dec(x_2);
return x_24;
}
}
default: 
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
lean_dec(x_2);
return x_25;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_inhabited;
x_4 = l_unreachable_x21___rarg(x_3);
return x_4;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = 0;
x_11 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(x_10, x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_8, x_1, x_14);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = l_Lean_Syntax_inhabited;
x_4 = l_unreachable_x21___rarg(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_setArg(x_7, x_10, x_9);
x_12 = 1;
x_13 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(x_12, x_5);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_setArg(x_11, x_14, x_13);
x_16 = l_List_redLength___main___rarg(x_6);
x_17 = lean_mk_empty_array_with_capacity(x_16);
lean_dec(x_16);
x_18 = l_List_toArrayAux___main___rarg(x_6, x_17);
x_19 = x_18;
x_20 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(x_14, x_19);
x_21 = x_20;
x_22 = l_Lean_nullKind;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Syntax_setArg(x_15, x_24, x_23);
return x_25;
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected structure syntax");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_6__toFieldLHS(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2;
x_4 = lean_name_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_nullKind;
x_6 = lean_name_eq(x_2, x_5);
lean_dec(x_2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Lean_Syntax_isIdent(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_fieldIdxKind;
x_9 = l_Lean_Syntax_isNatLitAux(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__2;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Syntax_getId(x_1);
x_15 = l_Lean_Name_eraseMacroScopes(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = l_Lean_Syntax_isIdent(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_fieldIdxKind;
x_22 = l_Lean_Syntax_isNatLitAux(x_21, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_19);
x_23 = l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__2;
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_Syntax_getId(x_19);
x_28 = l_Lean_Name_eraseMacroScopes(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_31 = lean_unsigned_to_nat(1u);
x_32 = l_Lean_Syntax_getArg(x_1, x_31);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = l_Array_shrink___main___rarg(x_1, x_3);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = l_Lean_Syntax_getKind(x_7);
x_9 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__8;
x_10 = lean_name_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_2);
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_17 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_fswap(x_1, x_2, x_3);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
lean_dec(x_2);
x_22 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_1 = x_19;
x_2 = x_21;
x_3 = x_22;
goto _start;
}
}
}
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2___closed__1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l___private_Lean_Elab_StructInst_6__toFieldLHS(x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_free_object(x_1);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2(x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_10);
lean_free_object(x_1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_10);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_10);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = l___private_Lean_Elab_StructInst_6__toFieldLHS(x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2(x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 1, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_31 = x_26;
} else {
 lean_dec_ref(x_26);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_30);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2___closed__1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(3u);
x_7 = l_Lean_Syntax_getArg(x_4, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_4, x_8);
x_10 = l___private_Lean_Elab_StructInst_6__toFieldLHS(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_free_object(x_1);
lean_dec(x_5);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_4, x_15);
x_17 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
x_18 = l_Array_toList___rarg(x_17);
lean_dec(x_17);
x_19 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2(x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_7);
lean_free_object(x_1);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set(x_1, 0, x_14);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_7);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_1);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_25);
x_27 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__3(x_5);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_27, 0, x_33);
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_unsigned_to_nat(3u);
x_40 = l_Lean_Syntax_getArg(x_37, x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lean_Syntax_getArg(x_37, x_41);
x_43 = l___private_Lean_Elab_StructInst_6__toFieldLHS(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_unsigned_to_nat(1u);
x_49 = l_Lean_Syntax_getArg(x_37, x_48);
x_50 = l_Lean_Syntax_getArgs(x_49);
lean_dec(x_49);
x_51 = l_Array_toList___rarg(x_50);
lean_dec(x_50);
x_52 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_53);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_40);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_37);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set(x_60, 3, x_59);
x_61 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__3(x_38);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 1, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_66 = x_61;
} else {
 lean_dec_ref(x_61);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_65);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_7__mkStructView(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1(x_6, x_7, x_7);
x_9 = l_Array_toList___rarg(x_8);
lean_dec(x_8);
x_10 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__3(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_3);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_3);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_4);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_apply_1(x_3, x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg___lambda__1), 5, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_7);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_apply_1(x_2, x_4);
lean_ctor_set(x_1, 2, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_10 = lean_apply_1(x_2, x_8);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set(x_11, 3, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFields(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_setFields(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_fix1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_3);
return x_4;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__2(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_13 = x_7;
} else {
 lean_dec_ref(x_7);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_24; 
lean_dec(x_23);
lean_free_object(x_1);
lean_dec(x_4);
x_24 = lean_box(0);
x_16 = x_24;
goto block_22;
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
block_22:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
x_17 = l_Lean_Name_components(x_15);
x_18 = l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(x_14, x_17);
x_19 = l_List_append___rarg(x_18, x_12);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_10);
lean_ctor_set(x_20, 3, x_11);
if (lean_is_scalar(x_13)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_13;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_free_object(x_1);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_7, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_7, 0);
lean_dec(x_27);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_28; 
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_1);
x_31 = l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__2(x_30);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 3);
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
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
if (lean_obj_tag(x_41) == 1)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_29);
lean_ctor_set(x_50, 1, x_31);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_49);
lean_dec(x_29);
x_51 = lean_box(0);
x_42 = x_51;
goto block_48;
}
}
else
{
lean_object* x_52; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_29);
lean_ctor_set(x_52, 1, x_31);
return x_52;
}
block_48:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_42);
x_43 = l_Lean_Name_components(x_41);
x_44 = l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(x_40, x_43);
x_45 = l_List_append___rarg(x_44, x_38);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_36);
lean_ctor_set(x_46, 3, x_37);
if (lean_is_scalar(x_39)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_39;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_31);
return x_47;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_53 = x_32;
} else {
 lean_dec_ref(x_32);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_29);
lean_ctor_set(x_54, 1, x_31);
return x_54;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_8__expandCompositeFields___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__2), 1, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_StructInst_8__expandCompositeFields(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_StructInst_8__expandCompositeFields___closed__1;
x_3 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field index, structure has only #");
return x_1;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" fields");
return x_1;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field index, index must be greater than 0");
return x_1;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_30; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_14 = x_2;
} else {
 lean_dec_ref(x_2);
 x_14 = lean_box(0);
}
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 1)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_ctor_get(x_12, 2);
x_35 = lean_ctor_get(x_12, 3);
x_36 = lean_ctor_get(x_12, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_30, 1);
x_39 = lean_ctor_get(x_30, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_ctor_get(x_31, 1);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_array_get_size(x_1);
x_46 = lean_nat_dec_lt(x_45, x_42);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_42, x_47);
lean_dec(x_42);
x_49 = l_Lean_Name_inhabited;
x_50 = lean_array_get(x_49, x_1, x_48);
lean_dec(x_48);
lean_ctor_set_tag(x_31, 0);
lean_ctor_set(x_31, 1, x_50);
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_free_object(x_31);
lean_dec(x_42);
lean_free_object(x_30);
lean_dec(x_38);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_51 = l_Nat_repr(x_45);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_41, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_41);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_free_object(x_31);
lean_dec(x_42);
lean_free_object(x_30);
lean_dec(x_38);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_63 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
x_64 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_41, x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_41);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
return x_64;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_31, 0);
x_70 = lean_ctor_get(x_31, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_31);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_dec_eq(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_array_get_size(x_1);
x_74 = lean_nat_dec_lt(x_73, x_70);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_73);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_sub(x_70, x_75);
lean_dec(x_70);
x_77 = l_Lean_Name_inhabited;
x_78 = lean_array_get(x_77, x_1, x_76);
lean_dec(x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_30, 0, x_79);
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_70);
lean_free_object(x_30);
lean_dec(x_38);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_80 = l_Nat_repr(x_73);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
x_86 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_69, x_86, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_69);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_70);
lean_free_object(x_30);
lean_dec(x_38);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_92 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
x_93 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_69, x_92, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_69);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_98 = lean_ctor_get(x_30, 1);
lean_inc(x_98);
lean_dec(x_30);
x_99 = lean_ctor_get(x_31, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_31, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_101 = x_31;
} else {
 lean_dec_ref(x_31);
 x_101 = lean_box(0);
}
x_102 = lean_unsigned_to_nat(0u);
x_103 = lean_nat_dec_eq(x_100, x_102);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_array_get_size(x_1);
x_105 = lean_nat_dec_lt(x_104, x_100);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_104);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_sub(x_100, x_106);
lean_dec(x_100);
x_108 = l_Lean_Name_inhabited;
x_109 = lean_array_get(x_108, x_1, x_107);
lean_dec(x_107);
if (lean_is_scalar(x_101)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_101;
 lean_ctor_set_tag(x_110, 0);
}
lean_ctor_set(x_110, 0, x_99);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_98);
lean_ctor_set(x_12, 1, x_111);
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_98);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_112 = l_Nat_repr(x_104);
x_113 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
x_116 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
x_118 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_99, x_118, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_99);
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
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_98);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_124 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
x_125 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_99, x_124, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_99);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_130 = lean_ctor_get(x_12, 0);
x_131 = lean_ctor_get(x_12, 2);
x_132 = lean_ctor_get(x_12, 3);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_12);
x_133 = lean_ctor_get(x_30, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_134 = x_30;
} else {
 lean_dec_ref(x_30);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get(x_31, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_31, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_137 = x_31;
} else {
 lean_dec_ref(x_31);
 x_137 = lean_box(0);
}
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_nat_dec_eq(x_136, x_138);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_array_get_size(x_1);
x_141 = lean_nat_dec_lt(x_140, x_136);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_140);
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_nat_sub(x_136, x_142);
lean_dec(x_136);
x_144 = l_Lean_Name_inhabited;
x_145 = lean_array_get(x_144, x_1, x_143);
lean_dec(x_143);
if (lean_is_scalar(x_137)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_137;
 lean_ctor_set_tag(x_146, 0);
}
lean_ctor_set(x_146, 0, x_135);
lean_ctor_set(x_146, 1, x_145);
if (lean_is_scalar(x_134)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_134;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_133);
x_148 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_148, 0, x_130);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_148, 2, x_131);
lean_ctor_set(x_148, 3, x_132);
x_15 = x_148;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_14);
lean_dec(x_13);
x_149 = l_Nat_repr(x_140);
x_150 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_152 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
x_153 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
x_155 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_135, x_155, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_135);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_14);
lean_dec(x_13);
x_161 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
x_162 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_135, x_161, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_135);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_165 = x_162;
} else {
 lean_dec_ref(x_162);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_30);
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
}
block_29:
{
lean_object* x_17; 
x_17 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(1, 2, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
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
if (lean_is_scalar(x_14)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_14;
}
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_14);
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
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_apply_8(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_1, 2, x_17);
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
lean_ctor_set(x_1, 2, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_free_object(x_1);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 2);
x_28 = lean_ctor_get(x_1, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_29 = lean_apply_8(x_2, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_28);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_37 = x_29;
} else {
 lean_dec_ref(x_29);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
x_15 = l_Lean_getStructureFields(x_13, x_14);
x_16 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_15);
return x_16;
}
}
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1___boxed), 9, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__1(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = l_List_map___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__1(x_1, x_6);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = lean_name_mk_string(x_9, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_1);
x_12 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_13 = l_unreachable_x21___rarg(x_12);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
lean_inc(x_1);
x_16 = l_List_map___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__1(x_1, x_15);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = lean_name_mk_string(x_18, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
lean_dec(x_1);
x_22 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_23 = l_unreachable_x21___rarg(x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
return x_24;
}
}
}
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a field of structure '");
return x_1;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to access field '");
return x_1;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' in parent structure");
return x_1;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_31; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_15 = x_3;
} else {
 lean_dec_ref(x_3);
 x_15 = lean_box(0);
}
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
x_16 = x_13;
x_17 = x_10;
goto block_30;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_13, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_13, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_38);
lean_inc(x_2);
x_39 = l_Lean_findField_x3f___main(x_2, x_38, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
x_40 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_41 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_38);
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
x_48 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_36, x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_36);
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
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_39, 0);
lean_inc(x_53);
lean_dec(x_39);
x_54 = lean_name_eq(x_53, x_38);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_13);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_13, 3);
lean_dec(x_56);
x_57 = lean_ctor_get(x_13, 2);
lean_dec(x_57);
x_58 = lean_ctor_get(x_13, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_13, 0);
lean_dec(x_59);
lean_inc(x_2);
x_60 = l_Lean_getPathToBaseStructure_x3f(x_2, x_53, x_38);
lean_dec(x_53);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_free_object(x_13);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_61 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_61, 0, x_37);
x_62 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_36, x_65, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_36);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
return x_66;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_37);
x_71 = lean_ctor_get(x_60, 0);
lean_inc(x_71);
lean_dec(x_60);
x_72 = l_List_map___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__1(x_36, x_71);
x_73 = l_List_append___rarg(x_72, x_31);
lean_ctor_set(x_13, 1, x_73);
x_16 = x_13;
x_17 = x_10;
goto block_30;
}
}
else
{
lean_object* x_74; 
lean_dec(x_13);
lean_inc(x_2);
x_74 = l_Lean_getPathToBaseStructure_x3f(x_2, x_53, x_38);
lean_dec(x_53);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_75 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_75, 0, x_37);
x_76 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_36, x_79, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_36);
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
lean_dec(x_37);
x_85 = lean_ctor_get(x_74, 0);
lean_inc(x_85);
lean_dec(x_74);
x_86 = l_List_map___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__1(x_36, x_85);
x_87 = l_List_append___rarg(x_86, x_31);
x_88 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_88, 0, x_33);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_34);
lean_ctor_set(x_88, 3, x_35);
x_16 = x_88;
x_17 = x_10;
goto block_30;
}
}
}
else
{
lean_dec(x_53);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
x_16 = x_13;
x_17 = x_10;
goto block_30;
}
}
}
else
{
lean_dec(x_32);
lean_dec(x_31);
x_16 = x_13;
x_17 = x_10;
goto block_30;
}
}
block_30:
{
lean_object* x_18; 
x_18 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
if (lean_is_scalar(x_15)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_15;
}
lean_ctor_set(x_21, 0, x_16);
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
if (lean_is_scalar(x_15)) {
 x_24 = lean_alloc_ctor(1, 2, 0);
} else {
 x_24 = x_15;
}
lean_ctor_set(x_24, 0, x_16);
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
lean_dec(x_16);
lean_dec(x_15);
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
}
lean_object* l___private_Lean_Elab_StructInst_10__expandParentFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___boxed), 10, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_14;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_Std_AssocList_contains___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
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
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Name_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_Std_HashMapImp_moveEntries___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__7(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_HashMapImp_moveEntries___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_AssocList_replace___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__8(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_AssocList_replace___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__8(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Std_AssocList_contains___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__4(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__5(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_Std_AssocList_replace___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__8(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Name_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_Std_AssocList_contains___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__4(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__5(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_Std_AssocList_replace___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__8(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Std_mkHashMap___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("field '");
return x_1;
}
}
static lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already beed specified");
return x_1;
}
}
static lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_15 = l_unreachable_x21___rarg(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = lean_apply_7(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_1 = x_17;
x_2 = x_13;
x_9 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_dec(x_26);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1(x_1, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
lean_ctor_set(x_12, 1, x_30);
lean_ctor_set(x_12, 0, x_11);
x_31 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_28, x_12);
x_1 = x_31;
x_2 = x_27;
goto _start;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_ctor_set(x_12, 1, x_33);
lean_ctor_set(x_12, 0, x_11);
x_34 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_28, x_12);
x_1 = x_34;
x_2 = x_27;
goto _start;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
x_37 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_11);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_36);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
lean_ctor_set(x_12, 1, x_33);
lean_ctor_set(x_12, 0, x_11);
x_39 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_28, x_12);
x_1 = x_39;
x_2 = x_27;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_33);
lean_dec(x_27);
lean_free_object(x_12);
lean_dec(x_1);
x_41 = lean_ctor_get(x_11, 0);
lean_inc(x_41);
lean_dec(x_11);
x_42 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_42, 0, x_28);
x_43 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_41, x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_41);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_27);
lean_free_object(x_12);
lean_dec(x_1);
x_52 = lean_ctor_get(x_11, 0);
lean_inc(x_52);
lean_dec(x_11);
x_53 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_53, 0, x_28);
x_54 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_52, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_52);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_12);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_1);
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
lean_dec(x_2);
x_64 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_65 = l_unreachable_x21___rarg(x_64);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_66 = lean_apply_7(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_1 = x_67;
x_2 = x_63;
x_9 = x_68;
goto _start;
}
else
{
uint8_t x_70; 
lean_dec(x_63);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_66, 0);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_66);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_12, 0);
lean_inc(x_74);
lean_dec(x_12);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_2, 1);
lean_inc(x_75);
lean_dec(x_2);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1(x_1, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_11);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_76, x_79);
x_1 = x_80;
x_2 = x_75;
goto _start;
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
lean_dec(x_77);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_11);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_76, x_83);
x_1 = x_84;
x_2 = x_75;
goto _start;
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
x_87 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_11);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_86);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_11);
lean_ctor_set(x_89, 1, x_82);
x_90 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_76, x_89);
x_1 = x_90;
x_2 = x_75;
goto _start;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_82);
lean_dec(x_75);
lean_dec(x_1);
x_92 = lean_ctor_get(x_11, 0);
lean_inc(x_92);
lean_dec(x_11);
x_93 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_93, 0, x_76);
x_94 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_95 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
x_97 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_92, x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_92);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
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
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_86);
lean_dec(x_82);
lean_dec(x_75);
lean_dec(x_1);
x_103 = lean_ctor_get(x_11, 0);
lean_inc(x_103);
lean_dec(x_11);
x_104 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_104, 0, x_76);
x_105 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_106 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_103, x_108, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_103);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
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
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_74);
lean_dec(x_11);
lean_dec(x_1);
x_114 = lean_ctor_get(x_2, 1);
lean_inc(x_114);
lean_dec(x_2);
x_115 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_116 = l_unreachable_x21___rarg(x_115);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_117 = lean_apply_7(x_116, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_1 = x_118;
x_2 = x_114;
x_9 = x_119;
goto _start;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_121 = lean_ctor_get(x_117, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_123 = x_117;
} else {
 lean_dec_ref(x_117);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_12__mkFieldMap___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_12__mkFieldMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_StructInst_12__mkFieldMap___closed__1;
x_10 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_contains___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_StructInst_13__isSimpleField_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_13__isSimpleField_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_StructInst_13__isSimpleField_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_StructInst_14__getFieldIdx___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a valid field of '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_findIdxAux___main___at___private_Lean_Elab_StructInst_14__getFieldIdx___spec__1(x_3, x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_3);
x_14 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__3;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_1);
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_StructInst_14__getFieldIdx___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_StructInst_14__getFieldIdx___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_StructInst_14__getFieldIdx(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_StructInst_15__mkProjStx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_System_FilePath_dirName___closed__1;
x_4 = l_Lean_mkAtomFrom(x_1, x_3);
x_5 = l_Lean_mkIdentFrom(x_1, x_2);
x_6 = l___private_Lean_Elab_Term_5__tryCoe___closed__3;
x_7 = lean_array_push(x_6, x_1);
x_8 = lean_array_push(x_7, x_4);
x_9 = lean_array_push(x_8, x_5);
x_10 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__9;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
lean_object* l___private_Lean_Elab_StructInst_16__mkSubstructSource(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 2)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_3);
lean_inc(x_1);
x_15 = l___private_Lean_Elab_StructInst_14__getFieldIdx(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_mkProj(x_1, x_17, x_14);
if (lean_obj_tag(x_13) == 1)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_array_get_size(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_21);
lean_dec(x_21);
if (x_23 == 0)
{
lean_dec(x_3);
lean_ctor_set(x_4, 1, x_18);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_array_fget(x_20, x_22);
x_25 = lean_box(0);
x_26 = lean_array_fset(x_20, x_22, x_25);
x_27 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_24, x_3);
x_28 = lean_array_fset(x_26, x_22, x_27);
lean_ctor_set(x_13, 1, x_28);
lean_ctor_set(x_4, 1, x_18);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_array_get_size(x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_31);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_3);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_4, 1, x_18);
lean_ctor_set(x_4, 0, x_34);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_array_fget(x_30, x_32);
x_36 = lean_box(0);
x_37 = lean_array_fset(x_30, x_32, x_36);
x_38 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_35, x_3);
x_39 = lean_array_fset(x_37, x_32, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_4, 1, x_18);
lean_ctor_set(x_4, 0, x_40);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
}
else
{
lean_dec(x_3);
lean_ctor_set(x_4, 1, x_18);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
x_43 = l_Lean_mkProj(x_1, x_41, x_14);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_13, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_46 = x_13;
} else {
 lean_dec_ref(x_13);
 x_46 = lean_box(0);
}
x_47 = lean_array_get_size(x_45);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_lt(x_48, x_47);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_3);
if (lean_is_scalar(x_46)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_46;
}
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_45);
lean_ctor_set(x_4, 1, x_43);
lean_ctor_set(x_4, 0, x_50);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_42);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_array_fget(x_45, x_48);
x_53 = lean_box(0);
x_54 = lean_array_fset(x_45, x_48, x_53);
x_55 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_52, x_3);
x_56 = lean_array_fset(x_54, x_48, x_55);
if (lean_is_scalar(x_46)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_46;
}
lean_ctor_set(x_57, 0, x_44);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_4, 1, x_43);
lean_ctor_set(x_4, 0, x_57);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_4);
lean_ctor_set(x_58, 1, x_42);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec(x_3);
lean_ctor_set(x_4, 1, x_43);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_42);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_15);
if (x_60 == 0)
{
return x_15;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get(x_4, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_66 = l___private_Lean_Elab_StructInst_14__getFieldIdx(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = l_Lean_mkProj(x_1, x_67, x_65);
if (lean_obj_tag(x_64) == 1)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_73 = x_64;
} else {
 lean_dec_ref(x_64);
 x_73 = lean_box(0);
}
x_74 = lean_array_get_size(x_72);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_nat_dec_lt(x_75, x_74);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_3);
if (lean_is_scalar(x_73)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_73;
}
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_72);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_70);
if (lean_is_scalar(x_69)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_69;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_68);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_80 = lean_array_fget(x_72, x_75);
x_81 = lean_box(0);
x_82 = lean_array_fset(x_72, x_75, x_81);
x_83 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_80, x_3);
x_84 = lean_array_fset(x_82, x_75, x_83);
if (lean_is_scalar(x_73)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_73;
}
lean_ctor_set(x_85, 0, x_71);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_70);
if (lean_is_scalar(x_69)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_69;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_68);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_3);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_64);
lean_ctor_set(x_88, 1, x_70);
if (lean_is_scalar(x_69)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_69;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_68);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_3);
lean_dec(x_1);
x_90 = lean_ctor_get(x_66, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_66, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_92 = x_66;
} else {
 lean_dec_ref(x_66);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
else
{
lean_object* x_94; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_4);
lean_ctor_set(x_94, 1, x_11);
return x_94;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_16__mkSubstructSource___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_List_tail_x21___rarg(x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = l_List_tail_x21___rarg(x_6);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_8);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_Field_toSyntax(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_17__groupFields___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Field_inhabited(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_17__groupFields___lambda__2___boxed), 2, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l___private_Lean_Elab_StructInst_13__isSimpleField_x3f(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1;
lean_inc(x_16);
x_19 = l_List_map___main___rarg(x_18, x_16);
x_20 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_8);
lean_inc(x_15);
lean_inc(x_2);
x_21 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_2, x_3, x_15, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2;
x_26 = l_List_head_x21___rarg(x_25, x_16);
lean_dec(x_16);
x_27 = l_Lean_isSubobjectField_x3f(x_4, x_2, x_15);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_28 = lean_unsigned_to_nat(4u);
x_29 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_5);
x_30 = l_Lean_Syntax_setArg(x_5, x_28, x_29);
x_31 = l_List_redLength___main___rarg(x_19);
x_32 = lean_mk_empty_array_with_capacity(x_31);
lean_dec(x_31);
x_33 = l_List_toArrayAux___main___rarg(x_19, x_32);
x_34 = x_33;
x_35 = l_Id_Monad;
x_36 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3;
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Array_umapMAux___main___rarg(x_35, lean_box(0), x_36, x_37, x_34);
x_39 = x_38;
x_40 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_530____closed__8;
x_41 = l_Lean_mkAtomFrom(x_5, x_40);
lean_dec(x_5);
x_42 = l_Lean_mkSepStx(x_39, x_41);
lean_dec(x_39);
x_43 = lean_unsigned_to_nat(2u);
x_44 = l_Lean_Syntax_setArg(x_30, x_43, x_42);
x_45 = l_Lean_Elab_Term_StructInst_setStructSourceSyntax(x_44, x_23);
x_46 = !lean_is_exclusive(x_26);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_26, 1);
x_48 = lean_ctor_get(x_26, 2);
lean_dec(x_48);
x_49 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_50 = l_List_head_x21___rarg(x_49, x_47);
lean_dec(x_47);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_26, 2, x_53);
lean_ctor_set(x_26, 1, x_52);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_26, 0);
x_55 = lean_ctor_get(x_26, 1);
x_56 = lean_ctor_get(x_26, 3);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_26);
x_57 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_58 = l_List_head_x21___rarg(x_57, x_55);
lean_dec(x_55);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_45);
x_62 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_62, 0, x_54);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_56);
lean_ctor_set(x_21, 0, x_62);
return x_21;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_free_object(x_21);
x_63 = lean_ctor_get(x_27, 0);
lean_inc(x_63);
lean_dec(x_27);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_5);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_19);
lean_ctor_set(x_64, 3, x_23);
x_65 = lean_apply_8(x_6, x_64, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_26);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_ctor_get(x_26, 1);
x_70 = lean_ctor_get(x_26, 2);
lean_dec(x_70);
x_71 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_72 = l_List_head_x21___rarg(x_71, x_69);
lean_dec(x_69);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_26, 2, x_75);
lean_ctor_set(x_26, 1, x_74);
lean_ctor_set(x_65, 0, x_26);
return x_65;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_76 = lean_ctor_get(x_65, 0);
x_77 = lean_ctor_get(x_26, 0);
x_78 = lean_ctor_get(x_26, 1);
x_79 = lean_ctor_get(x_26, 3);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_26);
x_80 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_81 = l_List_head_x21___rarg(x_80, x_78);
lean_dec(x_78);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_76);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_83);
lean_ctor_set(x_85, 2, x_84);
lean_ctor_set(x_85, 3, x_79);
lean_ctor_set(x_65, 0, x_85);
return x_65;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_86 = lean_ctor_get(x_65, 0);
x_87 = lean_ctor_get(x_65, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_65);
x_88 = lean_ctor_get(x_26, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_26, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_26, 3);
lean_inc(x_90);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 x_91 = x_26;
} else {
 lean_dec_ref(x_26);
 x_91 = lean_box(0);
}
x_92 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_93 = l_List_head_x21___rarg(x_92, x_89);
lean_dec(x_89);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_86);
if (lean_is_scalar(x_91)) {
 x_97 = lean_alloc_ctor(0, 4, 0);
} else {
 x_97 = x_91;
}
lean_ctor_set(x_97, 0, x_88);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_97, 2, x_96);
lean_ctor_set(x_97, 3, x_90);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_87);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_26);
x_99 = !lean_is_exclusive(x_65);
if (x_99 == 0)
{
return x_65;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_65, 0);
x_101 = lean_ctor_get(x_65, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_65);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_21, 0);
x_104 = lean_ctor_get(x_21, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_21);
x_105 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2;
x_106 = l_List_head_x21___rarg(x_105, x_16);
lean_dec(x_16);
x_107 = l_Lean_isSubobjectField_x3f(x_4, x_2, x_15);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_108 = lean_unsigned_to_nat(4u);
x_109 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_5);
x_110 = l_Lean_Syntax_setArg(x_5, x_108, x_109);
x_111 = l_List_redLength___main___rarg(x_19);
x_112 = lean_mk_empty_array_with_capacity(x_111);
lean_dec(x_111);
x_113 = l_List_toArrayAux___main___rarg(x_19, x_112);
x_114 = x_113;
x_115 = l_Id_Monad;
x_116 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3;
x_117 = lean_unsigned_to_nat(0u);
x_118 = l_Array_umapMAux___main___rarg(x_115, lean_box(0), x_116, x_117, x_114);
x_119 = x_118;
x_120 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_530____closed__8;
x_121 = l_Lean_mkAtomFrom(x_5, x_120);
lean_dec(x_5);
x_122 = l_Lean_mkSepStx(x_119, x_121);
lean_dec(x_119);
x_123 = lean_unsigned_to_nat(2u);
x_124 = l_Lean_Syntax_setArg(x_110, x_123, x_122);
x_125 = l_Lean_Elab_Term_StructInst_setStructSourceSyntax(x_124, x_103);
x_126 = lean_ctor_get(x_106, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_106, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_106, 3);
lean_inc(x_128);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 x_129 = x_106;
} else {
 lean_dec_ref(x_106);
 x_129 = lean_box(0);
}
x_130 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_131 = l_List_head_x21___rarg(x_130, x_127);
lean_dec(x_127);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_125);
if (lean_is_scalar(x_129)) {
 x_135 = lean_alloc_ctor(0, 4, 0);
} else {
 x_135 = x_129;
}
lean_ctor_set(x_135, 0, x_126);
lean_ctor_set(x_135, 1, x_133);
lean_ctor_set(x_135, 2, x_134);
lean_ctor_set(x_135, 3, x_128);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_104);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_107, 0);
lean_inc(x_137);
lean_dec(x_107);
x_138 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_138, 0, x_5);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_138, 2, x_19);
lean_ctor_set(x_138, 3, x_103);
x_139 = lean_apply_8(x_6, x_138, x_8, x_9, x_10, x_11, x_12, x_13, x_104);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_106, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_106, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_106, 3);
lean_inc(x_145);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 x_146 = x_106;
} else {
 lean_dec_ref(x_106);
 x_146 = lean_box(0);
}
x_147 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_148 = l_List_head_x21___rarg(x_147, x_144);
lean_dec(x_144);
x_149 = lean_box(0);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_140);
if (lean_is_scalar(x_146)) {
 x_152 = lean_alloc_ctor(0, 4, 0);
} else {
 x_152 = x_146;
}
lean_ctor_set(x_152, 0, x_143);
lean_ctor_set(x_152, 1, x_150);
lean_ctor_set(x_152, 2, x_151);
lean_ctor_set(x_152, 3, x_145);
if (lean_is_scalar(x_142)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_142;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_141);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_106);
x_154 = lean_ctor_get(x_139, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_139, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_156 = x_139;
} else {
 lean_dec_ref(x_139);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_21);
if (x_158 == 0)
{
return x_21;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_21, 0);
x_160 = lean_ctor_get(x_21, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_21);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_162 = lean_ctor_get(x_17, 0);
lean_inc(x_162);
lean_dec(x_17);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_14);
return x_163;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l___private_Lean_Elab_StructInst_12__mkFieldMap(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___boxed), 14, 6);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_6);
x_20 = l_Std_HashMap_toList___rarg(x_17);
lean_dec(x_17);
x_21 = l_List_mapM___main___rarg(x_7, lean_box(0), lean_box(0), x_19, x_20);
x_22 = lean_apply_7(x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_14);
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
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_StructInst_Struct_structName(x_2);
lean_inc(x_14);
lean_inc(x_13);
x_15 = l_Lean_getStructureFields(x_13, x_14);
x_16 = l_Lean_Elab_Term_StructInst_Struct_ref(x_2);
x_17 = l_Lean_Meta_CheckAssignment_checkFVar___closed__1;
lean_inc(x_16);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_17__groupFields___lambda__4), 15, 7);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_14);
lean_closure_set(x_18, 2, x_15);
lean_closure_set(x_18, 3, x_13);
lean_closure_set(x_18, 4, x_16);
lean_closure_set(x_18, 5, x_1);
lean_closure_set(x_18, 6, x_17);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_7, 3);
x_21 = l_Lean_replaceRef(x_16, x_20);
lean_dec(x_16);
x_22 = l_Lean_replaceRef(x_21, x_20);
lean_dec(x_21);
x_23 = l_Lean_replaceRef(x_22, x_20);
lean_dec(x_20);
lean_dec(x_22);
lean_ctor_set(x_7, 3, x_23);
x_24 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(x_17, x_2, x_18);
x_25 = lean_apply_7(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
x_28 = lean_ctor_get(x_7, 2);
x_29 = lean_ctor_get(x_7, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_30 = l_Lean_replaceRef(x_16, x_29);
lean_dec(x_16);
x_31 = l_Lean_replaceRef(x_30, x_29);
lean_dec(x_30);
x_32 = l_Lean_replaceRef(x_31, x_29);
lean_dec(x_29);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_32);
x_34 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(x_17, x_2, x_18);
x_35 = lean_apply_7(x_34, x_3, x_4, x_5, x_6, x_33, x_8, x_12);
return x_35;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
uint8_t l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_name_eq(x_7, x_1);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_findField_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_List_find_x3f___main___rarg(x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_inc(x_9);
x_19 = l_Lean_Elab_Term_StructInst_findField_x3f(x_18, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_inc(x_9);
lean_inc(x_3);
x_20 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_3);
x_21 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
switch (lean_obj_tag(x_21)) {
case 0:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_box(2);
lean_inc(x_4);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_9);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_10);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_17);
return x_28;
}
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_21);
x_29 = l_Lean_mkHole(x_4);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_inc(x_4);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_9);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_30);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_10);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_17);
return x_36;
}
default: 
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_21, 0);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_Syntax_getArg(x_37, x_38);
lean_dec(x_37);
lean_inc(x_9);
x_40 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_39, x_9);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_inc(x_4);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_9);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_5);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_41);
lean_ctor_set(x_45, 3, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_10);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_17);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_20, 0);
lean_inc(x_48);
lean_dec(x_20);
x_49 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_11);
lean_inc(x_9);
x_50 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_3, x_6, x_9, x_49, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_5);
lean_inc(x_4);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_4);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_5);
lean_ctor_set(x_53, 3, x_51);
x_54 = lean_apply_8(x_7, x_53, x_11, x_12, x_13, x_14, x_15, x_16, x_52);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_inc(x_4);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_4);
lean_ctor_set(x_58, 1, x_9);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_5);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_57);
lean_ctor_set(x_61, 3, x_60);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_10);
lean_ctor_set(x_54, 0, x_62);
return x_54;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_54, 0);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_54);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_63);
lean_inc(x_4);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_4);
lean_ctor_set(x_66, 1, x_9);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_5);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_4);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_65);
lean_ctor_set(x_69, 3, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_10);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_64);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_72 = !lean_is_exclusive(x_54);
if (x_72 == 0)
{
return x_54;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_54, 0);
x_74 = lean_ctor_get(x_54, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_54);
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
lean_dec(x_48);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_76 = !lean_is_exclusive(x_50);
if (x_76 == 0)
{
return x_50;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_50, 0);
x_78 = lean_ctor_get(x_50, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_50);
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
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = lean_ctor_get(x_19, 0);
lean_inc(x_80);
lean_dec(x_19);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_10);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_17);
return x_82;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_StructInst_Struct_structName(x_2);
lean_inc(x_14);
lean_inc(x_13);
x_15 = l_Lean_getStructureFields(x_13, x_14);
x_16 = l_Lean_Elab_Term_StructInst_Struct_ref(x_2);
x_17 = lean_box(0);
lean_inc(x_15);
lean_inc(x_16);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1___boxed), 17, 7);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_13);
lean_closure_set(x_18, 2, x_14);
lean_closure_set(x_18, 3, x_16);
lean_closure_set(x_18, 4, x_17);
lean_closure_set(x_18, 5, x_15);
lean_closure_set(x_18, 6, x_1);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_7, 3);
x_21 = l_Lean_replaceRef(x_16, x_20);
lean_dec(x_16);
x_22 = l_Lean_replaceRef(x_21, x_20);
lean_dec(x_21);
x_23 = l_Lean_replaceRef(x_22, x_20);
lean_dec(x_20);
lean_dec(x_22);
lean_ctor_set(x_7, 3, x_23);
x_24 = l_Lean_Meta_CheckAssignment_checkFVar___closed__1;
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_iterateMAux___main___rarg(x_24, lean_box(0), x_15, x_18, x_25, x_17);
x_27 = lean_apply_7(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l_List_reverse___rarg(x_29);
x_31 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_30);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = l_List_reverse___rarg(x_32);
x_35 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_27);
if (x_37 == 0)
{
return x_27;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_27, 0);
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_27);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_7, 0);
x_42 = lean_ctor_get(x_7, 1);
x_43 = lean_ctor_get(x_7, 2);
x_44 = lean_ctor_get(x_7, 3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_7);
x_45 = l_Lean_replaceRef(x_16, x_44);
lean_dec(x_16);
x_46 = l_Lean_replaceRef(x_45, x_44);
lean_dec(x_45);
x_47 = l_Lean_replaceRef(x_46, x_44);
lean_dec(x_44);
lean_dec(x_46);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_42);
lean_ctor_set(x_48, 2, x_43);
lean_ctor_set(x_48, 3, x_47);
x_49 = l_Lean_Meta_CheckAssignment_checkFVar___closed__1;
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Array_iterateMAux___main___rarg(x_49, lean_box(0), x_15, x_18, x_50, x_17);
x_52 = lean_apply_7(x_51, x_3, x_4, x_5, x_6, x_48, x_8, x_12);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = l_List_reverse___rarg(x_53);
x_57 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_56);
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_2);
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_52, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_61 = x_52;
} else {
 lean_dec_ref(x_52);
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
}
}
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1___boxed(lean_object** _args) {
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
x_18 = l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_18;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_List_tail_x21___rarg(x_7);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_8);
x_9 = l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(x_6);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_15 = l_List_tail_x21___rarg(x_12);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_14);
x_17 = l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(x_10);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 3);
lean_inc(x_23);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 x_24 = x_18;
} else {
 lean_dec_ref(x_18);
 x_24 = lean_box(0);
}
x_25 = l_List_tail_x21___rarg(x_21);
lean_dec(x_21);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 4, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_23);
x_27 = l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2;
x_3 = l_List_head_x21___rarg___closed__2;
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
return x_5;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = l_Lean_Elab_Term_StructInst_Field_toSyntax(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_3 = l_List_head_x21___rarg___closed__2;
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
return x_5;
}
}
}
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__7(x_4, x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__8(x_1, x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l___private_Lean_Elab_StructInst_13__isSimpleField_x3f(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_20);
x_22 = l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(x_20);
x_23 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_7);
lean_inc(x_19);
lean_inc(x_3);
x_24 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_3, x_4, x_19, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3(x_20);
lean_dec(x_20);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_19);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_29 = lean_unsigned_to_nat(4u);
x_30 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_5);
x_31 = l_Lean_Syntax_setArg(x_5, x_29, x_30);
x_32 = l_List_redLength___main___rarg(x_22);
x_33 = lean_mk_empty_array_with_capacity(x_32);
lean_dec(x_32);
x_34 = l_List_toArrayAux___main___rarg(x_22, x_33);
x_35 = x_34;
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Array_umapMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__4(x_36, x_35);
x_38 = x_37;
x_39 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_530____closed__8;
x_40 = l_Lean_mkAtomFrom(x_5, x_39);
x_41 = l_Lean_mkSepStx(x_38, x_40);
lean_dec(x_38);
x_42 = lean_unsigned_to_nat(2u);
x_43 = l_Lean_Syntax_setArg(x_31, x_42, x_41);
x_44 = l_Lean_Elab_Term_StructInst_setStructSourceSyntax(x_43, x_25);
x_45 = !lean_is_exclusive(x_27);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_27, 1);
x_47 = lean_ctor_get(x_27, 2);
lean_dec(x_47);
x_48 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_46);
lean_dec(x_46);
x_49 = lean_box(0);
lean_ctor_set(x_6, 1, x_49);
lean_ctor_set(x_6, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_27, 2, x_50);
lean_ctor_set(x_27, 1, x_6);
x_51 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_27);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_51, 0, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_27);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_27);
x_59 = !lean_is_exclusive(x_51);
if (x_59 == 0)
{
return x_51;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_51, 0);
x_61 = lean_ctor_get(x_51, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_51);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_27, 0);
x_64 = lean_ctor_get(x_27, 1);
x_65 = lean_ctor_get(x_27, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_27);
x_66 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_64);
lean_dec(x_64);
x_67 = lean_box(0);
lean_ctor_set(x_6, 1, x_67);
lean_ctor_set(x_6, 0, x_66);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_44);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_6);
lean_ctor_set(x_69, 2, x_68);
lean_ctor_set(x_69, 3, x_65);
x_70 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_71);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_69);
x_76 = lean_ctor_get(x_70, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_78 = x_70;
} else {
 lean_dec_ref(x_70);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_28, 0);
lean_inc(x_80);
lean_dec(x_28);
lean_inc(x_5);
x_81 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_81, 0, x_5);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_81, 2, x_22);
lean_ctor_set(x_81, 3, x_25);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_82 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_81, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = !lean_is_exclusive(x_27);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_27, 1);
x_87 = lean_ctor_get(x_27, 2);
lean_dec(x_87);
x_88 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_86);
lean_dec(x_86);
x_89 = lean_box(0);
lean_ctor_set(x_6, 1, x_89);
lean_ctor_set(x_6, 0, x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_27, 2, x_90);
lean_ctor_set(x_27, 1, x_6);
x_91 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_84);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_27);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_91, 0, x_94);
return x_91;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_91, 0);
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_91);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_27);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_27);
x_99 = !lean_is_exclusive(x_91);
if (x_99 == 0)
{
return x_91;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_91, 0);
x_101 = lean_ctor_get(x_91, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_91);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_103 = lean_ctor_get(x_27, 0);
x_104 = lean_ctor_get(x_27, 1);
x_105 = lean_ctor_get(x_27, 3);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_27);
x_106 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_104);
lean_dec(x_104);
x_107 = lean_box(0);
lean_ctor_set(x_6, 1, x_107);
lean_ctor_set(x_6, 0, x_106);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_83);
x_109 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_109, 0, x_103);
lean_ctor_set(x_109, 1, x_6);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_105);
x_110 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_84);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_109);
lean_ctor_set(x_114, 1, x_111);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_109);
x_116 = lean_ctor_get(x_110, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_118 = x_110;
} else {
 lean_dec_ref(x_110);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_27);
lean_free_object(x_6);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_82);
if (x_120 == 0)
{
return x_82;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_82, 0);
x_122 = lean_ctor_get(x_82, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_82);
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
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_free_object(x_6);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_124 = !lean_is_exclusive(x_24);
if (x_124 == 0)
{
return x_24;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_24, 0);
x_126 = lean_ctor_get(x_24, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_24);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_20);
lean_dec(x_19);
x_128 = lean_ctor_get(x_21, 0);
lean_inc(x_128);
lean_dec(x_21);
x_129 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_129, 0);
lean_ctor_set(x_6, 1, x_131);
lean_ctor_set(x_6, 0, x_128);
lean_ctor_set(x_129, 0, x_6);
return x_129;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_129, 0);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_129);
lean_ctor_set(x_6, 1, x_132);
lean_ctor_set(x_6, 0, x_128);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_6);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
else
{
uint8_t x_135; 
lean_dec(x_128);
lean_free_object(x_6);
x_135 = !lean_is_exclusive(x_129);
if (x_135 == 0)
{
return x_129;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_129, 0);
x_137 = lean_ctor_get(x_129, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_129);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_6, 0);
x_140 = lean_ctor_get(x_6, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_6);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_143 = l___private_Lean_Elab_StructInst_13__isSimpleField_x3f(x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_inc(x_142);
x_144 = l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(x_142);
x_145 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_7);
lean_inc(x_141);
lean_inc(x_3);
x_146 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_3, x_4, x_141, x_145, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3(x_142);
lean_dec(x_142);
lean_inc(x_3);
lean_inc(x_2);
x_150 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_141);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_151 = lean_unsigned_to_nat(4u);
x_152 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_5);
x_153 = l_Lean_Syntax_setArg(x_5, x_151, x_152);
x_154 = l_List_redLength___main___rarg(x_144);
x_155 = lean_mk_empty_array_with_capacity(x_154);
lean_dec(x_154);
x_156 = l_List_toArrayAux___main___rarg(x_144, x_155);
x_157 = x_156;
x_158 = lean_unsigned_to_nat(0u);
x_159 = l_Array_umapMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__4(x_158, x_157);
x_160 = x_159;
x_161 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_530____closed__8;
x_162 = l_Lean_mkAtomFrom(x_5, x_161);
x_163 = l_Lean_mkSepStx(x_160, x_162);
lean_dec(x_160);
x_164 = lean_unsigned_to_nat(2u);
x_165 = l_Lean_Syntax_setArg(x_153, x_164, x_163);
x_166 = l_Lean_Elab_Term_StructInst_setStructSourceSyntax(x_165, x_147);
x_167 = lean_ctor_get(x_149, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_149, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_149, 3);
lean_inc(x_169);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 lean_ctor_release(x_149, 3);
 x_170 = x_149;
} else {
 lean_dec_ref(x_149);
 x_170 = lean_box(0);
}
x_171 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_168);
lean_dec(x_168);
x_172 = lean_box(0);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_166);
if (lean_is_scalar(x_170)) {
 x_175 = lean_alloc_ctor(0, 4, 0);
} else {
 x_175 = x_170;
}
lean_ctor_set(x_175, 0, x_167);
lean_ctor_set(x_175, 1, x_173);
lean_ctor_set(x_175, 2, x_174);
lean_ctor_set(x_175, 3, x_169);
x_176 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_140, x_7, x_8, x_9, x_10, x_11, x_12, x_148);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_175);
lean_ctor_set(x_180, 1, x_177);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_178);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_175);
x_182 = lean_ctor_get(x_176, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_176, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_184 = x_176;
} else {
 lean_dec_ref(x_176);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_150, 0);
lean_inc(x_186);
lean_dec(x_150);
lean_inc(x_5);
x_187 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_187, 0, x_5);
lean_ctor_set(x_187, 1, x_186);
lean_ctor_set(x_187, 2, x_144);
lean_ctor_set(x_187, 3, x_147);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_188 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_187, x_7, x_8, x_9, x_10, x_11, x_12, x_148);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_ctor_get(x_149, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_149, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_149, 3);
lean_inc(x_193);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 lean_ctor_release(x_149, 3);
 x_194 = x_149;
} else {
 lean_dec_ref(x_149);
 x_194 = lean_box(0);
}
x_195 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_192);
lean_dec(x_192);
x_196 = lean_box(0);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_189);
if (lean_is_scalar(x_194)) {
 x_199 = lean_alloc_ctor(0, 4, 0);
} else {
 x_199 = x_194;
}
lean_ctor_set(x_199, 0, x_191);
lean_ctor_set(x_199, 1, x_197);
lean_ctor_set(x_199, 2, x_198);
lean_ctor_set(x_199, 3, x_193);
x_200 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_140, x_7, x_8, x_9, x_10, x_11, x_12, x_190);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_203 = x_200;
} else {
 lean_dec_ref(x_200);
 x_203 = lean_box(0);
}
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_199);
lean_ctor_set(x_204, 1, x_201);
if (lean_is_scalar(x_203)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_203;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_202);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_199);
x_206 = lean_ctor_get(x_200, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_208 = x_200;
} else {
 lean_dec_ref(x_200);
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
lean_dec(x_149);
lean_dec(x_140);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_210 = lean_ctor_get(x_188, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_188, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_212 = x_188;
} else {
 lean_dec_ref(x_188);
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
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_214 = lean_ctor_get(x_146, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_146, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_216 = x_146;
} else {
 lean_dec_ref(x_146);
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
else
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_142);
lean_dec(x_141);
x_218 = lean_ctor_get(x_143, 0);
lean_inc(x_218);
lean_dec(x_143);
x_219 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_140, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_222 = x_219;
} else {
 lean_dec_ref(x_219);
 x_222 = lean_box(0);
}
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_218);
lean_ctor_set(x_223, 1, x_220);
if (lean_is_scalar(x_222)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_222;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_221);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_218);
x_225 = lean_ctor_get(x_219, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_219, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_227 = x_219;
} else {
 lean_dec_ref(x_219);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l___private_Lean_Elab_StructInst_12__mkFieldMap(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__6(x_15);
lean_dec(x_15);
x_18 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_13);
lean_inc(x_12);
x_14 = l_Lean_getStructureFields(x_12, x_13);
x_15 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
lean_inc(x_15);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1___boxed), 13, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_12);
lean_closure_set(x_16, 2, x_13);
lean_closure_set(x_16, 3, x_14);
lean_closure_set(x_16, 4, x_15);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_6, 3);
x_19 = l_Lean_replaceRef(x_15, x_18);
lean_dec(x_15);
x_20 = l_Lean_replaceRef(x_19, x_18);
lean_dec(x_19);
x_21 = l_Lean_replaceRef(x_20, x_18);
lean_dec(x_18);
lean_dec(x_20);
lean_ctor_set(x_6, 3, x_21);
x_22 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(x_1, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
x_25 = lean_ctor_get(x_6, 2);
x_26 = lean_ctor_get(x_6, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_27 = l_Lean_replaceRef(x_15, x_26);
lean_dec(x_15);
x_28 = l_Lean_replaceRef(x_27, x_26);
lean_dec(x_27);
x_29 = l_Lean_replaceRef(x_28, x_26);
lean_dec(x_26);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_29);
x_31 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(x_1, x_16, x_2, x_3, x_4, x_5, x_30, x_7, x_11);
return x_31;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_get_size(x_8);
x_19 = lean_nat_dec_lt(x_9, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_array_fget(x_8, x_9);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_9, x_22);
lean_dec(x_9);
x_24 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_inc(x_21);
x_25 = l_Lean_Elab_Term_StructInst_findField_x3f(x_24, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_inc(x_21);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l_Lean_isSubobjectField_x3f(x_3, x_4, x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
switch (lean_obj_tag(x_27)) {
case 0:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_box(2);
lean_inc(x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_21);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
lean_inc(x_6);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_6);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_10);
x_9 = x_23;
x_10 = x_34;
goto _start;
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_27);
x_36 = l_Lean_mkHole(x_6);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_inc(x_6);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_21);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_box(0);
lean_inc(x_6);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_6);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_10);
x_9 = x_23;
x_10 = x_43;
goto _start;
}
default: 
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_45 = lean_ctor_get(x_27, 0);
lean_inc(x_45);
lean_dec(x_27);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Lean_Syntax_getArg(x_45, x_46);
lean_dec(x_45);
lean_inc(x_21);
x_48 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_47, x_21);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_inc(x_6);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_6);
lean_ctor_set(x_50, 1, x_21);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_box(0);
lean_inc(x_6);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_6);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_49);
lean_ctor_set(x_54, 3, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_10);
x_9 = x_23;
x_10 = x_55;
goto _start;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_26, 0);
lean_inc(x_57);
lean_dec(x_26);
x_58 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_11);
lean_inc(x_21);
lean_inc(x_4);
x_59 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_4, x_5, x_21, x_58, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_7);
lean_inc(x_6);
x_62 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_62, 0, x_6);
lean_ctor_set(x_62, 1, x_57);
lean_ctor_set(x_62, 2, x_7);
lean_ctor_set(x_62, 3, x_60);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_63 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_62, x_11, x_12, x_13, x_14, x_15, x_16, x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_64);
lean_inc(x_6);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_6);
lean_ctor_set(x_67, 1, x_21);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_box(0);
lean_inc(x_6);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_6);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_66);
lean_ctor_set(x_71, 3, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_10);
x_9 = x_23;
x_10 = x_72;
x_17 = x_65;
goto _start;
}
else
{
uint8_t x_74; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_63);
if (x_74 == 0)
{
return x_63;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_63, 0);
x_76 = lean_ctor_get(x_63, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_63);
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
lean_dec(x_57);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_59);
if (x_78 == 0)
{
return x_59;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_59, 0);
x_80 = lean_ctor_get(x_59, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_59);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_21);
x_82 = lean_ctor_get(x_25, 0);
lean_inc(x_82);
lean_dec(x_25);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_10);
x_9 = x_23;
x_10 = x_83;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_13);
lean_inc(x_12);
x_14 = l_Lean_getStructureFields(x_12, x_13);
x_15 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_16 = lean_box(0);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_6, 3);
x_19 = l_Lean_replaceRef(x_15, x_18);
x_20 = l_Lean_replaceRef(x_19, x_18);
lean_dec(x_19);
x_21 = l_Lean_replaceRef(x_20, x_18);
lean_dec(x_18);
lean_dec(x_20);
lean_ctor_set(x_6, 3, x_21);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11(x_1, x_10, x_12, x_13, x_14, x_15, x_16, x_14, x_22, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_14);
lean_dec(x_10);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_List_reverse___rarg(x_25);
x_27 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_26);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = l_List_reverse___rarg(x_28);
x_31 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_6, 0);
x_38 = lean_ctor_get(x_6, 1);
x_39 = lean_ctor_get(x_6, 2);
x_40 = lean_ctor_get(x_6, 3);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_6);
x_41 = l_Lean_replaceRef(x_15, x_40);
x_42 = l_Lean_replaceRef(x_41, x_40);
lean_dec(x_41);
x_43 = l_Lean_replaceRef(x_42, x_40);
lean_dec(x_40);
lean_dec(x_42);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_38);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_43);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11(x_1, x_10, x_12, x_13, x_14, x_15, x_16, x_14, x_45, x_16, x_2, x_3, x_4, x_5, x_44, x_7, x_11);
lean_dec(x_14);
lean_dec(x_10);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_List_reverse___rarg(x_47);
x_51 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_50);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_1);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_55 = x_46;
} else {
 lean_dec_ref(x_46);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_19__expandStruct___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l___private_Lean_Elab_StructInst_8__expandCompositeFields___closed__1;
x_10 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l___private_Lean_Elab_StructInst_9__expandNumLitFields(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l___private_Lean_Elab_StructInst_10__expandParentFields(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Elab_StructInst_18__addMissingFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__10(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__7(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__6(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11___boxed(lean_object** _args) {
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
x_18 = l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
lean_object* l___private_Lean_Elab_StructInst_19__expandStruct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected constructor type");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_1, x_14);
lean_dec(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 7)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; uint8_t x_33; lean_object* x_34; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
x_21 = lean_ctor_get_uint64(x_17, sizeof(void*)*3);
lean_dec(x_17);
x_33 = (uint8_t)((x_21 << 24) >> 61);
x_34 = lean_box(x_33);
if (lean_obj_tag(x_34) == 3)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_19);
x_36 = 1;
x_37 = lean_box(0);
lean_inc(x_7);
x_38 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_35, x_36, x_37, x_7, x_8, x_9, x_10, x_18);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_expr_instantiate1(x_20, x_39);
lean_dec(x_20);
lean_inc(x_39);
x_42 = l_Lean_mkApp(x_3, x_39);
x_43 = l_Lean_Expr_mvarId_x21(x_39);
lean_dec(x_39);
x_44 = lean_array_push(x_4, x_43);
x_1 = x_15;
x_2 = x_41;
x_3 = x_42;
x_4 = x_44;
x_11 = x_40;
goto _start;
}
else
{
lean_object* x_46; 
lean_dec(x_34);
x_46 = lean_box(0);
x_22 = x_46;
goto block_32;
}
block_32:
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_19);
x_24 = 0;
x_25 = lean_box(0);
lean_inc(x_7);
x_26 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_23, x_24, x_25, x_7, x_8, x_9, x_10, x_18);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_expr_instantiate1(x_20, x_27);
lean_dec(x_20);
x_30 = l_Lean_mkApp(x_3, x_27);
x_1 = x_15;
x_2 = x_29;
x_3 = x_30;
x_11 = x_28;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
x_47 = lean_ctor_get(x_16, 1);
lean_inc(x_47);
lean_dec(x_16);
x_48 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_49 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_47);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_16);
if (x_50 == 0)
{
return x_16;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_16, 0);
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_16);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_3);
lean_ctor_set(x_54, 1, x_2);
lean_ctor_set(x_54, 2, x_4);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_11);
return x_55;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l___private_Lean_Elab_StructInst_21__getForallBody___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_21__getForallBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_StructInst_21__getForallBody___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_StructInst_22__propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = l___private_Lean_Elab_StructInst_21__getForallBody___main(x_2, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Expr_hasLooseBVars(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_13, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_10);
return x_31;
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_22__propagateExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_StructInst_22__propagateExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2___rarg(x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_15);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2___rarg(x_5, x_6, x_7, x_8);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_28);
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
}
}
lean_object* l___private_Lean_Elab_StructInst_23__mkCtorHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
lean_inc(x_13);
x_16 = l_Lean_mkConst(x_15, x_13);
lean_inc(x_1);
x_17 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = lean_instantiate_type_lparams(x_17, x_13);
lean_dec(x_13);
lean_dec(x_17);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
x_20 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_21 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main(x_19, x_18, x_16, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 4);
lean_inc(x_25);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = l___private_Lean_Elab_StructInst_22__propagateExpectedType(x_24, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_22, 2);
lean_inc(x_28);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_28, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_22);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_22);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
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
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_26);
if (x_39 == 0)
{
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
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
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_StructInst_23__mkCtorHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_23__mkCtorHeader(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structInstDefault");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2;
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_defaultMissing_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2;
x_3 = l_Lean_annotation_x3f(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_defaultMissing_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to elaborate field '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' of '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__6;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_2);
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
x_21 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
}
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Meta_synthInstance_x3f___at_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Elab_Term_StructInst_Struct_allDefault___main(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set_tag(x_13, 0);
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
}
}
}
lean_object* l_Lean_Meta_synthInstance_x3f___at_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_synthInstance_x3f___at_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected unexpanded structure field");
return x_1;
}
}
static lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_24; lean_object* x_29; lean_object* x_30; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_29);
lean_free_object(x_3);
lean_dec(x_2);
x_31 = lean_box(0);
x_24 = x_31;
goto block_28;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_13);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 2);
x_43 = lean_ctor_get(x_13, 3);
lean_dec(x_43);
x_44 = lean_ctor_get(x_13, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_46 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 7)
{
lean_dec(x_45);
switch (lean_obj_tag(x_42)) {
case 0:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_47, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_47, 2);
lean_inc(x_64);
lean_dec(x_47);
x_65 = lean_ctor_get(x_42, 0);
lean_inc(x_65);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_63);
x_67 = lean_box(0);
x_68 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_69 = l_Lean_Elab_Term_elabTermEnsuringType(x_65, x_66, x_68, x_67, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = l_Lean_mkApp(x_35, x_71);
x_73 = lean_expr_instantiate1(x_64, x_71);
lean_dec(x_64);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_13, 3, x_74);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_73);
lean_ctor_set(x_2, 0, x_72);
lean_ctor_set(x_69, 0, x_2);
x_15 = x_69;
goto block_23;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_69, 0);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_69);
lean_inc(x_75);
x_77 = l_Lean_mkApp(x_35, x_75);
x_78 = lean_expr_instantiate1(x_64, x_75);
lean_dec(x_64);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_13, 3, x_79);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_78);
lean_ctor_set(x_2, 0, x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_2);
lean_ctor_set(x_80, 1, x_76);
x_15 = x_80;
goto block_23;
}
}
else
{
uint8_t x_81; 
lean_dec(x_64);
lean_free_object(x_13);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_81 = !lean_is_exclusive(x_69);
if (x_81 == 0)
{
x_15 = x_69;
goto block_23;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_69, 0);
x_83 = lean_ctor_get(x_69, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_69);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_15 = x_84;
goto block_23;
}
}
}
case 1:
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_47, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_47, 2);
lean_inc(x_86);
lean_dec(x_47);
x_87 = !lean_is_exclusive(x_42);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_42, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_85);
x_89 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_88, x_85, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_free_object(x_2);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_85);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_92);
x_93 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_88, x_92, x_4, x_5, x_6, x_7, x_8, x_9, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = !lean_is_exclusive(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_94, 0);
x_98 = lean_ctor_get(x_94, 1);
x_99 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_100 = l_Lean_Elab_Term_ensureHasType(x_92, x_97, x_99, x_4, x_5, x_6, x_7, x_8, x_9, x_95);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_100, 0);
lean_ctor_set(x_42, 0, x_98);
lean_inc(x_102);
x_103 = l_Lean_mkApp(x_35, x_102);
x_104 = lean_expr_instantiate1(x_86, x_102);
lean_dec(x_86);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_13, 3, x_105);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_94, 1, x_3);
lean_ctor_set(x_94, 0, x_104);
lean_ctor_set(x_29, 1, x_94);
lean_ctor_set(x_29, 0, x_103);
lean_ctor_set(x_100, 0, x_29);
x_15 = x_100;
goto block_23;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_100, 0);
x_107 = lean_ctor_get(x_100, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_100);
lean_ctor_set(x_42, 0, x_98);
lean_inc(x_106);
x_108 = l_Lean_mkApp(x_35, x_106);
x_109 = lean_expr_instantiate1(x_86, x_106);
lean_dec(x_86);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_13, 3, x_110);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_94, 1, x_3);
lean_ctor_set(x_94, 0, x_109);
lean_ctor_set(x_29, 1, x_94);
lean_ctor_set(x_29, 0, x_108);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_29);
lean_ctor_set(x_111, 1, x_107);
x_15 = x_111;
goto block_23;
}
}
else
{
uint8_t x_112; 
lean_free_object(x_94);
lean_dec(x_98);
lean_free_object(x_42);
lean_dec(x_86);
lean_free_object(x_13);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_112 = !lean_is_exclusive(x_100);
if (x_112 == 0)
{
x_15 = x_100;
goto block_23;
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
x_15 = x_115;
goto block_23;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_94, 0);
x_117 = lean_ctor_get(x_94, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_94);
x_118 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_119 = l_Lean_Elab_Term_ensureHasType(x_92, x_116, x_118, x_4, x_5, x_6, x_7, x_8, x_9, x_95);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
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
lean_ctor_set(x_42, 0, x_117);
lean_inc(x_120);
x_123 = l_Lean_mkApp(x_35, x_120);
x_124 = lean_expr_instantiate1(x_86, x_120);
lean_dec(x_86);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_13, 3, x_125);
lean_ctor_set(x_3, 1, x_40);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_3);
lean_ctor_set(x_29, 1, x_126);
lean_ctor_set(x_29, 0, x_123);
if (lean_is_scalar(x_122)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_122;
}
lean_ctor_set(x_127, 0, x_29);
lean_ctor_set(x_127, 1, x_121);
x_15 = x_127;
goto block_23;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_117);
lean_free_object(x_42);
lean_dec(x_86);
lean_free_object(x_13);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_128 = lean_ctor_get(x_119, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_119, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_130 = x_119;
} else {
 lean_dec_ref(x_119);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
x_15 = x_131;
goto block_23;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_92);
lean_free_object(x_42);
lean_dec(x_86);
lean_free_object(x_13);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_132 = !lean_is_exclusive(x_93);
if (x_132 == 0)
{
x_15 = x_93;
goto block_23;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_93, 0);
x_134 = lean_ctor_get(x_93, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_93);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_15 = x_135;
goto block_23;
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_88);
lean_dec(x_85);
x_136 = !lean_is_exclusive(x_89);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_89, 0);
lean_dec(x_137);
x_138 = !lean_is_exclusive(x_90);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_90, 0);
x_140 = l_Lean_mkHole(x_41);
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_140);
lean_inc(x_139);
x_141 = l_Lean_mkApp(x_35, x_139);
x_142 = lean_expr_instantiate1(x_86, x_139);
lean_dec(x_86);
lean_ctor_set(x_13, 3, x_90);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_142);
lean_ctor_set(x_2, 0, x_141);
lean_ctor_set(x_89, 0, x_2);
x_15 = x_89;
goto block_23;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_ctor_get(x_90, 0);
lean_inc(x_143);
lean_dec(x_90);
x_144 = l_Lean_mkHole(x_41);
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_144);
lean_inc(x_143);
x_145 = l_Lean_mkApp(x_35, x_143);
x_146 = lean_expr_instantiate1(x_86, x_143);
lean_dec(x_86);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_143);
lean_ctor_set(x_13, 3, x_147);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_146);
lean_ctor_set(x_2, 0, x_145);
lean_ctor_set(x_89, 0, x_2);
x_15 = x_89;
goto block_23;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_148 = lean_ctor_get(x_89, 1);
lean_inc(x_148);
lean_dec(x_89);
x_149 = lean_ctor_get(x_90, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_150 = x_90;
} else {
 lean_dec_ref(x_90);
 x_150 = lean_box(0);
}
x_151 = l_Lean_mkHole(x_41);
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_151);
lean_inc(x_149);
x_152 = l_Lean_mkApp(x_35, x_149);
x_153 = lean_expr_instantiate1(x_86, x_149);
lean_dec(x_86);
if (lean_is_scalar(x_150)) {
 x_154 = lean_alloc_ctor(1, 1, 0);
} else {
 x_154 = x_150;
}
lean_ctor_set(x_154, 0, x_149);
lean_ctor_set(x_13, 3, x_154);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_153);
lean_ctor_set(x_2, 0, x_152);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_2);
lean_ctor_set(x_155, 1, x_148);
x_15 = x_155;
goto block_23;
}
}
}
else
{
uint8_t x_156; 
lean_free_object(x_42);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_free_object(x_13);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_156 = !lean_is_exclusive(x_89);
if (x_156 == 0)
{
x_15 = x_89;
goto block_23;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_89, 0);
x_158 = lean_ctor_get(x_89, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_89);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_15 = x_159;
goto block_23;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_42, 0);
lean_inc(x_160);
lean_dec(x_42);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_85);
x_161 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_160, x_85, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_free_object(x_2);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_85);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_164);
x_165 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_160, x_164, x_4, x_5, x_6, x_7, x_8, x_9, x_163);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_170 = x_166;
} else {
 lean_dec_ref(x_166);
 x_170 = lean_box(0);
}
x_171 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_172 = l_Lean_Elab_Term_ensureHasType(x_164, x_168, x_171, x_4, x_5, x_6, x_7, x_8, x_9, x_167);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_175 = x_172;
} else {
 lean_dec_ref(x_172);
 x_175 = lean_box(0);
}
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_169);
lean_inc(x_173);
x_177 = l_Lean_mkApp(x_35, x_173);
x_178 = lean_expr_instantiate1(x_86, x_173);
lean_dec(x_86);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_173);
lean_ctor_set(x_13, 3, x_179);
lean_ctor_set(x_13, 2, x_176);
lean_ctor_set(x_3, 1, x_40);
if (lean_is_scalar(x_170)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_170;
}
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_3);
lean_ctor_set(x_29, 1, x_180);
lean_ctor_set(x_29, 0, x_177);
if (lean_is_scalar(x_175)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_175;
}
lean_ctor_set(x_181, 0, x_29);
lean_ctor_set(x_181, 1, x_174);
x_15 = x_181;
goto block_23;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_86);
lean_free_object(x_13);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_182 = lean_ctor_get(x_172, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_172, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_184 = x_172;
} else {
 lean_dec_ref(x_172);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
x_15 = x_185;
goto block_23;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_164);
lean_dec(x_86);
lean_free_object(x_13);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_186 = lean_ctor_get(x_165, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_165, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_188 = x_165;
} else {
 lean_dec_ref(x_165);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
x_15 = x_189;
goto block_23;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_160);
lean_dec(x_85);
x_190 = lean_ctor_get(x_161, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_191 = x_161;
} else {
 lean_dec_ref(x_161);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_162, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 x_193 = x_162;
} else {
 lean_dec_ref(x_162);
 x_193 = lean_box(0);
}
x_194 = l_Lean_mkHole(x_41);
x_195 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_195, 0, x_194);
lean_inc(x_192);
x_196 = l_Lean_mkApp(x_35, x_192);
x_197 = lean_expr_instantiate1(x_86, x_192);
lean_dec(x_86);
if (lean_is_scalar(x_193)) {
 x_198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_198 = x_193;
}
lean_ctor_set(x_198, 0, x_192);
lean_ctor_set(x_13, 3, x_198);
lean_ctor_set(x_13, 2, x_195);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_197);
lean_ctor_set(x_2, 0, x_196);
if (lean_is_scalar(x_191)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_191;
}
lean_ctor_set(x_199, 0, x_2);
lean_ctor_set(x_199, 1, x_190);
x_15 = x_199;
goto block_23;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_160);
lean_dec(x_86);
lean_dec(x_85);
lean_free_object(x_13);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_200 = lean_ctor_get(x_161, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_161, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_202 = x_161;
} else {
 lean_dec_ref(x_161);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
x_15 = x_203;
goto block_23;
}
}
}
default: 
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_204 = lean_ctor_get(x_47, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_47, 2);
lean_inc(x_205);
lean_dec(x_47);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_204);
x_207 = lean_ctor_get(x_8, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_8, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_8, 2);
lean_inc(x_209);
x_210 = lean_ctor_get(x_8, 3);
lean_inc(x_210);
x_211 = l_Lean_replaceRef(x_41, x_210);
x_212 = l_Lean_replaceRef(x_211, x_210);
lean_dec(x_211);
x_213 = l_Lean_replaceRef(x_212, x_210);
lean_dec(x_210);
lean_dec(x_212);
x_214 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_214, 0, x_207);
lean_ctor_set(x_214, 1, x_208);
lean_ctor_set(x_214, 2, x_209);
lean_ctor_set(x_214, 3, x_213);
x_215 = 0;
x_216 = lean_box(0);
lean_inc(x_6);
x_217 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_206, x_215, x_216, x_6, x_7, x_214, x_9, x_48);
lean_dec(x_214);
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_219 = lean_ctor_get(x_217, 0);
x_220 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_219);
lean_inc(x_220);
x_221 = l_Lean_mkApp(x_35, x_220);
x_222 = lean_expr_instantiate1(x_205, x_220);
lean_dec(x_205);
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_13, 3, x_223);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_222);
lean_ctor_set(x_2, 0, x_221);
lean_ctor_set(x_217, 0, x_2);
x_15 = x_217;
goto block_23;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = lean_ctor_get(x_217, 0);
x_225 = lean_ctor_get(x_217, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_217);
x_226 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_224);
lean_inc(x_226);
x_227 = l_Lean_mkApp(x_35, x_226);
x_228 = lean_expr_instantiate1(x_205, x_226);
lean_dec(x_205);
x_229 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_13, 3, x_229);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_228);
lean_ctor_set(x_2, 0, x_227);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_2);
lean_ctor_set(x_230, 1, x_225);
x_15 = x_230;
goto block_23;
}
}
}
}
else
{
lean_object* x_231; 
lean_free_object(x_13);
lean_dec(x_42);
lean_free_object(x_29);
lean_dec(x_40);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_231 = lean_box(0);
x_49 = x_231;
goto block_62;
}
block_62:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_49);
x_50 = l_Lean_indentExpr(x_47);
x_51 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_ctor_get(x_8, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_8, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_8, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_8, 3);
lean_inc(x_56);
x_57 = l_Lean_replaceRef(x_41, x_56);
lean_dec(x_41);
x_58 = l_Lean_replaceRef(x_57, x_56);
lean_dec(x_57);
x_59 = l_Lean_replaceRef(x_58, x_56);
lean_dec(x_56);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_54);
lean_ctor_set(x_60, 2, x_55);
lean_ctor_set(x_60, 3, x_59);
lean_inc(x_4);
lean_inc(x_1);
x_61 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_45, x_1, x_52, x_4, x_5, x_6, x_7, x_60, x_9, x_48);
lean_dec(x_60);
x_15 = x_61;
goto block_23;
}
}
else
{
uint8_t x_232; 
lean_dec(x_45);
lean_free_object(x_13);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_232 = !lean_is_exclusive(x_46);
if (x_232 == 0)
{
x_15 = x_46;
goto block_23;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_46, 0);
x_234 = lean_ctor_get(x_46, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_46);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
x_15 = x_235;
goto block_23;
}
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_236 = lean_ctor_get(x_29, 0);
x_237 = lean_ctor_get(x_29, 1);
x_238 = lean_ctor_get(x_13, 0);
x_239 = lean_ctor_get(x_13, 2);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_13);
x_240 = lean_ctor_get(x_32, 1);
lean_inc(x_240);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_241 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(x_236, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
if (lean_obj_tag(x_242) == 7)
{
lean_dec(x_240);
switch (lean_obj_tag(x_239)) {
case 0:
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; 
x_258 = lean_ctor_get(x_242, 1);
lean_inc(x_258);
x_259 = lean_ctor_get(x_242, 2);
lean_inc(x_259);
lean_dec(x_242);
x_260 = lean_ctor_get(x_239, 0);
lean_inc(x_260);
x_261 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_261, 0, x_258);
x_262 = lean_box(0);
x_263 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_264 = l_Lean_Elab_Term_elabTermEnsuringType(x_260, x_261, x_263, x_262, x_4, x_5, x_6, x_7, x_8, x_9, x_243);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_267 = x_264;
} else {
 lean_dec_ref(x_264);
 x_267 = lean_box(0);
}
lean_inc(x_265);
x_268 = l_Lean_mkApp(x_35, x_265);
x_269 = lean_expr_instantiate1(x_259, x_265);
lean_dec(x_259);
x_270 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_270, 0, x_265);
x_271 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_271, 0, x_238);
lean_ctor_set(x_271, 1, x_30);
lean_ctor_set(x_271, 2, x_239);
lean_ctor_set(x_271, 3, x_270);
lean_ctor_set(x_3, 1, x_237);
lean_ctor_set(x_3, 0, x_271);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_269);
lean_ctor_set(x_2, 0, x_268);
if (lean_is_scalar(x_267)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_267;
}
lean_ctor_set(x_272, 0, x_2);
lean_ctor_set(x_272, 1, x_266);
x_15 = x_272;
goto block_23;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_259);
lean_dec(x_239);
lean_dec(x_238);
lean_free_object(x_29);
lean_dec(x_237);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_273 = lean_ctor_get(x_264, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_264, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_275 = x_264;
} else {
 lean_dec_ref(x_264);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
x_15 = x_276;
goto block_23;
}
}
case 1:
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_277 = lean_ctor_get(x_242, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_242, 2);
lean_inc(x_278);
lean_dec(x_242);
x_279 = lean_ctor_get(x_239, 0);
lean_inc(x_279);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 x_280 = x_239;
} else {
 lean_dec_ref(x_239);
 x_280 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_277);
x_281 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_279, x_277, x_4, x_5, x_6, x_7, x_8, x_9, x_243);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_free_object(x_2);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_284, 0, x_277);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_284);
x_285 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_279, x_284, x_4, x_5, x_6, x_7, x_8, x_9, x_283);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_ctor_get(x_286, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_286, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_290 = x_286;
} else {
 lean_dec_ref(x_286);
 x_290 = lean_box(0);
}
x_291 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_292 = l_Lean_Elab_Term_ensureHasType(x_284, x_288, x_291, x_4, x_5, x_6, x_7, x_8, x_9, x_287);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_295 = x_292;
} else {
 lean_dec_ref(x_292);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_296 = lean_alloc_ctor(1, 1, 0);
} else {
 x_296 = x_280;
}
lean_ctor_set(x_296, 0, x_289);
lean_inc(x_293);
x_297 = l_Lean_mkApp(x_35, x_293);
x_298 = lean_expr_instantiate1(x_278, x_293);
lean_dec(x_278);
x_299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_299, 0, x_293);
x_300 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_300, 0, x_238);
lean_ctor_set(x_300, 1, x_30);
lean_ctor_set(x_300, 2, x_296);
lean_ctor_set(x_300, 3, x_299);
lean_ctor_set(x_3, 1, x_237);
lean_ctor_set(x_3, 0, x_300);
if (lean_is_scalar(x_290)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_290;
}
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_3);
lean_ctor_set(x_29, 1, x_301);
lean_ctor_set(x_29, 0, x_297);
if (lean_is_scalar(x_295)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_295;
}
lean_ctor_set(x_302, 0, x_29);
lean_ctor_set(x_302, 1, x_294);
x_15 = x_302;
goto block_23;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_280);
lean_dec(x_278);
lean_dec(x_238);
lean_free_object(x_29);
lean_dec(x_237);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_303 = lean_ctor_get(x_292, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_292, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_305 = x_292;
} else {
 lean_dec_ref(x_292);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_304);
x_15 = x_306;
goto block_23;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_284);
lean_dec(x_280);
lean_dec(x_278);
lean_dec(x_238);
lean_free_object(x_29);
lean_dec(x_237);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_307 = lean_ctor_get(x_285, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_285, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_309 = x_285;
} else {
 lean_dec_ref(x_285);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_308);
x_15 = x_310;
goto block_23;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_279);
lean_dec(x_277);
x_311 = lean_ctor_get(x_281, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_312 = x_281;
} else {
 lean_dec_ref(x_281);
 x_312 = lean_box(0);
}
x_313 = lean_ctor_get(x_282, 0);
lean_inc(x_313);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 x_314 = x_282;
} else {
 lean_dec_ref(x_282);
 x_314 = lean_box(0);
}
x_315 = l_Lean_mkHole(x_238);
if (lean_is_scalar(x_280)) {
 x_316 = lean_alloc_ctor(0, 1, 0);
} else {
 x_316 = x_280;
 lean_ctor_set_tag(x_316, 0);
}
lean_ctor_set(x_316, 0, x_315);
lean_inc(x_313);
x_317 = l_Lean_mkApp(x_35, x_313);
x_318 = lean_expr_instantiate1(x_278, x_313);
lean_dec(x_278);
if (lean_is_scalar(x_314)) {
 x_319 = lean_alloc_ctor(1, 1, 0);
} else {
 x_319 = x_314;
}
lean_ctor_set(x_319, 0, x_313);
x_320 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_320, 0, x_238);
lean_ctor_set(x_320, 1, x_30);
lean_ctor_set(x_320, 2, x_316);
lean_ctor_set(x_320, 3, x_319);
lean_ctor_set(x_3, 1, x_237);
lean_ctor_set(x_3, 0, x_320);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_318);
lean_ctor_set(x_2, 0, x_317);
if (lean_is_scalar(x_312)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_312;
}
lean_ctor_set(x_321, 0, x_2);
lean_ctor_set(x_321, 1, x_311);
x_15 = x_321;
goto block_23;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_280);
lean_dec(x_279);
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_238);
lean_free_object(x_29);
lean_dec(x_237);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_322 = lean_ctor_get(x_281, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_281, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_324 = x_281;
} else {
 lean_dec_ref(x_281);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 2, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_322);
lean_ctor_set(x_325, 1, x_323);
x_15 = x_325;
goto block_23;
}
}
default: 
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_326 = lean_ctor_get(x_242, 1);
lean_inc(x_326);
x_327 = lean_ctor_get(x_242, 2);
lean_inc(x_327);
lean_dec(x_242);
x_328 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_328, 0, x_326);
x_329 = lean_ctor_get(x_8, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_8, 1);
lean_inc(x_330);
x_331 = lean_ctor_get(x_8, 2);
lean_inc(x_331);
x_332 = lean_ctor_get(x_8, 3);
lean_inc(x_332);
x_333 = l_Lean_replaceRef(x_238, x_332);
x_334 = l_Lean_replaceRef(x_333, x_332);
lean_dec(x_333);
x_335 = l_Lean_replaceRef(x_334, x_332);
lean_dec(x_332);
lean_dec(x_334);
x_336 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_336, 0, x_329);
lean_ctor_set(x_336, 1, x_330);
lean_ctor_set(x_336, 2, x_331);
lean_ctor_set(x_336, 3, x_335);
x_337 = 0;
x_338 = lean_box(0);
lean_inc(x_6);
x_339 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_328, x_337, x_338, x_6, x_7, x_336, x_9, x_243);
lean_dec(x_336);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 x_342 = x_339;
} else {
 lean_dec_ref(x_339);
 x_342 = lean_box(0);
}
x_343 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_340);
lean_inc(x_343);
x_344 = l_Lean_mkApp(x_35, x_343);
x_345 = lean_expr_instantiate1(x_327, x_343);
lean_dec(x_327);
x_346 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_346, 0, x_343);
x_347 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_347, 0, x_238);
lean_ctor_set(x_347, 1, x_30);
lean_ctor_set(x_347, 2, x_239);
lean_ctor_set(x_347, 3, x_346);
lean_ctor_set(x_3, 1, x_237);
lean_ctor_set(x_3, 0, x_347);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_345);
lean_ctor_set(x_2, 0, x_344);
if (lean_is_scalar(x_342)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_342;
}
lean_ctor_set(x_348, 0, x_2);
lean_ctor_set(x_348, 1, x_341);
x_15 = x_348;
goto block_23;
}
}
}
else
{
lean_object* x_349; 
lean_dec(x_239);
lean_free_object(x_29);
lean_dec(x_237);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_349 = lean_box(0);
x_244 = x_349;
goto block_257;
}
block_257:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_244);
x_245 = l_Lean_indentExpr(x_242);
x_246 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_247 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_245);
x_248 = lean_ctor_get(x_8, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_8, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_8, 2);
lean_inc(x_250);
x_251 = lean_ctor_get(x_8, 3);
lean_inc(x_251);
x_252 = l_Lean_replaceRef(x_238, x_251);
lean_dec(x_238);
x_253 = l_Lean_replaceRef(x_252, x_251);
lean_dec(x_252);
x_254 = l_Lean_replaceRef(x_253, x_251);
lean_dec(x_251);
lean_dec(x_253);
x_255 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_255, 0, x_248);
lean_ctor_set(x_255, 1, x_249);
lean_ctor_set(x_255, 2, x_250);
lean_ctor_set(x_255, 3, x_254);
lean_inc(x_4);
lean_inc(x_1);
x_256 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_240, x_1, x_247, x_4, x_5, x_6, x_7, x_255, x_9, x_243);
lean_dec(x_255);
x_15 = x_256;
goto block_23;
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_free_object(x_29);
lean_dec(x_237);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_350 = lean_ctor_get(x_241, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_241, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_352 = x_241;
} else {
 lean_dec_ref(x_241);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_350);
lean_ctor_set(x_353, 1, x_351);
x_15 = x_353;
goto block_23;
}
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_354 = lean_ctor_get(x_29, 0);
x_355 = lean_ctor_get(x_29, 1);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_29);
x_356 = lean_ctor_get(x_13, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_13, 2);
lean_inc(x_357);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 x_358 = x_13;
} else {
 lean_dec_ref(x_13);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_32, 1);
lean_inc(x_359);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_360 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(x_354, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
if (lean_obj_tag(x_361) == 7)
{
lean_dec(x_359);
switch (lean_obj_tag(x_357)) {
case 0:
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; lean_object* x_383; 
x_377 = lean_ctor_get(x_361, 1);
lean_inc(x_377);
x_378 = lean_ctor_get(x_361, 2);
lean_inc(x_378);
lean_dec(x_361);
x_379 = lean_ctor_get(x_357, 0);
lean_inc(x_379);
x_380 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_380, 0, x_377);
x_381 = lean_box(0);
x_382 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_383 = l_Lean_Elab_Term_elabTermEnsuringType(x_379, x_380, x_382, x_381, x_4, x_5, x_6, x_7, x_8, x_9, x_362);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_386 = x_383;
} else {
 lean_dec_ref(x_383);
 x_386 = lean_box(0);
}
lean_inc(x_384);
x_387 = l_Lean_mkApp(x_35, x_384);
x_388 = lean_expr_instantiate1(x_378, x_384);
lean_dec(x_378);
x_389 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_389, 0, x_384);
if (lean_is_scalar(x_358)) {
 x_390 = lean_alloc_ctor(0, 4, 0);
} else {
 x_390 = x_358;
}
lean_ctor_set(x_390, 0, x_356);
lean_ctor_set(x_390, 1, x_30);
lean_ctor_set(x_390, 2, x_357);
lean_ctor_set(x_390, 3, x_389);
lean_ctor_set(x_3, 1, x_355);
lean_ctor_set(x_3, 0, x_390);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_388);
lean_ctor_set(x_391, 1, x_3);
lean_ctor_set(x_2, 1, x_391);
lean_ctor_set(x_2, 0, x_387);
if (lean_is_scalar(x_386)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_386;
}
lean_ctor_set(x_392, 0, x_2);
lean_ctor_set(x_392, 1, x_385);
x_15 = x_392;
goto block_23;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_378);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_393 = lean_ctor_get(x_383, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_383, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_395 = x_383;
} else {
 lean_dec_ref(x_383);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_393);
lean_ctor_set(x_396, 1, x_394);
x_15 = x_396;
goto block_23;
}
}
case 1:
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_397 = lean_ctor_get(x_361, 1);
lean_inc(x_397);
x_398 = lean_ctor_get(x_361, 2);
lean_inc(x_398);
lean_dec(x_361);
x_399 = lean_ctor_get(x_357, 0);
lean_inc(x_399);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 x_400 = x_357;
} else {
 lean_dec_ref(x_357);
 x_400 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_397);
x_401 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_399, x_397, x_4, x_5, x_6, x_7, x_8, x_9, x_362);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_free_object(x_2);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_404, 0, x_397);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_404);
x_405 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_399, x_404, x_4, x_5, x_6, x_7, x_8, x_9, x_403);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_408 = lean_ctor_get(x_406, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_406, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 x_410 = x_406;
} else {
 lean_dec_ref(x_406);
 x_410 = lean_box(0);
}
x_411 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_412 = l_Lean_Elab_Term_ensureHasType(x_404, x_408, x_411, x_4, x_5, x_6, x_7, x_8, x_9, x_407);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 x_415 = x_412;
} else {
 lean_dec_ref(x_412);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_416 = lean_alloc_ctor(1, 1, 0);
} else {
 x_416 = x_400;
}
lean_ctor_set(x_416, 0, x_409);
lean_inc(x_413);
x_417 = l_Lean_mkApp(x_35, x_413);
x_418 = lean_expr_instantiate1(x_398, x_413);
lean_dec(x_398);
x_419 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_419, 0, x_413);
if (lean_is_scalar(x_358)) {
 x_420 = lean_alloc_ctor(0, 4, 0);
} else {
 x_420 = x_358;
}
lean_ctor_set(x_420, 0, x_356);
lean_ctor_set(x_420, 1, x_30);
lean_ctor_set(x_420, 2, x_416);
lean_ctor_set(x_420, 3, x_419);
lean_ctor_set(x_3, 1, x_355);
lean_ctor_set(x_3, 0, x_420);
if (lean_is_scalar(x_410)) {
 x_421 = lean_alloc_ctor(0, 2, 0);
} else {
 x_421 = x_410;
}
lean_ctor_set(x_421, 0, x_418);
lean_ctor_set(x_421, 1, x_3);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_417);
lean_ctor_set(x_422, 1, x_421);
if (lean_is_scalar(x_415)) {
 x_423 = lean_alloc_ctor(0, 2, 0);
} else {
 x_423 = x_415;
}
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_414);
x_15 = x_423;
goto block_23;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_400);
lean_dec(x_398);
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_424 = lean_ctor_get(x_412, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_412, 1);
lean_inc(x_425);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 x_426 = x_412;
} else {
 lean_dec_ref(x_412);
 x_426 = lean_box(0);
}
if (lean_is_scalar(x_426)) {
 x_427 = lean_alloc_ctor(1, 2, 0);
} else {
 x_427 = x_426;
}
lean_ctor_set(x_427, 0, x_424);
lean_ctor_set(x_427, 1, x_425);
x_15 = x_427;
goto block_23;
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_404);
lean_dec(x_400);
lean_dec(x_398);
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_428 = lean_ctor_get(x_405, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_405, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_430 = x_405;
} else {
 lean_dec_ref(x_405);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 2, 0);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_428);
lean_ctor_set(x_431, 1, x_429);
x_15 = x_431;
goto block_23;
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_399);
lean_dec(x_397);
x_432 = lean_ctor_get(x_401, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_433 = x_401;
} else {
 lean_dec_ref(x_401);
 x_433 = lean_box(0);
}
x_434 = lean_ctor_get(x_402, 0);
lean_inc(x_434);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 x_435 = x_402;
} else {
 lean_dec_ref(x_402);
 x_435 = lean_box(0);
}
x_436 = l_Lean_mkHole(x_356);
if (lean_is_scalar(x_400)) {
 x_437 = lean_alloc_ctor(0, 1, 0);
} else {
 x_437 = x_400;
 lean_ctor_set_tag(x_437, 0);
}
lean_ctor_set(x_437, 0, x_436);
lean_inc(x_434);
x_438 = l_Lean_mkApp(x_35, x_434);
x_439 = lean_expr_instantiate1(x_398, x_434);
lean_dec(x_398);
if (lean_is_scalar(x_435)) {
 x_440 = lean_alloc_ctor(1, 1, 0);
} else {
 x_440 = x_435;
}
lean_ctor_set(x_440, 0, x_434);
if (lean_is_scalar(x_358)) {
 x_441 = lean_alloc_ctor(0, 4, 0);
} else {
 x_441 = x_358;
}
lean_ctor_set(x_441, 0, x_356);
lean_ctor_set(x_441, 1, x_30);
lean_ctor_set(x_441, 2, x_437);
lean_ctor_set(x_441, 3, x_440);
lean_ctor_set(x_3, 1, x_355);
lean_ctor_set(x_3, 0, x_441);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_439);
lean_ctor_set(x_442, 1, x_3);
lean_ctor_set(x_2, 1, x_442);
lean_ctor_set(x_2, 0, x_438);
if (lean_is_scalar(x_433)) {
 x_443 = lean_alloc_ctor(0, 2, 0);
} else {
 x_443 = x_433;
}
lean_ctor_set(x_443, 0, x_2);
lean_ctor_set(x_443, 1, x_432);
x_15 = x_443;
goto block_23;
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_397);
lean_dec(x_358);
lean_dec(x_356);
lean_dec(x_355);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_444 = lean_ctor_get(x_401, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_401, 1);
lean_inc(x_445);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_446 = x_401;
} else {
 lean_dec_ref(x_401);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(1, 2, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_445);
x_15 = x_447;
goto block_23;
}
}
default: 
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_448 = lean_ctor_get(x_361, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_361, 2);
lean_inc(x_449);
lean_dec(x_361);
x_450 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_450, 0, x_448);
x_451 = lean_ctor_get(x_8, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_8, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_8, 2);
lean_inc(x_453);
x_454 = lean_ctor_get(x_8, 3);
lean_inc(x_454);
x_455 = l_Lean_replaceRef(x_356, x_454);
x_456 = l_Lean_replaceRef(x_455, x_454);
lean_dec(x_455);
x_457 = l_Lean_replaceRef(x_456, x_454);
lean_dec(x_454);
lean_dec(x_456);
x_458 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_458, 0, x_451);
lean_ctor_set(x_458, 1, x_452);
lean_ctor_set(x_458, 2, x_453);
lean_ctor_set(x_458, 3, x_457);
x_459 = 0;
x_460 = lean_box(0);
lean_inc(x_6);
x_461 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_450, x_459, x_460, x_6, x_7, x_458, x_9, x_362);
lean_dec(x_458);
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_464 = x_461;
} else {
 lean_dec_ref(x_461);
 x_464 = lean_box(0);
}
x_465 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_462);
lean_inc(x_465);
x_466 = l_Lean_mkApp(x_35, x_465);
x_467 = lean_expr_instantiate1(x_449, x_465);
lean_dec(x_449);
x_468 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_468, 0, x_465);
if (lean_is_scalar(x_358)) {
 x_469 = lean_alloc_ctor(0, 4, 0);
} else {
 x_469 = x_358;
}
lean_ctor_set(x_469, 0, x_356);
lean_ctor_set(x_469, 1, x_30);
lean_ctor_set(x_469, 2, x_357);
lean_ctor_set(x_469, 3, x_468);
lean_ctor_set(x_3, 1, x_355);
lean_ctor_set(x_3, 0, x_469);
x_470 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_470, 0, x_467);
lean_ctor_set(x_470, 1, x_3);
lean_ctor_set(x_2, 1, x_470);
lean_ctor_set(x_2, 0, x_466);
if (lean_is_scalar(x_464)) {
 x_471 = lean_alloc_ctor(0, 2, 0);
} else {
 x_471 = x_464;
}
lean_ctor_set(x_471, 0, x_2);
lean_ctor_set(x_471, 1, x_463);
x_15 = x_471;
goto block_23;
}
}
}
else
{
lean_object* x_472; 
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_355);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_472 = lean_box(0);
x_363 = x_472;
goto block_376;
}
block_376:
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_363);
x_364 = l_Lean_indentExpr(x_361);
x_365 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_366 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_364);
x_367 = lean_ctor_get(x_8, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_8, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_8, 2);
lean_inc(x_369);
x_370 = lean_ctor_get(x_8, 3);
lean_inc(x_370);
x_371 = l_Lean_replaceRef(x_356, x_370);
lean_dec(x_356);
x_372 = l_Lean_replaceRef(x_371, x_370);
lean_dec(x_371);
x_373 = l_Lean_replaceRef(x_372, x_370);
lean_dec(x_370);
lean_dec(x_372);
x_374 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_374, 0, x_367);
lean_ctor_set(x_374, 1, x_368);
lean_ctor_set(x_374, 2, x_369);
lean_ctor_set(x_374, 3, x_373);
lean_inc(x_4);
lean_inc(x_1);
x_375 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_359, x_1, x_366, x_4, x_5, x_6, x_7, x_374, x_9, x_362);
lean_dec(x_374);
x_15 = x_375;
goto block_23;
}
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_473 = lean_ctor_get(x_360, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_360, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_475 = x_360;
} else {
 lean_dec_ref(x_360);
 x_475 = lean_box(0);
}
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(1, 2, 0);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_473);
lean_ctor_set(x_476, 1, x_474);
x_15 = x_476;
goto block_23;
}
}
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_477 = lean_ctor_get(x_2, 0);
lean_inc(x_477);
lean_dec(x_2);
x_478 = lean_ctor_get(x_29, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_29, 1);
lean_inc(x_479);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_480 = x_29;
} else {
 lean_dec_ref(x_29);
 x_480 = lean_box(0);
}
x_481 = lean_ctor_get(x_13, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_13, 2);
lean_inc(x_482);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 x_483 = x_13;
} else {
 lean_dec_ref(x_13);
 x_483 = lean_box(0);
}
x_484 = lean_ctor_get(x_32, 1);
lean_inc(x_484);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_485 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(x_478, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
lean_dec(x_485);
if (lean_obj_tag(x_486) == 7)
{
lean_dec(x_484);
switch (lean_obj_tag(x_482)) {
case 0:
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; 
x_502 = lean_ctor_get(x_486, 1);
lean_inc(x_502);
x_503 = lean_ctor_get(x_486, 2);
lean_inc(x_503);
lean_dec(x_486);
x_504 = lean_ctor_get(x_482, 0);
lean_inc(x_504);
x_505 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_505, 0, x_502);
x_506 = lean_box(0);
x_507 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_508 = l_Lean_Elab_Term_elabTermEnsuringType(x_504, x_505, x_507, x_506, x_4, x_5, x_6, x_7, x_8, x_9, x_487);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_511 = x_508;
} else {
 lean_dec_ref(x_508);
 x_511 = lean_box(0);
}
lean_inc(x_509);
x_512 = l_Lean_mkApp(x_477, x_509);
x_513 = lean_expr_instantiate1(x_503, x_509);
lean_dec(x_503);
x_514 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_514, 0, x_509);
if (lean_is_scalar(x_483)) {
 x_515 = lean_alloc_ctor(0, 4, 0);
} else {
 x_515 = x_483;
}
lean_ctor_set(x_515, 0, x_481);
lean_ctor_set(x_515, 1, x_30);
lean_ctor_set(x_515, 2, x_482);
lean_ctor_set(x_515, 3, x_514);
lean_ctor_set(x_3, 1, x_479);
lean_ctor_set(x_3, 0, x_515);
if (lean_is_scalar(x_480)) {
 x_516 = lean_alloc_ctor(0, 2, 0);
} else {
 x_516 = x_480;
}
lean_ctor_set(x_516, 0, x_513);
lean_ctor_set(x_516, 1, x_3);
x_517 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_517, 0, x_512);
lean_ctor_set(x_517, 1, x_516);
if (lean_is_scalar(x_511)) {
 x_518 = lean_alloc_ctor(0, 2, 0);
} else {
 x_518 = x_511;
}
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_510);
x_15 = x_518;
goto block_23;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_dec(x_503);
lean_dec(x_483);
lean_dec(x_482);
lean_dec(x_481);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_477);
lean_dec(x_30);
lean_free_object(x_3);
x_519 = lean_ctor_get(x_508, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_508, 1);
lean_inc(x_520);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_521 = x_508;
} else {
 lean_dec_ref(x_508);
 x_521 = lean_box(0);
}
if (lean_is_scalar(x_521)) {
 x_522 = lean_alloc_ctor(1, 2, 0);
} else {
 x_522 = x_521;
}
lean_ctor_set(x_522, 0, x_519);
lean_ctor_set(x_522, 1, x_520);
x_15 = x_522;
goto block_23;
}
}
case 1:
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_523 = lean_ctor_get(x_486, 1);
lean_inc(x_523);
x_524 = lean_ctor_get(x_486, 2);
lean_inc(x_524);
lean_dec(x_486);
x_525 = lean_ctor_get(x_482, 0);
lean_inc(x_525);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 x_526 = x_482;
} else {
 lean_dec_ref(x_482);
 x_526 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_523);
x_527 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_525, x_523, x_4, x_5, x_6, x_7, x_8, x_9, x_487);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
lean_dec(x_527);
x_530 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_530, 0, x_523);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_530);
x_531 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_525, x_530, x_4, x_5, x_6, x_7, x_8, x_9, x_529);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
lean_dec(x_531);
x_534 = lean_ctor_get(x_532, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_532, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_536 = x_532;
} else {
 lean_dec_ref(x_532);
 x_536 = lean_box(0);
}
x_537 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_538 = l_Lean_Elab_Term_ensureHasType(x_530, x_534, x_537, x_4, x_5, x_6, x_7, x_8, x_9, x_533);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_538, 1);
lean_inc(x_540);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 lean_ctor_release(x_538, 1);
 x_541 = x_538;
} else {
 lean_dec_ref(x_538);
 x_541 = lean_box(0);
}
if (lean_is_scalar(x_526)) {
 x_542 = lean_alloc_ctor(1, 1, 0);
} else {
 x_542 = x_526;
}
lean_ctor_set(x_542, 0, x_535);
lean_inc(x_539);
x_543 = l_Lean_mkApp(x_477, x_539);
x_544 = lean_expr_instantiate1(x_524, x_539);
lean_dec(x_524);
x_545 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_545, 0, x_539);
if (lean_is_scalar(x_483)) {
 x_546 = lean_alloc_ctor(0, 4, 0);
} else {
 x_546 = x_483;
}
lean_ctor_set(x_546, 0, x_481);
lean_ctor_set(x_546, 1, x_30);
lean_ctor_set(x_546, 2, x_542);
lean_ctor_set(x_546, 3, x_545);
lean_ctor_set(x_3, 1, x_479);
lean_ctor_set(x_3, 0, x_546);
if (lean_is_scalar(x_536)) {
 x_547 = lean_alloc_ctor(0, 2, 0);
} else {
 x_547 = x_536;
}
lean_ctor_set(x_547, 0, x_544);
lean_ctor_set(x_547, 1, x_3);
if (lean_is_scalar(x_480)) {
 x_548 = lean_alloc_ctor(0, 2, 0);
} else {
 x_548 = x_480;
}
lean_ctor_set(x_548, 0, x_543);
lean_ctor_set(x_548, 1, x_547);
if (lean_is_scalar(x_541)) {
 x_549 = lean_alloc_ctor(0, 2, 0);
} else {
 x_549 = x_541;
}
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_540);
x_15 = x_549;
goto block_23;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
lean_dec(x_536);
lean_dec(x_535);
lean_dec(x_526);
lean_dec(x_524);
lean_dec(x_483);
lean_dec(x_481);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_477);
lean_dec(x_30);
lean_free_object(x_3);
x_550 = lean_ctor_get(x_538, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_538, 1);
lean_inc(x_551);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 lean_ctor_release(x_538, 1);
 x_552 = x_538;
} else {
 lean_dec_ref(x_538);
 x_552 = lean_box(0);
}
if (lean_is_scalar(x_552)) {
 x_553 = lean_alloc_ctor(1, 2, 0);
} else {
 x_553 = x_552;
}
lean_ctor_set(x_553, 0, x_550);
lean_ctor_set(x_553, 1, x_551);
x_15 = x_553;
goto block_23;
}
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec(x_530);
lean_dec(x_526);
lean_dec(x_524);
lean_dec(x_483);
lean_dec(x_481);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_477);
lean_dec(x_30);
lean_free_object(x_3);
x_554 = lean_ctor_get(x_531, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_531, 1);
lean_inc(x_555);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 x_556 = x_531;
} else {
 lean_dec_ref(x_531);
 x_556 = lean_box(0);
}
if (lean_is_scalar(x_556)) {
 x_557 = lean_alloc_ctor(1, 2, 0);
} else {
 x_557 = x_556;
}
lean_ctor_set(x_557, 0, x_554);
lean_ctor_set(x_557, 1, x_555);
x_15 = x_557;
goto block_23;
}
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
lean_dec(x_525);
lean_dec(x_523);
x_558 = lean_ctor_get(x_527, 1);
lean_inc(x_558);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 lean_ctor_release(x_527, 1);
 x_559 = x_527;
} else {
 lean_dec_ref(x_527);
 x_559 = lean_box(0);
}
x_560 = lean_ctor_get(x_528, 0);
lean_inc(x_560);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 x_561 = x_528;
} else {
 lean_dec_ref(x_528);
 x_561 = lean_box(0);
}
x_562 = l_Lean_mkHole(x_481);
if (lean_is_scalar(x_526)) {
 x_563 = lean_alloc_ctor(0, 1, 0);
} else {
 x_563 = x_526;
 lean_ctor_set_tag(x_563, 0);
}
lean_ctor_set(x_563, 0, x_562);
lean_inc(x_560);
x_564 = l_Lean_mkApp(x_477, x_560);
x_565 = lean_expr_instantiate1(x_524, x_560);
lean_dec(x_524);
if (lean_is_scalar(x_561)) {
 x_566 = lean_alloc_ctor(1, 1, 0);
} else {
 x_566 = x_561;
}
lean_ctor_set(x_566, 0, x_560);
if (lean_is_scalar(x_483)) {
 x_567 = lean_alloc_ctor(0, 4, 0);
} else {
 x_567 = x_483;
}
lean_ctor_set(x_567, 0, x_481);
lean_ctor_set(x_567, 1, x_30);
lean_ctor_set(x_567, 2, x_563);
lean_ctor_set(x_567, 3, x_566);
lean_ctor_set(x_3, 1, x_479);
lean_ctor_set(x_3, 0, x_567);
if (lean_is_scalar(x_480)) {
 x_568 = lean_alloc_ctor(0, 2, 0);
} else {
 x_568 = x_480;
}
lean_ctor_set(x_568, 0, x_565);
lean_ctor_set(x_568, 1, x_3);
x_569 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_569, 0, x_564);
lean_ctor_set(x_569, 1, x_568);
if (lean_is_scalar(x_559)) {
 x_570 = lean_alloc_ctor(0, 2, 0);
} else {
 x_570 = x_559;
}
lean_ctor_set(x_570, 0, x_569);
lean_ctor_set(x_570, 1, x_558);
x_15 = x_570;
goto block_23;
}
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
lean_dec(x_526);
lean_dec(x_525);
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_483);
lean_dec(x_481);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_477);
lean_dec(x_30);
lean_free_object(x_3);
x_571 = lean_ctor_get(x_527, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_527, 1);
lean_inc(x_572);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 lean_ctor_release(x_527, 1);
 x_573 = x_527;
} else {
 lean_dec_ref(x_527);
 x_573 = lean_box(0);
}
if (lean_is_scalar(x_573)) {
 x_574 = lean_alloc_ctor(1, 2, 0);
} else {
 x_574 = x_573;
}
lean_ctor_set(x_574, 0, x_571);
lean_ctor_set(x_574, 1, x_572);
x_15 = x_574;
goto block_23;
}
}
default: 
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; uint8_t x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_575 = lean_ctor_get(x_486, 1);
lean_inc(x_575);
x_576 = lean_ctor_get(x_486, 2);
lean_inc(x_576);
lean_dec(x_486);
x_577 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_577, 0, x_575);
x_578 = lean_ctor_get(x_8, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_8, 1);
lean_inc(x_579);
x_580 = lean_ctor_get(x_8, 2);
lean_inc(x_580);
x_581 = lean_ctor_get(x_8, 3);
lean_inc(x_581);
x_582 = l_Lean_replaceRef(x_481, x_581);
x_583 = l_Lean_replaceRef(x_582, x_581);
lean_dec(x_582);
x_584 = l_Lean_replaceRef(x_583, x_581);
lean_dec(x_581);
lean_dec(x_583);
x_585 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_585, 0, x_578);
lean_ctor_set(x_585, 1, x_579);
lean_ctor_set(x_585, 2, x_580);
lean_ctor_set(x_585, 3, x_584);
x_586 = 0;
x_587 = lean_box(0);
lean_inc(x_6);
x_588 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_577, x_586, x_587, x_6, x_7, x_585, x_9, x_487);
lean_dec(x_585);
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_588, 1);
lean_inc(x_590);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 x_591 = x_588;
} else {
 lean_dec_ref(x_588);
 x_591 = lean_box(0);
}
x_592 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_589);
lean_inc(x_592);
x_593 = l_Lean_mkApp(x_477, x_592);
x_594 = lean_expr_instantiate1(x_576, x_592);
lean_dec(x_576);
x_595 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_595, 0, x_592);
if (lean_is_scalar(x_483)) {
 x_596 = lean_alloc_ctor(0, 4, 0);
} else {
 x_596 = x_483;
}
lean_ctor_set(x_596, 0, x_481);
lean_ctor_set(x_596, 1, x_30);
lean_ctor_set(x_596, 2, x_482);
lean_ctor_set(x_596, 3, x_595);
lean_ctor_set(x_3, 1, x_479);
lean_ctor_set(x_3, 0, x_596);
if (lean_is_scalar(x_480)) {
 x_597 = lean_alloc_ctor(0, 2, 0);
} else {
 x_597 = x_480;
}
lean_ctor_set(x_597, 0, x_594);
lean_ctor_set(x_597, 1, x_3);
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_593);
lean_ctor_set(x_598, 1, x_597);
if (lean_is_scalar(x_591)) {
 x_599 = lean_alloc_ctor(0, 2, 0);
} else {
 x_599 = x_591;
}
lean_ctor_set(x_599, 0, x_598);
lean_ctor_set(x_599, 1, x_590);
x_15 = x_599;
goto block_23;
}
}
}
else
{
lean_object* x_600; 
lean_dec(x_483);
lean_dec(x_482);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_477);
lean_dec(x_30);
lean_free_object(x_3);
x_600 = lean_box(0);
x_488 = x_600;
goto block_501;
}
block_501:
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_488);
x_489 = l_Lean_indentExpr(x_486);
x_490 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_491 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set(x_491, 1, x_489);
x_492 = lean_ctor_get(x_8, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_8, 1);
lean_inc(x_493);
x_494 = lean_ctor_get(x_8, 2);
lean_inc(x_494);
x_495 = lean_ctor_get(x_8, 3);
lean_inc(x_495);
x_496 = l_Lean_replaceRef(x_481, x_495);
lean_dec(x_481);
x_497 = l_Lean_replaceRef(x_496, x_495);
lean_dec(x_496);
x_498 = l_Lean_replaceRef(x_497, x_495);
lean_dec(x_495);
lean_dec(x_497);
x_499 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_499, 0, x_492);
lean_ctor_set(x_499, 1, x_493);
lean_ctor_set(x_499, 2, x_494);
lean_ctor_set(x_499, 3, x_498);
lean_inc(x_4);
lean_inc(x_1);
x_500 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_484, x_1, x_491, x_4, x_5, x_6, x_7, x_499, x_9, x_487);
lean_dec(x_499);
x_15 = x_500;
goto block_23;
}
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_482);
lean_dec(x_481);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_477);
lean_dec(x_30);
lean_free_object(x_3);
x_601 = lean_ctor_get(x_485, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_485, 1);
lean_inc(x_602);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 lean_ctor_release(x_485, 1);
 x_603 = x_485;
} else {
 lean_dec_ref(x_485);
 x_603 = lean_box(0);
}
if (lean_is_scalar(x_603)) {
 x_604 = lean_alloc_ctor(1, 2, 0);
} else {
 x_604 = x_603;
}
lean_ctor_set(x_604, 0, x_601);
lean_ctor_set(x_604, 1, x_602);
x_15 = x_604;
goto block_23;
}
}
}
else
{
lean_object* x_605; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_3);
lean_dec(x_2);
x_605 = lean_box(0);
x_24 = x_605;
goto block_28;
}
}
else
{
lean_object* x_606; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_3);
lean_dec(x_2);
x_606 = lean_box(0);
x_24 = x_606;
goto block_28;
}
}
block_23:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_2 = x_16;
x_3 = x_14;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
block_28:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
lean_dec(x_13);
x_26 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3;
lean_inc(x_8);
lean_inc(x_4);
x_27 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_25, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_25);
x_15 = x_27;
goto block_23;
}
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_618; lean_object* x_623; lean_object* x_624; 
x_607 = lean_ctor_get(x_3, 0);
x_608 = lean_ctor_get(x_3, 1);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_3);
x_623 = lean_ctor_get(x_2, 1);
lean_inc(x_623);
x_624 = lean_ctor_get(x_607, 1);
lean_inc(x_624);
if (lean_obj_tag(x_624) == 0)
{
lean_object* x_625; 
lean_dec(x_623);
lean_dec(x_2);
x_625 = lean_box(0);
x_618 = x_625;
goto block_622;
}
else
{
lean_object* x_626; 
x_626 = lean_ctor_get(x_624, 0);
lean_inc(x_626);
if (lean_obj_tag(x_626) == 0)
{
lean_object* x_627; 
x_627 = lean_ctor_get(x_624, 1);
lean_inc(x_627);
if (lean_obj_tag(x_627) == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_628 = lean_ctor_get(x_2, 0);
lean_inc(x_628);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_629 = x_2;
} else {
 lean_dec_ref(x_2);
 x_629 = lean_box(0);
}
x_630 = lean_ctor_get(x_623, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_623, 1);
lean_inc(x_631);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 lean_ctor_release(x_623, 1);
 x_632 = x_623;
} else {
 lean_dec_ref(x_623);
 x_632 = lean_box(0);
}
x_633 = lean_ctor_get(x_607, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_607, 2);
lean_inc(x_634);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 lean_ctor_release(x_607, 1);
 lean_ctor_release(x_607, 2);
 lean_ctor_release(x_607, 3);
 x_635 = x_607;
} else {
 lean_dec_ref(x_607);
 x_635 = lean_box(0);
}
x_636 = lean_ctor_get(x_626, 1);
lean_inc(x_636);
lean_dec(x_626);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_637 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(x_630, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_637) == 0)
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_638 = lean_ctor_get(x_637, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_637, 1);
lean_inc(x_639);
lean_dec(x_637);
if (lean_obj_tag(x_638) == 7)
{
lean_dec(x_636);
switch (lean_obj_tag(x_634)) {
case 0:
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; uint8_t x_659; lean_object* x_660; 
x_654 = lean_ctor_get(x_638, 1);
lean_inc(x_654);
x_655 = lean_ctor_get(x_638, 2);
lean_inc(x_655);
lean_dec(x_638);
x_656 = lean_ctor_get(x_634, 0);
lean_inc(x_656);
x_657 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_657, 0, x_654);
x_658 = lean_box(0);
x_659 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_660 = l_Lean_Elab_Term_elabTermEnsuringType(x_656, x_657, x_659, x_658, x_4, x_5, x_6, x_7, x_8, x_9, x_639);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_660, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 lean_ctor_release(x_660, 1);
 x_663 = x_660;
} else {
 lean_dec_ref(x_660);
 x_663 = lean_box(0);
}
lean_inc(x_661);
x_664 = l_Lean_mkApp(x_628, x_661);
x_665 = lean_expr_instantiate1(x_655, x_661);
lean_dec(x_655);
x_666 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_666, 0, x_661);
if (lean_is_scalar(x_635)) {
 x_667 = lean_alloc_ctor(0, 4, 0);
} else {
 x_667 = x_635;
}
lean_ctor_set(x_667, 0, x_633);
lean_ctor_set(x_667, 1, x_624);
lean_ctor_set(x_667, 2, x_634);
lean_ctor_set(x_667, 3, x_666);
x_668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_668, 0, x_667);
lean_ctor_set(x_668, 1, x_631);
if (lean_is_scalar(x_632)) {
 x_669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_669 = x_632;
}
lean_ctor_set(x_669, 0, x_665);
lean_ctor_set(x_669, 1, x_668);
if (lean_is_scalar(x_629)) {
 x_670 = lean_alloc_ctor(0, 2, 0);
} else {
 x_670 = x_629;
}
lean_ctor_set(x_670, 0, x_664);
lean_ctor_set(x_670, 1, x_669);
if (lean_is_scalar(x_663)) {
 x_671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_671 = x_663;
}
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_662);
x_609 = x_671;
goto block_617;
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
lean_dec(x_655);
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_629);
lean_dec(x_628);
lean_dec(x_624);
x_672 = lean_ctor_get(x_660, 0);
lean_inc(x_672);
x_673 = lean_ctor_get(x_660, 1);
lean_inc(x_673);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 lean_ctor_release(x_660, 1);
 x_674 = x_660;
} else {
 lean_dec_ref(x_660);
 x_674 = lean_box(0);
}
if (lean_is_scalar(x_674)) {
 x_675 = lean_alloc_ctor(1, 2, 0);
} else {
 x_675 = x_674;
}
lean_ctor_set(x_675, 0, x_672);
lean_ctor_set(x_675, 1, x_673);
x_609 = x_675;
goto block_617;
}
}
case 1:
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_676 = lean_ctor_get(x_638, 1);
lean_inc(x_676);
x_677 = lean_ctor_get(x_638, 2);
lean_inc(x_677);
lean_dec(x_638);
x_678 = lean_ctor_get(x_634, 0);
lean_inc(x_678);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 x_679 = x_634;
} else {
 lean_dec_ref(x_634);
 x_679 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_676);
x_680 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_678, x_676, x_4, x_5, x_6, x_7, x_8, x_9, x_639);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; 
lean_dec(x_629);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
lean_dec(x_680);
x_683 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_683, 0, x_676);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_683);
x_684 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_678, x_683, x_4, x_5, x_6, x_7, x_8, x_9, x_682);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_685 = lean_ctor_get(x_684, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_684, 1);
lean_inc(x_686);
lean_dec(x_684);
x_687 = lean_ctor_get(x_685, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_685, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 x_689 = x_685;
} else {
 lean_dec_ref(x_685);
 x_689 = lean_box(0);
}
x_690 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_691 = l_Lean_Elab_Term_ensureHasType(x_683, x_687, x_690, x_4, x_5, x_6, x_7, x_8, x_9, x_686);
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_692 = lean_ctor_get(x_691, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_691, 1);
lean_inc(x_693);
if (lean_is_exclusive(x_691)) {
 lean_ctor_release(x_691, 0);
 lean_ctor_release(x_691, 1);
 x_694 = x_691;
} else {
 lean_dec_ref(x_691);
 x_694 = lean_box(0);
}
if (lean_is_scalar(x_679)) {
 x_695 = lean_alloc_ctor(1, 1, 0);
} else {
 x_695 = x_679;
}
lean_ctor_set(x_695, 0, x_688);
lean_inc(x_692);
x_696 = l_Lean_mkApp(x_628, x_692);
x_697 = lean_expr_instantiate1(x_677, x_692);
lean_dec(x_677);
x_698 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_698, 0, x_692);
if (lean_is_scalar(x_635)) {
 x_699 = lean_alloc_ctor(0, 4, 0);
} else {
 x_699 = x_635;
}
lean_ctor_set(x_699, 0, x_633);
lean_ctor_set(x_699, 1, x_624);
lean_ctor_set(x_699, 2, x_695);
lean_ctor_set(x_699, 3, x_698);
x_700 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_631);
if (lean_is_scalar(x_689)) {
 x_701 = lean_alloc_ctor(0, 2, 0);
} else {
 x_701 = x_689;
}
lean_ctor_set(x_701, 0, x_697);
lean_ctor_set(x_701, 1, x_700);
if (lean_is_scalar(x_632)) {
 x_702 = lean_alloc_ctor(0, 2, 0);
} else {
 x_702 = x_632;
}
lean_ctor_set(x_702, 0, x_696);
lean_ctor_set(x_702, 1, x_701);
if (lean_is_scalar(x_694)) {
 x_703 = lean_alloc_ctor(0, 2, 0);
} else {
 x_703 = x_694;
}
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_693);
x_609 = x_703;
goto block_617;
}
else
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
lean_dec(x_689);
lean_dec(x_688);
lean_dec(x_679);
lean_dec(x_677);
lean_dec(x_635);
lean_dec(x_633);
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_628);
lean_dec(x_624);
x_704 = lean_ctor_get(x_691, 0);
lean_inc(x_704);
x_705 = lean_ctor_get(x_691, 1);
lean_inc(x_705);
if (lean_is_exclusive(x_691)) {
 lean_ctor_release(x_691, 0);
 lean_ctor_release(x_691, 1);
 x_706 = x_691;
} else {
 lean_dec_ref(x_691);
 x_706 = lean_box(0);
}
if (lean_is_scalar(x_706)) {
 x_707 = lean_alloc_ctor(1, 2, 0);
} else {
 x_707 = x_706;
}
lean_ctor_set(x_707, 0, x_704);
lean_ctor_set(x_707, 1, x_705);
x_609 = x_707;
goto block_617;
}
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
lean_dec(x_683);
lean_dec(x_679);
lean_dec(x_677);
lean_dec(x_635);
lean_dec(x_633);
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_628);
lean_dec(x_624);
x_708 = lean_ctor_get(x_684, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_684, 1);
lean_inc(x_709);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 x_710 = x_684;
} else {
 lean_dec_ref(x_684);
 x_710 = lean_box(0);
}
if (lean_is_scalar(x_710)) {
 x_711 = lean_alloc_ctor(1, 2, 0);
} else {
 x_711 = x_710;
}
lean_ctor_set(x_711, 0, x_708);
lean_ctor_set(x_711, 1, x_709);
x_609 = x_711;
goto block_617;
}
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
lean_dec(x_678);
lean_dec(x_676);
x_712 = lean_ctor_get(x_680, 1);
lean_inc(x_712);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_713 = x_680;
} else {
 lean_dec_ref(x_680);
 x_713 = lean_box(0);
}
x_714 = lean_ctor_get(x_681, 0);
lean_inc(x_714);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 x_715 = x_681;
} else {
 lean_dec_ref(x_681);
 x_715 = lean_box(0);
}
x_716 = l_Lean_mkHole(x_633);
if (lean_is_scalar(x_679)) {
 x_717 = lean_alloc_ctor(0, 1, 0);
} else {
 x_717 = x_679;
 lean_ctor_set_tag(x_717, 0);
}
lean_ctor_set(x_717, 0, x_716);
lean_inc(x_714);
x_718 = l_Lean_mkApp(x_628, x_714);
x_719 = lean_expr_instantiate1(x_677, x_714);
lean_dec(x_677);
if (lean_is_scalar(x_715)) {
 x_720 = lean_alloc_ctor(1, 1, 0);
} else {
 x_720 = x_715;
}
lean_ctor_set(x_720, 0, x_714);
if (lean_is_scalar(x_635)) {
 x_721 = lean_alloc_ctor(0, 4, 0);
} else {
 x_721 = x_635;
}
lean_ctor_set(x_721, 0, x_633);
lean_ctor_set(x_721, 1, x_624);
lean_ctor_set(x_721, 2, x_717);
lean_ctor_set(x_721, 3, x_720);
x_722 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_722, 0, x_721);
lean_ctor_set(x_722, 1, x_631);
if (lean_is_scalar(x_632)) {
 x_723 = lean_alloc_ctor(0, 2, 0);
} else {
 x_723 = x_632;
}
lean_ctor_set(x_723, 0, x_719);
lean_ctor_set(x_723, 1, x_722);
if (lean_is_scalar(x_629)) {
 x_724 = lean_alloc_ctor(0, 2, 0);
} else {
 x_724 = x_629;
}
lean_ctor_set(x_724, 0, x_718);
lean_ctor_set(x_724, 1, x_723);
if (lean_is_scalar(x_713)) {
 x_725 = lean_alloc_ctor(0, 2, 0);
} else {
 x_725 = x_713;
}
lean_ctor_set(x_725, 0, x_724);
lean_ctor_set(x_725, 1, x_712);
x_609 = x_725;
goto block_617;
}
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
lean_dec(x_679);
lean_dec(x_678);
lean_dec(x_677);
lean_dec(x_676);
lean_dec(x_635);
lean_dec(x_633);
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_629);
lean_dec(x_628);
lean_dec(x_624);
x_726 = lean_ctor_get(x_680, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_680, 1);
lean_inc(x_727);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_728 = x_680;
} else {
 lean_dec_ref(x_680);
 x_728 = lean_box(0);
}
if (lean_is_scalar(x_728)) {
 x_729 = lean_alloc_ctor(1, 2, 0);
} else {
 x_729 = x_728;
}
lean_ctor_set(x_729, 0, x_726);
lean_ctor_set(x_729, 1, x_727);
x_609 = x_729;
goto block_617;
}
}
default: 
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; uint8_t x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_730 = lean_ctor_get(x_638, 1);
lean_inc(x_730);
x_731 = lean_ctor_get(x_638, 2);
lean_inc(x_731);
lean_dec(x_638);
x_732 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_732, 0, x_730);
x_733 = lean_ctor_get(x_8, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_8, 1);
lean_inc(x_734);
x_735 = lean_ctor_get(x_8, 2);
lean_inc(x_735);
x_736 = lean_ctor_get(x_8, 3);
lean_inc(x_736);
x_737 = l_Lean_replaceRef(x_633, x_736);
x_738 = l_Lean_replaceRef(x_737, x_736);
lean_dec(x_737);
x_739 = l_Lean_replaceRef(x_738, x_736);
lean_dec(x_736);
lean_dec(x_738);
x_740 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_740, 0, x_733);
lean_ctor_set(x_740, 1, x_734);
lean_ctor_set(x_740, 2, x_735);
lean_ctor_set(x_740, 3, x_739);
x_741 = 0;
x_742 = lean_box(0);
lean_inc(x_6);
x_743 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_732, x_741, x_742, x_6, x_7, x_740, x_9, x_639);
lean_dec(x_740);
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
if (lean_is_exclusive(x_743)) {
 lean_ctor_release(x_743, 0);
 lean_ctor_release(x_743, 1);
 x_746 = x_743;
} else {
 lean_dec_ref(x_743);
 x_746 = lean_box(0);
}
x_747 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_744);
lean_inc(x_747);
x_748 = l_Lean_mkApp(x_628, x_747);
x_749 = lean_expr_instantiate1(x_731, x_747);
lean_dec(x_731);
x_750 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_750, 0, x_747);
if (lean_is_scalar(x_635)) {
 x_751 = lean_alloc_ctor(0, 4, 0);
} else {
 x_751 = x_635;
}
lean_ctor_set(x_751, 0, x_633);
lean_ctor_set(x_751, 1, x_624);
lean_ctor_set(x_751, 2, x_634);
lean_ctor_set(x_751, 3, x_750);
x_752 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_752, 0, x_751);
lean_ctor_set(x_752, 1, x_631);
if (lean_is_scalar(x_632)) {
 x_753 = lean_alloc_ctor(0, 2, 0);
} else {
 x_753 = x_632;
}
lean_ctor_set(x_753, 0, x_749);
lean_ctor_set(x_753, 1, x_752);
if (lean_is_scalar(x_629)) {
 x_754 = lean_alloc_ctor(0, 2, 0);
} else {
 x_754 = x_629;
}
lean_ctor_set(x_754, 0, x_748);
lean_ctor_set(x_754, 1, x_753);
if (lean_is_scalar(x_746)) {
 x_755 = lean_alloc_ctor(0, 2, 0);
} else {
 x_755 = x_746;
}
lean_ctor_set(x_755, 0, x_754);
lean_ctor_set(x_755, 1, x_745);
x_609 = x_755;
goto block_617;
}
}
}
else
{
lean_object* x_756; 
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_629);
lean_dec(x_628);
lean_dec(x_624);
x_756 = lean_box(0);
x_640 = x_756;
goto block_653;
}
block_653:
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_dec(x_640);
x_641 = l_Lean_indentExpr(x_638);
x_642 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_643 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_641);
x_644 = lean_ctor_get(x_8, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_8, 1);
lean_inc(x_645);
x_646 = lean_ctor_get(x_8, 2);
lean_inc(x_646);
x_647 = lean_ctor_get(x_8, 3);
lean_inc(x_647);
x_648 = l_Lean_replaceRef(x_633, x_647);
lean_dec(x_633);
x_649 = l_Lean_replaceRef(x_648, x_647);
lean_dec(x_648);
x_650 = l_Lean_replaceRef(x_649, x_647);
lean_dec(x_647);
lean_dec(x_649);
x_651 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_651, 0, x_644);
lean_ctor_set(x_651, 1, x_645);
lean_ctor_set(x_651, 2, x_646);
lean_ctor_set(x_651, 3, x_650);
lean_inc(x_4);
lean_inc(x_1);
x_652 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_636, x_1, x_643, x_4, x_5, x_6, x_7, x_651, x_9, x_639);
lean_dec(x_651);
x_609 = x_652;
goto block_617;
}
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
lean_dec(x_636);
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_629);
lean_dec(x_628);
lean_dec(x_624);
x_757 = lean_ctor_get(x_637, 0);
lean_inc(x_757);
x_758 = lean_ctor_get(x_637, 1);
lean_inc(x_758);
if (lean_is_exclusive(x_637)) {
 lean_ctor_release(x_637, 0);
 lean_ctor_release(x_637, 1);
 x_759 = x_637;
} else {
 lean_dec_ref(x_637);
 x_759 = lean_box(0);
}
if (lean_is_scalar(x_759)) {
 x_760 = lean_alloc_ctor(1, 2, 0);
} else {
 x_760 = x_759;
}
lean_ctor_set(x_760, 0, x_757);
lean_ctor_set(x_760, 1, x_758);
x_609 = x_760;
goto block_617;
}
}
else
{
lean_object* x_761; 
lean_dec(x_627);
lean_dec(x_626);
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_2);
x_761 = lean_box(0);
x_618 = x_761;
goto block_622;
}
}
else
{
lean_object* x_762; 
lean_dec(x_626);
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_2);
x_762 = lean_box(0);
x_618 = x_762;
goto block_622;
}
}
block_617:
{
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; lean_object* x_611; 
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec(x_609);
x_2 = x_610;
x_3 = x_608;
x_10 = x_611;
goto _start;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
lean_dec(x_608);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_613 = lean_ctor_get(x_609, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_609, 1);
lean_inc(x_614);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 lean_ctor_release(x_609, 1);
 x_615 = x_609;
} else {
 lean_dec_ref(x_609);
 x_615 = lean_box(0);
}
if (lean_is_scalar(x_615)) {
 x_616 = lean_alloc_ctor(1, 2, 0);
} else {
 x_616 = x_615;
}
lean_ctor_set(x_616, 0, x_613);
lean_ctor_set(x_616, 1, x_614);
return x_616;
}
}
block_622:
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_618);
x_619 = lean_ctor_get(x_607, 0);
lean_inc(x_619);
lean_dec(x_607);
x_620 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3;
lean_inc(x_8);
lean_inc(x_4);
x_621 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_619, x_620, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_619);
x_609 = x_621;
goto block_617;
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_24__elabStruct___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_7, 3);
x_13 = l_Lean_replaceRef(x_10, x_12);
lean_dec(x_10);
x_14 = l_Lean_replaceRef(x_13, x_12);
lean_dec(x_13);
x_15 = l_Lean_replaceRef(x_14, x_12);
lean_dec(x_12);
lean_dec(x_14);
lean_ctor_set(x_7, 3, x_15);
x_16 = lean_st_ref_get(x_8, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_20);
x_21 = l_Lean_getStructureCtor(x_19, x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_22 = l___private_Lean_Elab_StructInst_23__mkCtorHeader(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
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
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_31 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1(x_20, x_29, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 1);
x_39 = lean_ctor_get(x_33, 0);
lean_dec(x_39);
x_40 = l_List_reverse___rarg(x_38);
x_41 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_40);
lean_ctor_set(x_33, 1, x_41);
lean_ctor_set(x_33, 0, x_36);
lean_ctor_set(x_31, 0, x_33);
return x_31;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_dec(x_33);
x_43 = l_List_reverse___rarg(x_42);
x_44 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_31, 0, x_45);
return x_31;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_dec(x_31);
x_47 = lean_ctor_get(x_32, 0);
lean_inc(x_47);
lean_dec(x_32);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_49 = x_33;
} else {
 lean_dec_ref(x_33);
 x_49 = lean_box(0);
}
x_50 = l_List_reverse___rarg(x_48);
x_51 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_50);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_31);
if (x_54 == 0)
{
return x_31;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_31, 0);
x_56 = lean_ctor_get(x_31, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_31);
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
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_22);
if (x_58 == 0)
{
return x_22;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_22, 0);
x_60 = lean_ctor_get(x_22, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_22);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_62 = lean_ctor_get(x_7, 0);
x_63 = lean_ctor_get(x_7, 1);
x_64 = lean_ctor_get(x_7, 2);
x_65 = lean_ctor_get(x_7, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_7);
x_66 = l_Lean_replaceRef(x_10, x_65);
lean_dec(x_10);
x_67 = l_Lean_replaceRef(x_66, x_65);
lean_dec(x_66);
x_68 = l_Lean_replaceRef(x_67, x_65);
lean_dec(x_65);
lean_dec(x_67);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_63);
lean_ctor_set(x_69, 2, x_64);
lean_ctor_set(x_69, 3, x_68);
x_70 = lean_st_ref_get(x_8, x_9);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_74);
x_75 = l_Lean_getStructureCtor(x_73, x_74);
lean_inc(x_8);
lean_inc(x_69);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_76 = l___private_Lean_Elab_StructInst_23__mkCtorHeader(x_75, x_2, x_3, x_4, x_5, x_6, x_69, x_8, x_72);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_85 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1(x_74, x_83, x_84, x_3, x_4, x_5, x_6, x_69, x_8, x_78);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_89 = x_85;
} else {
 lean_dec_ref(x_85);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_86, 0);
lean_inc(x_90);
lean_dec(x_86);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_92 = x_87;
} else {
 lean_dec_ref(x_87);
 x_92 = lean_box(0);
}
x_93 = l_List_reverse___rarg(x_91);
x_94 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_93);
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_92;
}
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_94);
if (lean_is_scalar(x_89)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_89;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_88);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_1);
x_97 = lean_ctor_get(x_85, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_85, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_99 = x_85;
} else {
 lean_dec_ref(x_85);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_74);
lean_dec(x_69);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_101 = lean_ctor_get(x_76, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_76, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_103 = x_76;
} else {
 lean_dec_ref(x_76);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_24__elabStruct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 2);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main(x_6, x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 1);
x_2 = x_9;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
x_4 = lean_array_push(x_2, x_3);
x_5 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_6 = l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___spec__1(x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 2);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
x_10 = l_Nat_max(x_1, x_9);
lean_dec(x_9);
lean_dec(x_1);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_2, 1);
x_2 = x_12;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_23; 
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(x_1, x_24);
lean_dec(x_24);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_23);
x_26 = lean_box(0);
x_3 = x_26;
goto block_22;
}
block_22:
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = l_unreachable_x21___rarg(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_7);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
if (lean_obj_tag(x_11) == 2)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_metavar_ctx_is_expr_assigned(x_1, x_12);
if (x_13 == 0)
{
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
else
{
lean_object* x_14; 
lean_free_object(x_8);
lean_dec(x_2);
x_14 = lean_box(0);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_free_object(x_8);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
if (lean_obj_tag(x_16) == 2)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_metavar_ctx_is_expr_assigned(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_2);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_2);
x_20 = lean_box(0);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
return x_21;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main___lambda__1), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Elab_Term_StructInst_Struct_fields(x_2);
x_5 = l_List_findSome_x3f___main___rarg(x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Name_inhabited;
x_4 = l_unreachable_x21___rarg(x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Name_inhabited;
x_9 = l_unreachable_x21___rarg(x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Name_inhabited;
x_11 = l_unreachable_x21___rarg(x_10);
return x_11;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_10, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_lt(x_24, x_23);
x_26 = lean_box(x_25);
lean_ctor_set(x_10, 0, x_26);
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
x_28 = lean_ctor_get(x_1, 2);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_lt(x_29, x_28);
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_2);
x_4 = lean_name_eq(x_3, x_1);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
return x_6;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_5 = l_List_findSome_x3f___main___rarg(x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_dec(x_2);
x_24 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_25 = (uint8_t)((x_23 << 24) >> 61);
x_26 = l_Lean_BinderInfo_isExplicit(x_25);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_7, 3);
x_29 = l_Lean_replaceRef(x_24, x_28);
lean_dec(x_24);
x_30 = l_Lean_replaceRef(x_29, x_28);
lean_dec(x_29);
x_31 = l_Lean_replaceRef(x_30, x_28);
lean_dec(x_28);
lean_dec(x_30);
lean_ctor_set(x_7, 3, x_31);
if (x_26 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_21);
x_33 = 0;
x_34 = lean_box(0);
lean_inc(x_5);
x_35 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_32, x_33, x_34, x_5, x_6, x_7, x_8, x_9);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_expr_instantiate1(x_22, x_36);
lean_dec(x_36);
lean_dec(x_22);
x_2 = x_38;
x_9 = x_37;
goto _start;
}
else
{
lean_object* x_40; 
x_40 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(x_1, x_20);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec(x_7);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_9);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_42);
x_43 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_46 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_44, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
uint8_t x_49; 
lean_dec(x_42);
lean_dec(x_7);
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_46, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_46, 0, x_51);
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_56 = lean_expr_instantiate1(x_22, x_42);
lean_dec(x_42);
lean_dec(x_22);
x_2 = x_56;
x_9 = x_55;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_42);
lean_dec(x_7);
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_58 = !lean_is_exclusive(x_46);
if (x_58 == 0)
{
return x_46;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_46, 0);
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_46);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_42);
lean_dec(x_7);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_62 = !lean_is_exclusive(x_43);
if (x_62 == 0)
{
return x_43;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_43, 0);
x_64 = lean_ctor_get(x_43, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_43);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_7, 0);
x_67 = lean_ctor_get(x_7, 1);
x_68 = lean_ctor_get(x_7, 2);
x_69 = lean_ctor_get(x_7, 3);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_7);
x_70 = l_Lean_replaceRef(x_24, x_69);
lean_dec(x_24);
x_71 = l_Lean_replaceRef(x_70, x_69);
lean_dec(x_70);
x_72 = l_Lean_replaceRef(x_71, x_69);
lean_dec(x_69);
lean_dec(x_71);
x_73 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_67);
lean_ctor_set(x_73, 2, x_68);
lean_ctor_set(x_73, 3, x_72);
if (x_26 == 0)
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_20);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_21);
x_75 = 0;
x_76 = lean_box(0);
lean_inc(x_5);
x_77 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_74, x_75, x_76, x_5, x_6, x_73, x_8, x_9);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_expr_instantiate1(x_22, x_78);
lean_dec(x_78);
lean_dec(x_22);
x_2 = x_80;
x_7 = x_73;
x_9 = x_79;
goto _start;
}
else
{
lean_object* x_82; 
x_82 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(x_1, x_20);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
lean_dec(x_73);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_9);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_8);
lean_inc(x_73);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_84);
x_85 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_84, x_3, x_4, x_5, x_6, x_73, x_8, x_9);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_8);
lean_inc(x_73);
lean_inc(x_6);
lean_inc(x_5);
x_88 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_86, x_21, x_3, x_4, x_5, x_6, x_73, x_8, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_84);
lean_dec(x_73);
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_92 = x_88;
} else {
 lean_dec_ref(x_88);
 x_92 = lean_box(0);
}
x_93 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_88, 1);
lean_inc(x_95);
lean_dec(x_88);
x_96 = lean_expr_instantiate1(x_22, x_84);
lean_dec(x_84);
lean_dec(x_22);
x_2 = x_96;
x_7 = x_73;
x_9 = x_95;
goto _start;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_84);
lean_dec(x_73);
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_98 = lean_ctor_get(x_88, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_88, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_100 = x_88;
} else {
 lean_dec_ref(x_88);
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
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_84);
lean_dec(x_73);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_102 = lean_ctor_get(x_85, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_85, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_104 = x_85;
} else {
 lean_dec_ref(x_85);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_106 = lean_box(0);
x_10 = x_106;
goto block_19;
}
block_19:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_10);
x_11 = l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__2;
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Expr_isAppOfArity___main(x_2, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_11 = l_Lean_ConstantInfo_lparams(x_2);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_7, 3);
x_14 = l_Lean_replaceRef(x_10, x_13);
lean_dec(x_10);
x_15 = l_Lean_replaceRef(x_14, x_13);
lean_dec(x_14);
x_16 = l_Lean_replaceRef(x_15, x_13);
lean_dec(x_13);
lean_dec(x_15);
lean_ctor_set(x_7, 3, x_16);
x_17 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_instantiate_value_lparams(x_2, x_18);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
x_24 = lean_ctor_get(x_7, 2);
x_25 = lean_ctor_get(x_7, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_26 = l_Lean_replaceRef(x_10, x_25);
lean_dec(x_10);
x_27 = l_Lean_replaceRef(x_26, x_25);
lean_dec(x_26);
x_28 = l_Lean_replaceRef(x_27, x_25);
lean_dec(x_25);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_28);
x_30 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_11, x_3, x_4, x_5, x_6, x_29, x_8, x_9);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_instantiate_value_lparams(x_2, x_31);
lean_dec(x_31);
x_34 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(x_1, x_33, x_3, x_4, x_5, x_6, x_29, x_8, x_32);
return x_34;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isApp(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_6, x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Environment_getProjectionStructureName_x3f(x_17, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_contains___at_Lean_findField_x3f___main___spec__1(x_1, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; 
lean_free_object(x_13);
x_23 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_2, x_3, x_4, x_5, x_6, x_16);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Environment_getProjectionStructureName_x3f(x_26, x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Array_contains___at_Lean_findField_x3f___main___spec__1(x_1, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_2, x_3, x_4, x_5, x_6, x_25);
return x_34;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_7);
return x_36;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_3;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_fget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_fset(x_3, x_2, x_14);
x_16 = x_13;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_17 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_16, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = x_18;
x_23 = lean_array_fset(x_15, x_2, x_22);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_23;
x_8 = x_19;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_2, x_10, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__1(x_2, x_10, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1(x_8, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_9, 1);
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_Expr_isMVar(x_18);
if (x_19 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_free_object(x_9);
x_2 = x_18;
x_7 = x_16;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = l_Lean_Expr_isMVar(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
else
{
x_2 = x_22;
x_7 = x_21;
goto _start;
}
}
}
}
case 5:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_27 = l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_getAppFn___main(x_26);
lean_dec(x_26);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_31 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_30, x_3, x_4, x_5, x_6, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Expr_isLambda(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_35);
x_37 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_36);
x_38 = lean_mk_array(x_36, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_36, x_39);
lean_dec(x_36);
x_41 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_38, x_40);
x_42 = x_41;
x_43 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___spec__1), 8, 3);
lean_closure_set(x_43, 0, x_1);
lean_closure_set(x_43, 1, x_35);
lean_closure_set(x_43, 2, x_42);
x_44 = x_43;
x_45 = lean_apply_5(x_44, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_47, x_47, x_35, x_32);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_45);
x_51 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_49, x_49, x_35, x_32);
lean_dec(x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_32);
x_53 = !lean_is_exclusive(x_45);
if (x_53 == 0)
{
return x_45;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_45, 0);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_45);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_57);
x_59 = lean_mk_empty_array_with_capacity(x_58);
lean_dec(x_58);
x_60 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_59);
x_61 = l_Lean_Expr_betaRev(x_32, x_60);
lean_dec(x_60);
lean_dec(x_32);
x_2 = x_61;
x_7 = x_33;
goto _start;
}
}
else
{
uint8_t x_63; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_31);
if (x_63 == 0)
{
return x_31;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_31, 0);
x_65 = lean_ctor_get(x_31, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_31);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_26);
lean_dec(x_2);
x_67 = lean_ctor_get(x_27, 1);
lean_inc(x_67);
lean_dec(x_27);
x_68 = lean_ctor_get(x_28, 0);
lean_inc(x_68);
lean_dec(x_28);
x_2 = x_68;
x_7 = x_67;
goto _start;
}
}
else
{
uint8_t x_70; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_27);
if (x_70 == 0)
{
return x_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_27, 0);
x_72 = lean_ctor_get(x_27, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_27);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
case 6:
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__1), 8, 1);
lean_closure_set(x_74, 0, x_1);
x_75 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__2___rarg(x_2, x_74, x_3, x_4, x_5, x_6, x_7);
return x_75;
}
case 7:
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__2), 8, 1);
lean_closure_set(x_76, 0, x_1);
x_77 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_2, x_76, x_3, x_4, x_5, x_6, x_7);
return x_77;
}
case 8:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__1), 8, 1);
lean_closure_set(x_78, 0, x_1);
x_79 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__2___rarg(x_2, x_78, x_3, x_4, x_5, x_6, x_7);
return x_79;
}
case 10:
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
x_81 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_80, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_2);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_expr_update_mdata(x_2, x_83);
lean_ctor_set(x_81, 0, x_85);
return x_81;
}
else
{
uint8_t x_86; 
lean_dec(x_84);
x_86 = l_Lean_Expr_isMVar(x_83);
if (x_86 == 0)
{
lean_dec(x_2);
return x_81;
}
else
{
lean_object* x_87; 
x_87 = lean_expr_update_mdata(x_2, x_83);
lean_ctor_set(x_81, 0, x_87);
return x_81;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_81, 0);
x_89 = lean_ctor_get(x_81, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_81);
x_90 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_2);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_expr_update_mdata(x_2, x_88);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
else
{
uint8_t x_93; 
lean_dec(x_90);
x_93 = l_Lean_Expr_isMVar(x_88);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec(x_2);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_89);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_expr_update_mdata(x_2, x_88);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_89);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_81);
if (x_97 == 0)
{
return x_81;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_81, 0);
x_99 = lean_ctor_get(x_81, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_81);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
case 11:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_2, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_2, 2);
lean_inc(x_102);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_102);
x_103 = l_Lean_Meta_reduceProj_x3f(x_102, x_101, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_102, x_3, x_4, x_5, x_6, x_105);
if (lean_obj_tag(x_106) == 0)
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = lean_expr_update_proj(x_2, x_108);
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
x_112 = lean_expr_update_proj(x_2, x_110);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_2);
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
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_102);
lean_dec(x_2);
x_118 = lean_ctor_get(x_103, 1);
lean_inc(x_118);
lean_dec(x_103);
x_119 = lean_ctor_get(x_104, 0);
lean_inc(x_119);
lean_dec(x_104);
x_2 = x_119;
x_7 = x_118;
goto _start;
}
}
else
{
uint8_t x_121; 
lean_dec(x_102);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_103);
if (x_121 == 0)
{
return x_103;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_103, 0);
x_123 = lean_ctor_get(x_103, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_103);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
default: 
{
lean_object* x_125; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_2);
lean_ctor_set(x_125, 1, x_7);
return x_125;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(size_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; size_t x_99; size_t x_100; lean_object* x_101; size_t x_102; uint8_t x_103; 
x_99 = lean_ptr_addr(x_2);
x_100 = x_1 == 0 ? 0 : x_99 % x_1;
x_101 = lean_array_uget(x_3, x_100);
x_102 = lean_ptr_addr(x_101);
lean_dec(x_101);
x_103 = x_102 == x_99;
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
lean_inc(x_2);
x_104 = lean_array_uset(x_3, x_100, x_2);
x_105 = 0;
x_4 = x_105;
x_5 = x_104;
goto block_98;
}
else
{
uint8_t x_106; 
x_106 = 1;
x_4 = x_106;
x_5 = x_3;
goto block_98;
}
block_98:
{
if (x_4 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_2);
if (lean_obj_tag(x_6) == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_1, x_7, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_2 = x_8;
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_8);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_20 = x_10;
} else {
 lean_dec_ref(x_10);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(1, 1, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
case 6:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_dec(x_2);
x_25 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_1, x_23, x_5);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_2 = x_24;
x_3 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_24);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_25, 0, x_33);
return x_25;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_36 = x_26;
} else {
 lean_dec_ref(x_26);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
}
case 7:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 2);
lean_inc(x_40);
lean_dec(x_2);
x_41 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_1, x_39, x_5);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_2 = x_40;
x_3 = x_43;
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_40);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_42);
if (x_47 == 0)
{
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_41, 0, x_49);
return x_41;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_52 = x_42;
} else {
 lean_dec_ref(x_42);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
}
}
case 8:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 3);
lean_inc(x_57);
lean_dec(x_2);
x_58 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_1, x_55, x_5);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_1, x_56, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_2 = x_57;
x_3 = x_63;
goto _start;
}
else
{
uint8_t x_65; 
lean_dec(x_57);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_61, 0);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_62);
if (x_67 == 0)
{
return x_61;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
lean_dec(x_62);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_61, 0, x_69);
return x_61;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
lean_dec(x_61);
x_71 = lean_ctor_get(x_62, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_72 = x_62;
} else {
 lean_dec_ref(x_62);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_71);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_57);
lean_dec(x_56);
x_75 = !lean_is_exclusive(x_58);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_58, 0);
lean_dec(x_76);
x_77 = !lean_is_exclusive(x_59);
if (x_77 == 0)
{
return x_58;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_59, 0);
lean_inc(x_78);
lean_dec(x_59);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_58, 0, x_79);
return x_58;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_58, 1);
lean_inc(x_80);
lean_dec(x_58);
x_81 = lean_ctor_get(x_59, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_82 = x_59;
} else {
 lean_dec_ref(x_59);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_81);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
return x_84;
}
}
}
case 10:
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
lean_dec(x_2);
x_2 = x_85;
x_3 = x_5;
goto _start;
}
case 11:
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_2, 2);
lean_inc(x_87);
lean_dec(x_2);
x_2 = x_87;
x_3 = x_5;
goto _start;
}
default: 
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_2);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_5);
return x_90;
}
}
}
else
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_6);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_6, 0);
lean_dec(x_92);
lean_ctor_set(x_6, 0, x_2);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_6);
lean_ctor_set(x_93, 1, x_5);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_6);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_2);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_5);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_2);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_5);
return x_97;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_default");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_3, x_7);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_1);
x_17 = lean_nat_dec_lt(x_6, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_array_fget(x_1, x_6);
x_22 = l_Lean_Elab_Term_StructInst_Struct_structName(x_21);
lean_inc(x_4);
x_23 = l_Lean_Name_append___main(x_22, x_4);
lean_dec(x_22);
x_24 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__2;
x_25 = l_Lean_Name_append___main(x_23, x_24);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_13, x_14);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_environment_find(x_29, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_21);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_6, x_31);
lean_dec(x_6);
x_6 = x_32;
x_14 = x_28;
goto _start;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_st_ref_get(x_11, x_28);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_39 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(x_21, x_34, x_8, x_9, x_10, x_11, x_12, x_13, x_37);
lean_dec(x_34);
lean_dec(x_21);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_setMCtx___at_Lean_Elab_Term_savingMCtx___spec__1(x_38, x_8, x_9, x_10, x_11, x_12, x_13, x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_6, x_44);
lean_dec(x_6);
x_46 = lean_nat_add(x_7, x_44);
lean_dec(x_7);
x_6 = x_45;
x_7 = x_46;
x_14 = x_43;
goto _start;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
x_49 = !lean_is_exclusive(x_40);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_51 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_2, x_50, x_10, x_11, x_12, x_13, x_48);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = 8192;
x_55 = l_Lean_Expr_FindImpl_initCache;
lean_inc(x_52);
x_56 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_54, x_52, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_58 = l_Lean_Elab_Term_getMVarDecl(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_53);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 2);
lean_inc(x_61);
lean_dec(x_59);
lean_ctor_set(x_40, 0, x_61);
x_62 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
x_63 = l_Lean_Elab_Term_ensureHasType(x_40, x_52, x_62, x_8, x_9, x_10, x_11, x_12, x_13, x_60);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(x_5, x_64, x_8, x_9, x_10, x_11, x_12, x_13, x_65);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
x_69 = 1;
x_70 = lean_box(x_69);
lean_ctor_set(x_66, 0, x_70);
return x_66;
}
else
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
x_72 = 1;
x_73 = lean_box(x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
x_75 = !lean_is_exclusive(x_63);
if (x_75 == 0)
{
return x_63;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_63, 0);
x_77 = lean_ctor_get(x_63, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_63);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_57);
lean_dec(x_52);
lean_free_object(x_40);
x_79 = l_Lean_Meta_setMCtx___at_Lean_Elab_Term_savingMCtx___spec__1(x_38, x_8, x_9, x_10, x_11, x_12, x_13, x_53);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_add(x_6, x_81);
lean_dec(x_6);
x_83 = lean_nat_add(x_7, x_81);
lean_dec(x_7);
x_6 = x_82;
x_7 = x_83;
x_14 = x_80;
goto _start;
}
}
else
{
uint8_t x_85; 
lean_free_object(x_40);
lean_dec(x_38);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_51);
if (x_85 == 0)
{
return x_51;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_51, 0);
x_87 = lean_ctor_get(x_51, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_51);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_40, 0);
lean_inc(x_89);
lean_dec(x_40);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_90 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_2, x_89, x_10, x_11, x_12, x_13, x_48);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; size_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = 8192;
x_94 = l_Lean_Expr_FindImpl_initCache;
lean_inc(x_91);
x_95 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_93, x_91, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec(x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_97 = l_Lean_Elab_Term_getMVarDecl(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_92);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 2);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
x_103 = l_Lean_Elab_Term_ensureHasType(x_101, x_91, x_102, x_8, x_9, x_10, x_11, x_12, x_13, x_99);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(x_5, x_104, x_8, x_9, x_10, x_11, x_12, x_13, x_105);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = 1;
x_110 = lean_box(x_109);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_108;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_107);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
x_112 = lean_ctor_get(x_103, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_103, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_114 = x_103;
} else {
 lean_dec_ref(x_103);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_96);
lean_dec(x_91);
x_116 = l_Lean_Meta_setMCtx___at_Lean_Elab_Term_savingMCtx___spec__1(x_38, x_8, x_9, x_10, x_11, x_12, x_13, x_92);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_6, x_118);
lean_dec(x_6);
x_120 = lean_nat_add(x_7, x_118);
lean_dec(x_7);
x_6 = x_119;
x_7 = x_120;
x_14 = x_117;
goto _start;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_38);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_122 = lean_ctor_get(x_90, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_90, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_124 = x_90;
} else {
 lean_dec_ref(x_90);
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
}
}
else
{
uint8_t x_126; 
lean_dec(x_38);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_126 = !lean_is_exclusive(x_39);
if (x_126 == 0)
{
return x_39;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_39, 0);
x_128 = lean_ctor_get(x_39, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_39);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_34);
lean_dec(x_21);
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_nat_add(x_6, x_130);
lean_dec(x_6);
x_6 = x_131;
x_14 = x_28;
goto _start;
}
}
}
}
else
{
uint8_t x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_133 = 0;
x_134 = lean_box(x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_14);
return x_135;
}
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_1, x_2, x_3, x_4, x_5, x_13, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_100; 
x_100 = lean_ctor_get(x_1, 2);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 1)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l_Lean_Elab_Term_StructInst_DefaultFields_step___main(x_101, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_102;
}
else
{
lean_object* x_103; 
lean_dec(x_100);
x_103 = lean_box(0);
x_12 = x_103;
goto block_99;
}
block_99:
{
lean_object* x_13; 
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_14 = l_PUnit_Inhabited;
x_15 = l_monadInhabited___rarg(x_2, x_14);
x_16 = lean_alloc_closure((void*)(l_ReaderT_inhabited___rarg___boxed), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_unreachable_x21___rarg(x_16);
x_18 = lean_apply_9(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_19);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_23) == 2)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_24);
x_25 = l_Lean_Elab_Term_isExprMVarAssigned(x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 2);
lean_inc(x_32);
lean_dec(x_3);
x_33 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_1);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_9);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_9, 3);
x_36 = l_Lean_replaceRef(x_29, x_35);
lean_dec(x_29);
x_37 = l_Lean_replaceRef(x_36, x_35);
lean_dec(x_36);
x_38 = l_Lean_replaceRef(x_37, x_35);
lean_dec(x_35);
lean_dec(x_37);
lean_ctor_set(x_9, 3, x_38);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_30, x_31, x_32, x_33, x_24, x_39, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
lean_dec(x_6);
lean_dec(x_32);
lean_dec(x_30);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
if (x_42 == 0)
{
uint8_t x_43; 
lean_dec(x_41);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_40, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_40, 0, x_45);
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_st_ref_take(x_4, x_49);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_st_ref_set(x_4, x_41, x_51);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_40);
if (x_59 == 0)
{
return x_40;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_40, 0);
x_61 = lean_ctor_get(x_40, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_40);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_9, 0);
x_64 = lean_ctor_get(x_9, 1);
x_65 = lean_ctor_get(x_9, 2);
x_66 = lean_ctor_get(x_9, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_9);
x_67 = l_Lean_replaceRef(x_29, x_66);
lean_dec(x_29);
x_68 = l_Lean_replaceRef(x_67, x_66);
lean_dec(x_67);
x_69 = l_Lean_replaceRef(x_68, x_66);
lean_dec(x_66);
lean_dec(x_68);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_64);
lean_ctor_set(x_70, 2, x_65);
lean_ctor_set(x_70, 3, x_69);
x_71 = lean_unsigned_to_nat(0u);
x_72 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_30, x_31, x_32, x_33, x_24, x_71, x_71, x_5, x_6, x_7, x_8, x_70, x_10, x_28);
lean_dec(x_6);
lean_dec(x_32);
lean_dec(x_30);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_73);
lean_dec(x_4);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_80 = lean_st_ref_take(x_4, x_79);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_st_ref_set(x_4, x_73, x_81);
lean_dec(x_4);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
x_85 = lean_box(0);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_4);
x_87 = lean_ctor_get(x_72, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_72, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_89 = x_72;
} else {
 lean_dec_ref(x_72);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_25);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_25, 0);
lean_dec(x_92);
x_93 = lean_box(0);
lean_ctor_set(x_25, 0, x_93);
return x_25;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_25, 1);
lean_inc(x_94);
lean_dec(x_25);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_11);
return x_98;
}
}
}
}
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_10(x_13, lean_box(0), x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_3);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__1), 11, 3);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_3);
x_20 = lean_alloc_closure((void*)(l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2___boxed), 12, 3);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_3);
x_21 = lean_apply_12(x_18, lean_box(0), lean_box(0), x_19, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_21;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_array_push(x_17, x_1);
lean_ctor_set(x_2, 0, x_18);
x_19 = l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
x_20 = l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1(x_19, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_24 = lean_array_push(x_21, x_1);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
x_26 = l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
x_27 = l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1(x_26, x_15, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_11, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_11, 0, x_30);
return x_11;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_dec(x_11);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_StructInst_DefaultFields_step___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__2___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_9, 3);
x_14 = l_Lean_replaceRef(x_1, x_13);
x_15 = l_Lean_replaceRef(x_14, x_13);
lean_dec(x_14);
x_16 = l_Lean_replaceRef(x_15, x_13);
lean_dec(x_13);
lean_dec(x_15);
lean_ctor_set(x_9, 3, x_16);
x_17 = l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__2___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
x_20 = lean_ctor_get(x_9, 2);
x_21 = lean_ctor_get(x_9, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_22 = l_Lean_replaceRef(x_1, x_21);
x_23 = l_Lean_replaceRef(x_22, x_21);
lean_dec(x_22);
x_24 = l_Lean_replaceRef(x_23, x_21);
lean_dec(x_21);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_24);
x_26 = l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__2___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25, x_10, x_11);
lean_dec(x_25);
return x_26;
}
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1___rarg___boxed), 11, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is missing");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_get(x_9, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(x_17, x_3);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
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
x_19 = lean_box(0);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_free_object(x_13);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_nat_dec_lt(x_1, x_2);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_20);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_4, 2);
lean_dec(x_23);
lean_inc(x_2);
lean_ctor_set(x_4, 2, x_2);
x_24 = lean_st_ref_take(x_5, x_16);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_st_ref_set(x_5, x_27, x_25);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Lean_Elab_Term_StructInst_DefaultFields_step___main(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_st_ref_get(x_5, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_2, x_36);
lean_dec(x_2);
x_2 = x_37;
x_12 = x_35;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_unsigned_to_nat(0u);
x_2 = x_40;
x_12 = x_39;
goto _start;
}
}
else
{
uint8_t x_42; 
lean_dec(x_4);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
return x_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_30, 0);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_30);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_4, 0);
x_47 = lean_ctor_get(x_4, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_4);
lean_inc(x_2);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_2);
x_49 = lean_st_ref_take(x_5, x_16);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = 0;
x_52 = lean_box(x_51);
x_53 = lean_st_ref_set(x_5, x_52, x_50);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_48);
lean_inc(x_3);
x_55 = l_Lean_Elab_Term_StructInst_DefaultFields_step___main(x_3, x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_st_ref_get(x_5, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_2, x_61);
lean_dec(x_2);
x_2 = x_62;
x_4 = x_48;
x_12 = x_60;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_2);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
x_65 = lean_unsigned_to_nat(0u);
x_2 = x_65;
x_4 = x_48;
x_12 = x_64;
goto _start;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_48);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_67 = lean_ctor_get(x_55, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_55, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_69 = x_55;
} else {
 lean_dec_ref(x_55);
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
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_ctor_get(x_20, 0);
lean_inc(x_71);
x_72 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_20);
lean_dec(x_20);
x_73 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1___rarg(x_71, x_77, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_71);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_13, 0);
x_80 = lean_ctor_get(x_13, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_13);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(x_81, x_3);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
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
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
return x_84;
}
else
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_nat_dec_lt(x_1, x_2);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_85);
x_87 = lean_ctor_get(x_4, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_4, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 x_89 = x_4;
} else {
 lean_dec_ref(x_4);
 x_89 = lean_box(0);
}
lean_inc(x_2);
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 3, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
lean_ctor_set(x_90, 2, x_2);
x_91 = lean_st_ref_take(x_5, x_80);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_st_ref_set(x_5, x_94, x_92);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_90);
lean_inc(x_3);
x_97 = l_Lean_Elab_Term_StructInst_DefaultFields_step___main(x_3, x_90, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_st_ref_get(x_5, x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_add(x_2, x_103);
lean_dec(x_2);
x_2 = x_104;
x_4 = x_90;
x_12 = x_102;
goto _start;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_2);
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
lean_dec(x_99);
x_107 = lean_unsigned_to_nat(0u);
x_2 = x_107;
x_4 = x_90;
x_12 = x_106;
goto _start;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_90);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_109 = lean_ctor_get(x_97, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_97, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_111 = x_97;
} else {
 lean_dec_ref(x_97);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_3);
lean_dec(x_2);
x_113 = lean_ctor_get(x_85, 0);
lean_inc(x_113);
x_114 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_85);
lean_dec(x_85);
x_115 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_117 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3;
x_119 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1___rarg(x_113, x_119, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_80);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_113);
return x_120;
}
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main(x_1);
x_10 = l_Array_empty___closed__1;
x_11 = l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main(x_1, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_st_mk_ref(x_15, x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_17);
x_19 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main(x_9, x_12, x_1, x_13, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_17, x_21);
lean_dec(x_17);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a structure");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l___private_Lean_Elab_StructInst_5__getStructName___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_75 = lean_st_ref_get(x_9, x_13);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_12);
x_79 = l_Lean_isStructureLike(x_78, x_12);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_80, 0, x_12);
x_81 = l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__3;
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__6;
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_84, x_4, x_5, x_6, x_7, x_8, x_9, x_77);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
return x_85;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_85);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
else
{
x_14 = x_77;
goto block_74;
}
block_74:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_StructInst_7__mkStructView(x_1, x_12, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
x_25 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2;
x_26 = l_Lean_checkTraceOption(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_22, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Elab_Term_StructInst_DefaultFields_propagate(x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_30);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_27);
if (x_41 == 0)
{
return x_27;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_27, 0);
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_27);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_inc(x_22);
x_45 = l_Lean_Elab_Term_StructInst_formatStruct___main(x_22);
x_46 = lean_box(0);
x_47 = l_Lean_Format_pretty(x_45, x_46);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_25, x_49, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_52 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_22, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_51);
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
x_57 = l_Lean_Elab_Term_StructInst_DefaultFields_propagate(x_56, x_4, x_5, x_6, x_7, x_8, x_9, x_54);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_55);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_57);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_66 = !lean_is_exclusive(x_52);
if (x_66 == 0)
{
return x_52;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_52, 0);
x_68 = lean_ctor_get(x_52, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_52);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_21);
if (x_70 == 0)
{
return x_21;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_21, 0);
x_72 = lean_ctor_get(x_21, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_21);
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
uint8_t x_90; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_11);
if (x_90 == 0)
{
return x_11;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_11, 0);
x_92 = lean_ctor_get(x_11, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_11);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, explicit source is required when using '[<index>] := <value>'");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l___private_Lean_Elab_StructInst_2__getStructSource(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_3);
x_16 = l___private_Lean_Elab_StructInst_3__isModifyOp_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_StructInst_25__elabStructInstAux(x_1, x_2, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_19;
}
else
{
if (lean_obj_tag(x_14) == 2)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l___private_Lean_Elab_StructInst_4__elabModifyOp(x_1, x_21, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = l_Lean_Elab_Term_StructInst_elabStructInst___closed__3;
x_26 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_ctor_get(x_11, 0);
lean_inc(x_36);
lean_dec(x_11);
x_37 = !lean_is_exclusive(x_3);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_3, 6);
lean_inc(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_3, 6, x_40);
x_41 = 1;
x_42 = l_Lean_Elab_Term_elabTerm(x_36, x_2, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_43 = lean_ctor_get(x_3, 0);
x_44 = lean_ctor_get(x_3, 1);
x_45 = lean_ctor_get(x_3, 2);
x_46 = lean_ctor_get(x_3, 3);
x_47 = lean_ctor_get(x_3, 4);
x_48 = lean_ctor_get(x_3, 5);
x_49 = lean_ctor_get(x_3, 6);
x_50 = lean_ctor_get(x_3, 7);
x_51 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_52 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_3);
lean_inc(x_36);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_36);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
x_55 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_44);
lean_ctor_set(x_55, 2, x_45);
lean_ctor_set(x_55, 3, x_46);
lean_ctor_set(x_55, 4, x_47);
lean_ctor_set(x_55, 5, x_48);
lean_ctor_set(x_55, 6, x_54);
lean_ctor_set(x_55, 7, x_50);
lean_ctor_set_uint8(x_55, sizeof(void*)*8, x_51);
lean_ctor_set_uint8(x_55, sizeof(void*)*8 + 1, x_52);
x_56 = 1;
x_57 = l_Lean_Elab_Term_elabTerm(x_36, x_2, x_56, x_55, x_4, x_5, x_6, x_7, x_8, x_35);
return x_57;
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_elabStructInst), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_StructInst_26__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_FindExpr(lean_object*);
lean_object* initialize_Lean_Elab_App(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
lean_object* initialize_Lean_Elab_Quotation(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_StructInst(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_App(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Quotation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1);
res = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1 = _init_l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1);
l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__2 = _init_l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__2);
l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3 = _init_l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3);
l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4 = _init_l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4);
l_Lean_Elab_Term_StructInst_Source_inhabited = _init_l_Lean_Elab_Term_StructInst_Source_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Source_inhabited);
l___private_Lean_Elab_StructInst_2__getStructSource___closed__1 = _init_l___private_Lean_Elab_StructInst_2__getStructSource___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_2__getStructSource___closed__1);
l___private_Lean_Elab_StructInst_2__getStructSource___closed__2 = _init_l___private_Lean_Elab_StructInst_2__getStructSource___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_2__getStructSource___closed__2);
l___private_Lean_Elab_StructInst_2__getStructSource___closed__3 = _init_l___private_Lean_Elab_StructInst_2__getStructSource___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_2__getStructSource___closed__3);
l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1 = _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1);
l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2 = _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2);
l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3 = _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3);
l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4 = _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4);
l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5 = _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5);
l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6 = _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6);
l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__7 = _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__7();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__7);
l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__8 = _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__8();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__8);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__1 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__1);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__6 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__6();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__6);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__10 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__10();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__10);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__13 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__13();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__13);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__14 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__14();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__14);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__15 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__15();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__15);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__16 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__16();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__16);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__18 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__18();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__18);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__19 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__19();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__19);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__21 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__21();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__21);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__22 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__22();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__22);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__23 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__23();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__23);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__24 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__24();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__24);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__25 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__25();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__25);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__26 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__26();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__26);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__27 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__27();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__27);
l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__1 = _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__1);
l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__2 = _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__2);
l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3 = _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3);
l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__4 = _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__4);
l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__5 = _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__5);
l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6 = _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6);
l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__7 = _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__7();
lean_mark_persistent(l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__7);
l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__8 = _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__8();
lean_mark_persistent(l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__8);
l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9 = _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9();
lean_mark_persistent(l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__9);
l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1 = _init_l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1);
l_Lean_Elab_Term_StructInst_FieldLHS_inhabited = _init_l_Lean_Elab_Term_StructInst_FieldLHS_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_FieldLHS_inhabited);
l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1 = _init_l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1);
l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2 = _init_l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2);
l_Lean_Elab_Term_StructInst_Struct_inhabited___closed__1 = _init_l_Lean_Elab_Term_StructInst_Struct_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Struct_inhabited___closed__1);
l_Lean_Elab_Term_StructInst_Struct_inhabited = _init_l_Lean_Elab_Term_StructInst_Struct_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Struct_inhabited);
l_Lean_Elab_Term_StructInst_formatField___closed__1 = _init_l_Lean_Elab_Term_StructInst_formatField___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatField___closed__1);
l_Lean_Elab_Term_StructInst_formatField___closed__2 = _init_l_Lean_Elab_Term_StructInst_formatField___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatField___closed__2);
l_Lean_Elab_Term_StructInst_formatField___closed__3 = _init_l_Lean_Elab_Term_StructInst_formatField___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatField___closed__3);
l_Lean_Elab_Term_StructInst_formatField___closed__4 = _init_l_Lean_Elab_Term_StructInst_formatField___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatField___closed__4);
l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1 = _init_l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1();
lean_mark_persistent(l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1);
l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1 = _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1);
l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2 = _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2);
l_Lean_Elab_Term_StructInst_formatStruct___main___closed__3 = _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___main___closed__3);
l_Lean_Elab_Term_StructInst_formatStruct___main___closed__4 = _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___main___closed__4);
l_Lean_Elab_Term_StructInst_formatStruct___main___closed__5 = _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___main___closed__5);
l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1 = _init_l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1);
l_Lean_Elab_Term_StructInst_Struct_hasFormat = _init_l_Lean_Elab_Term_StructInst_Struct_hasFormat();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Struct_hasFormat);
l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1 = _init_l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1);
l_Lean_Elab_Term_StructInst_Struct_hasToString = _init_l_Lean_Elab_Term_StructInst_Struct_hasToString();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Struct_hasToString);
l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1 = _init_l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1);
l_Lean_Elab_Term_StructInst_Field_hasFormat = _init_l_Lean_Elab_Term_StructInst_Field_hasFormat();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_hasFormat);
l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1 = _init_l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1);
l_Lean_Elab_Term_StructInst_Field_hasToString = _init_l_Lean_Elab_Term_StructInst_Field_hasToString();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_hasToString);
l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__1 = _init_l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__1);
l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__2 = _init_l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__2);
l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2___closed__1 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2___closed__1();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2___closed__1);
l___private_Lean_Elab_StructInst_8__expandCompositeFields___closed__1 = _init_l___private_Lean_Elab_StructInst_8__expandCompositeFields___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_8__expandCompositeFields___closed__1);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6);
l___private_Lean_Elab_StructInst_12__mkFieldMap___closed__1 = _init_l___private_Lean_Elab_StructInst_12__mkFieldMap___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_12__mkFieldMap___closed__1);
l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__1 = _init_l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__1);
l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__2 = _init_l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__2);
l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__3 = _init_l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__3);
l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1 = _init_l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1);
l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2 = _init_l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2);
l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3 = _init_l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3);
l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__1 = _init_l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__1);
l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__2 = _init_l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__2);
l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3 = _init_l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3);
l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1 = _init_l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1);
l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2 = _init_l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2);
l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__1 = _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__1);
l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2 = _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2);
l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3 = _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3);
l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__4 = _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__4);
l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5 = _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5);
l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__6 = _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__6);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__1 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__1);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__2 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__2);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3);
l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__1 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__1);
l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__2 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__2);
l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__1 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__1);
l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__2 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__2);
l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3);
l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__1 = _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__1);
l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__2 = _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__2);
l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__3 = _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__3);
l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__4 = _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__4);
l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__5 = _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__5);
l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__6 = _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__6);
l_Lean_Elab_Term_StructInst_elabStructInst___closed__1 = _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_elabStructInst___closed__1);
l_Lean_Elab_Term_StructInst_elabStructInst___closed__2 = _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_elabStructInst___closed__2);
l_Lean_Elab_Term_StructInst_elabStructInst___closed__3 = _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_elabStructInst___closed__3);
l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1);
res = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_StructInst_26__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
