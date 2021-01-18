// Lean compiler output
// Module: Lean.Elab.Command
// Imports: Init Lean.Parser.Command Lean.ResolveName Lean.Meta.Reduce Lean.Elab.Log Lean.Elab.Term Lean.Elab.Binders Lean.Elab.SyntheticMVars Lean.Elab.DeclModifiers Lean.Elab.InfoTree
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
lean_object* l_Lean_Elab_Command_State_scopes___default___closed__1;
lean_object* l_Lean_Elab_Command_elabVariable(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__4;
lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Elab_Command_elabEnd_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_withLogging___closed__1;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls___boxed(lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_elabSection(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInitQuot_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instInhabitedState;
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_catchExceptions(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_check___closed__1;
lean_object* l_Lean_throwKernelException___at_Lean_Elab_Command_elabEvalUnsafe___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabUsingElabFnsAux___closed__2;
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2;
lean_object* l_ReaderT_read___at_Lean_Elab_Command_instMonadLogCommandElabM___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at_Lean_Elab_addMacroStack___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l_Lean_Elab_Command_instAddMessageContextCommandElabM___closed__1;
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Elab_Command_withNamespace(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_1128____closed__2;
lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_quote___closed__1;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__2;
lean_object* l_Lean_Elab_Command_elabReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption_match__3___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope_match__1(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_Lean_Expr_isSyntheticSorry(lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__2;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__4;
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1;
lean_object* l_Lean_Elab_Command_elabEval___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenSimple(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_liftAttrM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
lean_object* l_Lean_Elab_Command_failIfSucceeds_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__1;
lean_object* l_Lean_Elab_Command_liftIO(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___closed__4;
lean_object* l_Lean_Elab_Command_instMonadOptionsCommandElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___boxed(lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Elab_Command_elabEvalUnsafe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverse(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__3;
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__2(lean_object*);
lean_object* l_Lean_popScope___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Context_macroStack___default;
lean_object* l_Lean_Elab_Command_modifyScope_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_runLinters___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
lean_object* l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_Command_withLogging___closed__2;
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabUsingElabFns___closed__4;
lean_object* l_Lean_Elab_Command_hasNoErrorMessages___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverses(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpen___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM(lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
extern lean_object* l_Lean_Parser_Command_section___elambda__1___closed__2;
lean_object* l_Std_PersistentArray_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at_Lean_Elab_Command_elabEvalUnsafe___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1;
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__1;
extern lean_object* l_Std_PersistentArray_empty___closed__1;
lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_traceAtCmdPos___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__1;
lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__2;
extern lean_object* l_instReprBool___closed__1;
lean_object* l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__1;
lean_object* l_Lean_Elab_Command_instMonadRefCommandElabM;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInitQuot___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureNoUnassignedMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Context_cmdPos___default;
lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSection(lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_Command_elabCommand___spec__3(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Scope_currNamespace___default;
lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__4;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3997____closed__3;
lean_object* l_Lean_Elab_Command_liftEIO(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDocString_x27___at_Lean_Elab_Command_expandDeclId___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadEnvCoreM___closed__1;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabReduce___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabReduce___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabExport___closed__1;
lean_object* l_Lean_Elab_Command_elabCheck(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1345____closed__1;
extern lean_object* l_Lean_Parser_Command_in___elambda__1___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1;
lean_object* l_Lean_Elab_Command_elabUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_getEvenElems___rarg___closed__1;
extern lean_object* l_Lean_Elab_logException___rarg___lambda__1___closed__2;
lean_object* l_Lean_Elab_Command_instMonadOptionsCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_init__quot___elambda__1___closed__2;
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadOptionsCommandElabM;
lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd(lean_object*);
extern lean_object* l_Lean_getMaxRecDepth___closed__1;
lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_add_alias(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__3;
lean_object* l_Lean_Elab_Command_setOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_export___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_ioErrorToMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Scope_opts___default;
lean_object* l_Lean_Elab_Command_failIfSucceeds(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__1;
lean_object* l_Lean_Elab_Command_withLogging_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenHiding___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Elab_Command_elabCommand_match__2(lean_object*);
lean_object* l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadRefCommandElabM___closed__2;
lean_object* l_Lean_Elab_Command_getScopes___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___closed__3;
extern lean_object* l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__3;
lean_object* l_Lean_Elab_Command_State_messages___default;
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_99_(uint8_t, uint8_t);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_instInhabitedPersistentArray___closed__1;
extern lean_object* l_Lean_Parser_Command_section___elambda__1___closed__1;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__2___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_instMonadRefCommandElabM___closed__1;
lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2;
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM;
lean_object* l_Lean_Elab_Command_elabOpen(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__2;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth___closed__2;
lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabUniverses___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__4;
extern lean_object* l_Lean_Meta_instInhabitedCache___closed__1;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabReduce___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_mkEmpty___closed__1;
lean_object* l_Lean_Elab_Command_elabCheckFailure(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedException___closed__1;
lean_object* l_Lean_Elab_Command_elabCheck___closed__3;
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__10___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption___closed__1;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverses(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_popScope___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__4;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption___closed__2;
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM;
lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope(lean_object*);
lean_object* l_IO_mkRef___at_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_155____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addOpenDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabEnd___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariables(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_Command_elabCommand___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__3___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instInhabitedCommandElabM(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabExport___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__1;
lean_object* l_Lean_addDocString_x27___at_Lean_Elab_Command_expandDeclId___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck___closed__1;
lean_object* l_Lean_Elab_Command_liftEIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runLinters(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_activateScoped___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__4___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_mkDeclName___rarg___closed__2;
extern lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecl(lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___closed__3;
lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__2;
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instInhabitedState___closed__1;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenSimple___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadOptionsCommandElabM___closed__2;
extern lean_object* l_Lean_choiceKind___closed__2;
lean_object* l_Lean_Elab_Command_elabCheck___closed__2;
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__9;
extern lean_object* l_Lean_Parser_Command_set__option___elambda__1___closed__2;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope(lean_object*);
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadQuotationCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1;
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermState(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadOptionsCommandElabM___closed__1;
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Scope_varDecls___default;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runLinters_match__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_Scope_openDecls___default;
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSection___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_State_nextInstIdx___default;
extern lean_object* l_Lean_Parser_Command_eval___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_instMonadRefCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermState___boxed(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__6;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runLinters_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEval___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_reduce___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_expandDeclId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenRenaming(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instReprBool___closed__3;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverses___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_instInhabitedMetavarContext___closed__1;
lean_object* l_Lean_Elab_Command_liftCoreM_match__1(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1;
lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__3;
lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__3;
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenHiding___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_pushScope___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__2;
lean_object* l_Lean_Elab_getMacros(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__5;
extern lean_object* l_IO_instInhabitedError___closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_setElabConfig(lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption_match__2(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1;
lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1;
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_155_(lean_object*);
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1050_(lean_object*);
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1345_(lean_object*);
lean_object* l_Lean_Elab_Command_elabSetOption_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Command_State_ngen___default;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenSimple___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Data_Options___hyg_528____closed__3;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__5;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__3;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at_Lean_Elab_Command_elabEvalUnsafe___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1;
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM_match__2(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elbChoice(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_activateScoped___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabExport(lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__2;
lean_object* l_Lean_Elab_Command_getScopes(lean_object*);
extern lean_object* l_Lean_protectedExt;
lean_object* l_Lean_Elab_Command_elbChoice(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Context_currRecDepth___default;
lean_object* l_Lean_Elab_Command_elabExport(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_liftAttrM(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenOnly(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getNumParts(lean_object*);
lean_object* l_Lean_Elab_Command_hasNoErrorMessages(lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_liftAttrM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_variable___elambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1;
lean_object* l_Lean_Elab_Command_liftCoreM_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__1;
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_docStringExt;
lean_object* l_Lean_Elab_Command_State_scopes___default;
lean_object* l_Lean_Elab_Command_instMonadLiftTIOCommandElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_addUnivLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__2;
lean_object* l_Lean_Elab_Command_withLogging(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_logUnknownDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1;
lean_object* l_Lean_Elab_Command_elabSynth___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedKeyedDeclsAttribute___closed__1;
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_instMonadQuotationCommandElabM;
lean_object* l_Lean_Elab_Command_elabSetOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
extern lean_object* l_Lean_firstFrontendMacroScope;
extern lean_object* l_Lean_Parser_Command_open___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_runLinters_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandDeclId___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Unhygienic_run___rarg___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__2;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__2;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___closed__2;
lean_object* l_Lean_Elab_Command_liftIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds___closed__2;
lean_object* l_Lean_Elab_Command_elabSetOption___closed__1;
lean_object* l_Lean_Elab_Command_elabSetOption___closed__2;
lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM;
lean_object* l___regBuiltin_Lean_Elab_Command_elabSection___closed__1;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__2;
lean_object* l_Lean_Elab_Command_elabCommand_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__1;
lean_object* l_Lean_Elab_Command_modifyScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_evalExpr___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Scope_levelNames___default;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___closed__1;
lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__6;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabEval___closed__1;
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_Syntax_mkAntiquotNode___closed__9;
lean_object* l_Lean_Elab_Command_withMacroExpansion(lean_object*);
lean_object* l_Lean_Elab_Command_withLogging_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Elab_expandDeclIdCore(lean_object*);
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce___closed__1;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInitQuot___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabReduce___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenHiding(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_hasNoErrorMessages___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabChoiceAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd(lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabExport___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__3(lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Command_Context_ref___default;
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__3;
lean_object* l_Lean_Elab_Command_elabEnd_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addUnivLevel(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedNameGenerator___closed__1;
lean_object* l_Lean_Elab_Command_setOption___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__4;
extern lean_object* l_Lean_Parser_Command_universe___elambda__1___closed__2;
lean_object* l_Lean_popScope___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resetMessageLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_Command_elabCommand___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds___closed__1;
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCheck___closed__4;
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__4;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(lean_object*);
extern lean_object* l_Lean_Syntax_mkApp___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__4(lean_object*);
lean_object* l_Lean_Elab_Command_elabReduce_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___closed__2;
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
extern lean_object* l_Lean_Parser_Command_end___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadRefCommandElabM___closed__3;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Elab_Command_elabCommand_match__3(lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_resetTraceState___rarg___lambda__1___closed__1;
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariables___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_end___elambda__1___closed__1;
lean_object* l_Lean_Elab_Command_elabExport___closed__1;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce(lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1;
lean_object* l_Lean_Elab_Command_getScope(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExport___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__3;
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_getMaxRecDepth(lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandInCmd(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__8;
lean_object* l_Lean_Elab_Command_elabVariable___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_check__failure___elambda__1___closed__2;
lean_object* l_Lean_pushScope___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabReduce(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEval(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___closed__1;
lean_object* l_Lean_Environment_registerNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setOption_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_logAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_ioErrorToMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_instMonadInfoTreeCommandElabM___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__2;
lean_object* l_Lean_Elab_Command_instInhabitedScope;
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___closed__6;
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_resolveNamespace___rarg___lambda__1___closed__1;
lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__3;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__4;
lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elbChoice___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_State_infoState___default___closed__1;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadLiftTIOCommandElabM(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen(lean_object*);
lean_object* l_Lean_pushScope___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withNamespace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__10(lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_head_x21___rarg___closed__3;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13781____closed__10;
lean_object* l_Lean_Elab_Command_failIfSucceeds___closed__4;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes_match__1___rarg(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___closed__6;
extern lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__2;
lean_object* l_Lean_Elab_Command_logUnknownDecl___closed__1;
lean_object* l_Lean_Elab_Command_instInhabitedCommandElabM___closed__1;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__3;
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__3;
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__3;
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___closed__1;
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandDeclId___spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenHiding___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe(lean_object*);
lean_object* l_Lean_Elab_Command_expandInCmd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace(lean_object*);
extern lean_object* l_Lean_Parser_Command_universes___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabEnd___closed__3;
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM;
lean_object* l_List_foldl___at_Lean_Elab_Command_elabExport___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames(lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___lambda__2___closed__1;
lean_object* l_Lean_Elab_Command_Context_currMacroScope___default;
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__3;
lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_evalConst___at_Lean_Elab_Term_evalExpr___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1;
extern lean_object* l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__5;
lean_object* l_Lean_Elab_Command_getMainModule___boxed(lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__1;
uint8_t l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader(lean_object*, lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
lean_object* l_Lean_Elab_Command_setOption___closed__3;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabEnd___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth(lean_object*);
lean_object* l_Lean_Elab_Command_instInhabitedCommandElabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_DataValue_sameCtor(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos(lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_openSimple___elambda__1___closed__2;
extern lean_object* l_Lean_Core_instInhabitedState___closed__1;
lean_object* l_Lean_Elab_Command_getScopes___rarg(lean_object*, lean_object*);
lean_object* l_Lean_throwKernelException___at_Lean_Elab_Command_elabEvalUnsafe___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instAddMessageContextCommandElabM;
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkMessageAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_Parser_Command_variables___elambda__1___closed__2;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_1128____closed__3;
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenRenaming___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_failIfSucceeds___closed__3;
lean_object* l_Lean_Elab_Command_elabSynth___lambda__2___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_instMonadInfoTreeCommandElabM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabEval(lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___closed__5;
lean_object* l_Lean_Elab_Term_addAutoBoundImplicits(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenRenaming___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__5;
lean_object* l_Lean_Elab_Command_instInhabitedCommandElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabChoiceAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_State_ngen___default___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__7;
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___closed__4;
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__3;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariables(lean_object*);
lean_object* l_Lean_Syntax_asNode(lean_object*);
lean_object* lean_compile_decl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_mkMacroAttributeUnsafe___closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenOnly___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___closed__2;
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_Command_elabCommand___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Command_instMonadLogCommandElabM___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_State_nextMacroScope___default;
extern lean_object* l_Lean_scopedEnvExtensionsRef;
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1080____closed__1;
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInitQuot(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1;
lean_object* l_Lean_Elab_Command_elabCheck_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Elab_isFreshInstanceName(lean_object*);
lean_object* l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM;
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__2;
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___closed__1;
lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_addClass___closed__1;
lean_object* l_Lean_Elab_Command_liftTermElabM_match__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__6;
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___closed__3;
lean_object* l_Lean_Elab_Command_elabVariable___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinder___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse(lean_object*);
lean_object* l_Lean_Elab_Command_hasNoErrorMessages___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_getScopes___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenSimple___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addOpenDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabOpenRenaming___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_State_infoState___default;
lean_object* l_Lean_Elab_Command_elabOpenOnly___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_synth___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabInitQuot_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_elabSynth___closed__3;
lean_object* l_Lean_Elab_Command_elabReduce_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEnd_match__2(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_mkMessageAux(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkSimpleThunk(lean_object*);
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabNamespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_Elab_getMacroStackOption(lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
lean_object* l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_activateScoped___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___closed__5;
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___closed__3;
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__2;
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___closed__7;
lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_elabInitQuot___boxed(lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_runLinters___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__3;
lean_object* l_Lean_Elab_Command_instMonadLiftTIOCommandElabM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instInhabitedScope___closed__1;
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabUsingElabFns___closed__2;
lean_object* l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__2;
lean_object* l_Lean_Elab_Command_liftEIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_lintersRef;
lean_object* l_Lean_Elab_Command_runTermElabM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedInfoState___closed__1;
lean_object* l_Lean_Elab_Command_elabSetOption_match__3(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_getAux___rarg___closed__1;
lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenOnly___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Command_Scope_opts___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Scope_currNamespace___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Scope_openDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Scope_levelNames___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Scope_varDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedScope___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = lean_box(0);
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedScope() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instInhabitedScope___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_messages___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentArray_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_scopes___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_instInhabitedScope___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_scopes___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_State_scopes___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_nextMacroScope___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Unhygienic_run___rarg___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_nextInstIdx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_ngen___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_State_ngen___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_State_infoState___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_State_infoState___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_instInhabitedState___closed__1;
x_3 = l_Std_instInhabitedPersistentArray___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_instInhabitedNameGenerator___closed__1;
x_6 = l_Lean_Elab_instInhabitedInfoState___closed__1;
x_7 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_1);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_4);
lean_ctor_set(x_7, 5, x_4);
lean_ctor_set(x_7, 6, x_5);
lean_ctor_set(x_7, 7, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instInhabitedState___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Context_currRecDepth___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Context_cmdPos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Context_macroStack___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Context_currMacroScope___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_firstFrontendMacroScope;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Context_ref___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Lean_Elab_Command_mkState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_box(0);
x_5 = l_Lean_instInhabitedParserDescr___closed__1;
x_6 = lean_box(0);
x_7 = l_Array_empty___closed__1;
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 4, x_4);
lean_ctor_set(x_8, 5, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
x_10 = l_Lean_getMaxRecDepth(x_3);
lean_dec(x_3);
x_11 = l_Lean_Unhygienic_run___rarg___closed__2;
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Core_State_ngen___default___closed__1;
x_14 = l_Lean_Elab_Term_State_infoState___default___closed__1;
x_15 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_9);
lean_ctor_set(x_15, 3, x_11);
lean_ctor_set(x_15, 4, x_10);
lean_ctor_set(x_15, 5, x_12);
lean_ctor_set(x_15, 6, x_13);
lean_ctor_set(x_15, 7, x_14);
return x_15;
}
}
lean_object* l_IO_mkRef___at_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_155____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_155_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = l_IO_mkRef___at_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_155____spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_addLinter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = l_Lean_Elab_Command_lintersRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_array_push(x_5, x_1);
x_8 = lean_st_ref_set(x_3, x_7, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_instMonadInfoTreeCommandElabM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_4(x_2, x_7, x_3, x_4, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Command_instMonadInfoTreeCommandElabM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_instMonadInfoTreeCommandElabM___spec__1___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 7);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 7);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_6, 7, x_10);
x_11 = lean_st_ref_set(x_3, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_26 = lean_apply_1(x_1, x_25);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_21);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set(x_27, 5, x_23);
lean_ctor_set(x_27, 6, x_24);
lean_ctor_set(x_27, 7, x_26);
x_28 = lean_st_ref_set(x_3, x_27, x_7);
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
}
static lean_object* _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadEnvCoreM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_instMonadInfoTreeCommandElabM___spec__1___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__2;
x_2 = l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__4;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_6, 0, x_10);
x_11 = lean_st_ref_set(x_3, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_26 = lean_apply_1(x_1, x_18);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_21);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set(x_27, 5, x_23);
lean_ctor_set(x_27, 6, x_24);
lean_ctor_set(x_27, 7, x_25);
x_28 = lean_st_ref_set(x_3, x_27, x_7);
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
}
static lean_object* _init_l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadEnvCoreM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_instMonadInfoTreeCommandElabM___spec__1___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__2;
x_2 = l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadEnvCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__4;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadEnvCommandElabM___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Command_instInhabitedScope;
x_3 = l_List_head_x21___rarg___closed__3;
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
lean_object* l_Lean_Elab_Command_instMonadOptionsCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 2);
x_6 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadOptionsCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadOptionsCommandElabM___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadOptionsCommandElabM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadEnvCoreM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadOptionsCommandElabM___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_instMonadInfoTreeCommandElabM___spec__1___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadOptionsCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadOptionsCommandElabM___closed__2;
return x_1;
}
}
lean_object* l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_instMonadOptionsCommandElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadOptionsCommandElabM___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getRef(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 6);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getRef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_getRef(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_get(x_3, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_MetavarContext_instInhabitedMetavarContext___closed__1;
x_16 = l_Lean_LocalContext_mkEmpty___closed__1;
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_17, 3, x_14);
x_18 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_MetavarContext_instInhabitedMetavarContext___closed__1;
x_25 = l_Lean_LocalContext_mkEmpty___closed__1;
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_26, 3, x_23);
x_27 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_20);
return x_28;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_instAddMessageContextCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instAddMessageContextCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instAddMessageContextCommandElabM___closed__1;
return x_1;
}
}
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_instMonadRefCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 6);
lean_dec(x_8);
lean_ctor_set(x_4, 6, x_2);
x_9 = lean_apply_3(x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_4, 4);
x_15 = lean_ctor_get(x_4, 5);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set(x_16, 4, x_14);
lean_ctor_set(x_16, 5, x_15);
lean_ctor_set(x_16, 6, x_2);
x_17 = lean_apply_3(x_3, x_16, x_5, x_6);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRefCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getRef___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRefCommandElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadRefCommandElabM___lambda__1), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRefCommandElabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_instMonadRefCommandElabM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadRefCommandElabM___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRefCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadRefCommandElabM___closed__3;
return x_1;
}
}
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_getMacroStackOption(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_MessageData_ofList___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__3;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_indentD(x_19);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_List_foldl___at_Lean_Elab_addMacroStack___spec__1(x_14, x_21, x_2);
lean_ctor_set(x_6, 0, x_22);
return x_6;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_ctor_get(x_23, 2);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Elab_getMacroStackOption(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_2, 0);
x_32 = l_Lean_MessageData_ofList___closed__3;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Elab_addMacroStack___rarg___lambda__1___closed__3;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_indentD(x_37);
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_List_foldl___at_Lean_Elab_addMacroStack___spec__1(x_32, x_39, x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_24);
return x_41;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_3, 4);
lean_inc(x_6);
lean_inc(x_6);
x_7 = l_Lean_Elab_getBetterRef(x_1, x_6);
x_8 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_9, x_6, x_3, x_4, x_10);
lean_dec(x_3);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_instAddErrorMessageContextCommandElabM(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_mkMessageAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_Lean_Syntax_getPos(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Elab_mkMessageCore(x_5, x_6, x_3, x_4, x_8);
lean_dec(x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Elab_mkMessageCore(x_5, x_6, x_3, x_4, x_10);
lean_dec(x_6);
return x_11;
}
}
}
lean_object* l_Lean_Elab_Command_mkMessageAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Elab_Command_mkMessageAux(x_1, x_2, x_3, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 2);
x_4 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_ctor_get(x_1, 6);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 3);
lean_inc(x_10);
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_7);
lean_ctor_set(x_11, 3, x_8);
lean_ctor_set(x_11, 4, x_9);
lean_ctor_set(x_11, 5, x_10);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_liftCoreM_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Command_liftCoreM_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftCoreM_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_liftCoreM_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Command_liftCoreM_match__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftCoreM_match__2___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_liftCoreM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_47 = lean_st_ref_get(x_3, x_4);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext(x_2, x_48);
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 6);
lean_inc(x_52);
lean_dec(x_48);
x_53 = l_Lean_Unhygienic_run___rarg___closed__2;
x_54 = l_Lean_resetTraceState___rarg___lambda__1___closed__1;
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_52);
lean_ctor_set(x_55, 3, x_54);
x_56 = lean_st_mk_ref(x_55, x_49);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_57);
x_59 = lean_apply_3(x_1, x_50, x_57, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_60);
x_63 = lean_st_ref_get(x_57, x_61);
lean_dec(x_57);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_64);
x_5 = x_66;
x_6 = x_65;
goto block_46;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_59, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_59, 1);
lean_inc(x_68);
lean_dec(x_59);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_67);
x_70 = lean_st_ref_get(x_57, x_68);
lean_dec(x_57);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_71);
x_5 = x_73;
x_6 = x_72;
goto block_46;
}
block_46:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_st_ref_take(x_3, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 6);
lean_dec(x_15);
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
lean_ctor_set(x_10, 6, x_13);
lean_ctor_set(x_10, 0, x_12);
x_17 = lean_st_ref_set(x_3, x_10, x_11);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec(x_7);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
lean_dec(x_7);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_7, 0);
lean_inc(x_28);
lean_dec(x_7);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_10, 1);
x_31 = lean_ctor_get(x_10, 2);
x_32 = lean_ctor_get(x_10, 3);
x_33 = lean_ctor_get(x_10, 4);
x_34 = lean_ctor_get(x_10, 5);
x_35 = lean_ctor_get(x_10, 7);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_36 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_36, 0, x_12);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_31);
lean_ctor_set(x_36, 3, x_32);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set(x_36, 5, x_34);
lean_ctor_set(x_36, 6, x_13);
lean_ctor_set(x_36, 7, x_35);
x_37 = lean_st_ref_set(x_3, x_36, x_11);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_7, 0);
lean_inc(x_40);
lean_dec(x_7);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_39;
 lean_ctor_set_tag(x_41, 1);
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_43 = x_37;
} else {
 lean_dec_ref(x_37);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_7, 0);
lean_inc(x_44);
lean_dec(x_7);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_liftCoreM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftCoreM___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_liftCoreM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_liftCoreM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_ioErrorToMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
x_5 = l_Lean_Elab_getBetterRef(x_2, x_4);
x_6 = lean_io_error_to_string(x_3);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = 2;
x_10 = l_Lean_Elab_Command_mkMessageAux(x_1, x_5, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_ioErrorToMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_ioErrorToMessage(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_liftEIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_liftEIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftEIO___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_liftEIO___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_liftEIO___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_liftIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_io_error_to_string(x_11);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_ctor_get(x_2, 6);
x_20 = lean_io_error_to_string(x_17);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_inc(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Command_liftIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftIO___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_liftIO___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_liftIO___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_instMonadLiftTIOCommandElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_io_error_to_string(x_11);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_ctor_get(x_2, 6);
x_20 = lean_io_error_to_string(x_17);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_inc(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Command_instMonadLiftTIOCommandElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadLiftTIOCommandElabM___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_instMonadLiftTIOCommandElabM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadLiftTIOCommandElabM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
lean_object* l_Lean_Elab_Command_getScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getScope___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_getScope___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getScope___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_getScope___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getScope(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getScope___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_instMonadInfoTreeCommandElabM___spec__1___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__4;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_instMonadInfoTreeCommandElabM___spec__1___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__3;
x_2 = l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__6;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadResolveNameCommandElabM___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_ReaderT_read___at_Lean_Elab_Command_instMonadLogCommandElabM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = l_Lean_Elab_Command_getScope___rarg(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_getScope___rarg(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_1, 4, x_16);
x_17 = lean_st_ref_take(x_3, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_18, 1);
x_22 = l_Std_PersistentArray_push___rarg(x_21, x_1);
lean_ctor_set(x_18, 1, x_22);
x_23 = lean_st_ref_set(x_3, x_18, x_19);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
x_32 = lean_ctor_get(x_18, 2);
x_33 = lean_ctor_get(x_18, 3);
x_34 = lean_ctor_get(x_18, 4);
x_35 = lean_ctor_get(x_18, 5);
x_36 = lean_ctor_get(x_18, 6);
x_37 = lean_ctor_get(x_18, 7);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_38 = l_Std_PersistentArray_push___rarg(x_31, x_1);
x_39 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_33);
lean_ctor_set(x_39, 4, x_34);
lean_ctor_set(x_39, 5, x_35);
lean_ctor_set(x_39, 6, x_36);
lean_ctor_set(x_39, 7, x_37);
x_40 = lean_st_ref_set(x_3, x_39, x_19);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_45 = lean_ctor_get(x_1, 0);
x_46 = lean_ctor_get(x_1, 1);
x_47 = lean_ctor_get(x_1, 2);
x_48 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_49 = lean_ctor_get(x_1, 3);
x_50 = lean_ctor_get(x_1, 4);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_8);
lean_ctor_set(x_51, 1, x_12);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_46);
lean_ctor_set(x_53, 2, x_47);
lean_ctor_set(x_53, 3, x_49);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*5, x_48);
x_54 = lean_st_ref_take(x_3, x_11);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 5);
lean_inc(x_62);
x_63 = lean_ctor_get(x_55, 6);
lean_inc(x_63);
x_64 = lean_ctor_get(x_55, 7);
lean_inc(x_64);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 lean_ctor_release(x_55, 4);
 lean_ctor_release(x_55, 5);
 lean_ctor_release(x_55, 6);
 lean_ctor_release(x_55, 7);
 x_65 = x_55;
} else {
 lean_dec_ref(x_55);
 x_65 = lean_box(0);
}
x_66 = l_Std_PersistentArray_push___rarg(x_58, x_53);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 8, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_57);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_59);
lean_ctor_set(x_67, 3, x_60);
lean_ctor_set(x_67, 4, x_61);
lean_ctor_set(x_67, 5, x_62);
lean_ctor_set(x_67, 6, x_63);
lean_ctor_set(x_67, 7, x_64);
x_68 = lean_st_ref_set(x_3, x_67, x_56);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Elab_Command_instMonadLogCommandElabM___spec__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_instMonadLogCommandElabM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadLogCommandElabM___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_instMonadInfoTreeCommandElabM___spec__1___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_instMonadLogCommandElabM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadLogCommandElabM___closed__4;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_instMonadInfoTreeCommandElabM___spec__1___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__3___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_instMonadLogCommandElabM___closed__3;
x_2 = l_Lean_Elab_Command_instMonadRefCommandElabM___closed__1;
x_3 = l_Lean_Elab_Command_instMonadLogCommandElabM___closed__5;
x_4 = l_Lean_Elab_Command_instMonadLogCommandElabM___closed__6;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadLogCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadLogCommandElabM___closed__7;
return x_1;
}
}
lean_object* l_ReaderT_read___at_Lean_Elab_Command_instMonadLogCommandElabM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_read___at_Lean_Elab_Command_instMonadLogCommandElabM___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadLogCommandElabM___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_runLinters_match__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_runLinters_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runLinters_match__1___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_runLinters_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_runLinters_match__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_runLinters___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_331; uint8_t x_332; 
x_331 = 2;
x_332 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_99_(x_3, x_331);
if (x_332 == 0)
{
lean_object* x_333; 
x_333 = lean_box(0);
x_7 = x_333;
goto block_330;
}
else
{
uint8_t x_334; 
x_334 = l_Lean_MessageData_hasSyntheticSorry(x_2);
if (x_334 == 0)
{
lean_object* x_335; 
x_335 = lean_box(0);
x_7 = x_335;
goto block_330;
}
else
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_2);
x_336 = lean_box(0);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_6);
return x_337;
}
}
block_330:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
x_8 = l_Lean_Elab_Command_getRef(x_4, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_replaceRef(x_1, x_9);
lean_dec(x_9);
x_12 = l_Lean_Syntax_getPos(x_11);
x_13 = l_Lean_Syntax_getTailPos(x_11);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_FileMap_toPosition(x_15, x_19);
lean_inc(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Elab_Command_getScope___rarg(x_5, x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 2);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Command_getScope___rarg(x_5, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 3);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_17);
x_32 = l_Lean_instInhabitedParserDescr___closed__1;
lean_inc(x_14);
x_33 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_20);
lean_ctor_set(x_33, 2, x_21);
lean_ctor_set(x_33, 3, x_32);
lean_ctor_set(x_33, 4, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*5, x_3);
x_34 = lean_st_ref_take(x_5, x_28);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_35, 1);
x_39 = l_Std_PersistentArray_push___rarg(x_38, x_33);
lean_ctor_set(x_35, 1, x_39);
x_40 = lean_st_ref_set(x_5, x_35, x_36);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_47 = lean_ctor_get(x_35, 0);
x_48 = lean_ctor_get(x_35, 1);
x_49 = lean_ctor_get(x_35, 2);
x_50 = lean_ctor_get(x_35, 3);
x_51 = lean_ctor_get(x_35, 4);
x_52 = lean_ctor_get(x_35, 5);
x_53 = lean_ctor_get(x_35, 6);
x_54 = lean_ctor_get(x_35, 7);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_35);
x_55 = l_Std_PersistentArray_push___rarg(x_48, x_33);
x_56 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_49);
lean_ctor_set(x_56, 3, x_50);
lean_ctor_set(x_56, 4, x_51);
lean_ctor_set(x_56, 5, x_52);
lean_ctor_set(x_56, 6, x_53);
lean_ctor_set(x_56, 7, x_54);
x_57 = lean_st_ref_set(x_5, x_56, x_36);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_13);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_63 = lean_ctor_get(x_13, 0);
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get(x_4, 1);
x_66 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unsigned_to_nat(0u);
x_70 = l_Lean_FileMap_toPosition(x_65, x_69);
x_71 = l_Lean_FileMap_toPosition(x_65, x_63);
lean_ctor_set(x_13, 0, x_71);
x_72 = l_Lean_Elab_Command_getScope___rarg(x_5, x_68);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 2);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Elab_Command_getScope___rarg(x_5, x_74);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 3);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_67);
x_82 = l_Lean_instInhabitedParserDescr___closed__1;
lean_inc(x_64);
x_83 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_83, 0, x_64);
lean_ctor_set(x_83, 1, x_70);
lean_ctor_set(x_83, 2, x_13);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set(x_83, 4, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*5, x_3);
x_84 = lean_st_ref_take(x_5, x_78);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_85, 1);
x_89 = l_Std_PersistentArray_push___rarg(x_88, x_83);
lean_ctor_set(x_85, 1, x_89);
x_90 = lean_st_ref_set(x_5, x_85, x_86);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
x_93 = lean_box(0);
lean_ctor_set(x_90, 0, x_93);
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_97 = lean_ctor_get(x_85, 0);
x_98 = lean_ctor_get(x_85, 1);
x_99 = lean_ctor_get(x_85, 2);
x_100 = lean_ctor_get(x_85, 3);
x_101 = lean_ctor_get(x_85, 4);
x_102 = lean_ctor_get(x_85, 5);
x_103 = lean_ctor_get(x_85, 6);
x_104 = lean_ctor_get(x_85, 7);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_85);
x_105 = l_Std_PersistentArray_push___rarg(x_98, x_83);
x_106 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_106, 0, x_97);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_99);
lean_ctor_set(x_106, 3, x_100);
lean_ctor_set(x_106, 4, x_101);
lean_ctor_set(x_106, 5, x_102);
lean_ctor_set(x_106, 6, x_103);
lean_ctor_set(x_106, 7, x_104);
x_107 = lean_st_ref_set(x_5, x_106, x_86);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_112 = lean_ctor_get(x_13, 0);
lean_inc(x_112);
lean_dec(x_13);
x_113 = lean_ctor_get(x_4, 0);
x_114 = lean_ctor_get(x_4, 1);
x_115 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_unsigned_to_nat(0u);
x_119 = l_Lean_FileMap_toPosition(x_114, x_118);
x_120 = l_Lean_FileMap_toPosition(x_114, x_112);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = l_Lean_Elab_Command_getScope___rarg(x_5, x_117);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get(x_123, 2);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l_Lean_Elab_Command_getScope___rarg(x_5, x_124);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 3);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_116);
x_132 = l_Lean_instInhabitedParserDescr___closed__1;
lean_inc(x_113);
x_133 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_133, 0, x_113);
lean_ctor_set(x_133, 1, x_119);
lean_ctor_set(x_133, 2, x_121);
lean_ctor_set(x_133, 3, x_132);
lean_ctor_set(x_133, 4, x_131);
lean_ctor_set_uint8(x_133, sizeof(void*)*5, x_3);
x_134 = lean_st_ref_take(x_5, x_128);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_135, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_135, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 4);
lean_inc(x_141);
x_142 = lean_ctor_get(x_135, 5);
lean_inc(x_142);
x_143 = lean_ctor_get(x_135, 6);
lean_inc(x_143);
x_144 = lean_ctor_get(x_135, 7);
lean_inc(x_144);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 lean_ctor_release(x_135, 5);
 lean_ctor_release(x_135, 6);
 lean_ctor_release(x_135, 7);
 x_145 = x_135;
} else {
 lean_dec_ref(x_135);
 x_145 = lean_box(0);
}
x_146 = l_Std_PersistentArray_push___rarg(x_138, x_133);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 8, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_137);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_139);
lean_ctor_set(x_147, 3, x_140);
lean_ctor_set(x_147, 4, x_141);
lean_ctor_set(x_147, 5, x_142);
lean_ctor_set(x_147, 6, x_143);
lean_ctor_set(x_147, 7, x_144);
x_148 = lean_st_ref_set(x_5, x_147, x_136);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
x_151 = lean_box(0);
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_150;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_149);
return x_152;
}
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_12);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_154 = lean_ctor_get(x_12, 0);
x_155 = lean_ctor_get(x_4, 0);
x_156 = lean_ctor_get(x_4, 1);
x_157 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Lean_FileMap_toPosition(x_156, x_154);
lean_inc(x_160);
lean_ctor_set(x_12, 0, x_160);
x_161 = l_Lean_Elab_Command_getScope___rarg(x_5, x_159);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get(x_162, 2);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_Lean_Elab_Command_getScope___rarg(x_5, x_163);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_166, 3);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_164);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_158);
x_171 = l_Lean_instInhabitedParserDescr___closed__1;
lean_inc(x_155);
x_172 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_172, 0, x_155);
lean_ctor_set(x_172, 1, x_160);
lean_ctor_set(x_172, 2, x_12);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set(x_172, 4, x_170);
lean_ctor_set_uint8(x_172, sizeof(void*)*5, x_3);
x_173 = lean_st_ref_take(x_5, x_167);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = !lean_is_exclusive(x_174);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_177 = lean_ctor_get(x_174, 1);
x_178 = l_Std_PersistentArray_push___rarg(x_177, x_172);
lean_ctor_set(x_174, 1, x_178);
x_179 = lean_st_ref_set(x_5, x_174, x_175);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_179, 0);
lean_dec(x_181);
x_182 = lean_box(0);
lean_ctor_set(x_179, 0, x_182);
return x_179;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_179, 1);
lean_inc(x_183);
lean_dec(x_179);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_186 = lean_ctor_get(x_174, 0);
x_187 = lean_ctor_get(x_174, 1);
x_188 = lean_ctor_get(x_174, 2);
x_189 = lean_ctor_get(x_174, 3);
x_190 = lean_ctor_get(x_174, 4);
x_191 = lean_ctor_get(x_174, 5);
x_192 = lean_ctor_get(x_174, 6);
x_193 = lean_ctor_get(x_174, 7);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_174);
x_194 = l_Std_PersistentArray_push___rarg(x_187, x_172);
x_195 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_195, 0, x_186);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_195, 2, x_188);
lean_ctor_set(x_195, 3, x_189);
lean_ctor_set(x_195, 4, x_190);
lean_ctor_set(x_195, 5, x_191);
lean_ctor_set(x_195, 6, x_192);
lean_ctor_set(x_195, 7, x_193);
x_196 = lean_st_ref_set(x_5, x_195, x_175);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
x_199 = lean_box(0);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_197);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_201 = lean_ctor_get(x_12, 0);
lean_inc(x_201);
lean_dec(x_12);
x_202 = lean_ctor_get(x_4, 0);
x_203 = lean_ctor_get(x_4, 1);
x_204 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = l_Lean_FileMap_toPosition(x_203, x_201);
lean_inc(x_207);
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_207);
x_209 = l_Lean_Elab_Command_getScope___rarg(x_5, x_206);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_ctor_get(x_210, 2);
lean_inc(x_212);
lean_dec(x_210);
x_213 = l_Lean_Elab_Command_getScope___rarg(x_5, x_211);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_ctor_get(x_214, 3);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_212);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_205);
x_219 = l_Lean_instInhabitedParserDescr___closed__1;
lean_inc(x_202);
x_220 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_220, 0, x_202);
lean_ctor_set(x_220, 1, x_207);
lean_ctor_set(x_220, 2, x_208);
lean_ctor_set(x_220, 3, x_219);
lean_ctor_set(x_220, 4, x_218);
lean_ctor_set_uint8(x_220, sizeof(void*)*5, x_3);
x_221 = lean_st_ref_take(x_5, x_215);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_222, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_222, 3);
lean_inc(x_227);
x_228 = lean_ctor_get(x_222, 4);
lean_inc(x_228);
x_229 = lean_ctor_get(x_222, 5);
lean_inc(x_229);
x_230 = lean_ctor_get(x_222, 6);
lean_inc(x_230);
x_231 = lean_ctor_get(x_222, 7);
lean_inc(x_231);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 lean_ctor_release(x_222, 2);
 lean_ctor_release(x_222, 3);
 lean_ctor_release(x_222, 4);
 lean_ctor_release(x_222, 5);
 lean_ctor_release(x_222, 6);
 lean_ctor_release(x_222, 7);
 x_232 = x_222;
} else {
 lean_dec_ref(x_222);
 x_232 = lean_box(0);
}
x_233 = l_Std_PersistentArray_push___rarg(x_225, x_220);
if (lean_is_scalar(x_232)) {
 x_234 = lean_alloc_ctor(0, 8, 0);
} else {
 x_234 = x_232;
}
lean_ctor_set(x_234, 0, x_224);
lean_ctor_set(x_234, 1, x_233);
lean_ctor_set(x_234, 2, x_226);
lean_ctor_set(x_234, 3, x_227);
lean_ctor_set(x_234, 4, x_228);
lean_ctor_set(x_234, 5, x_229);
lean_ctor_set(x_234, 6, x_230);
lean_ctor_set(x_234, 7, x_231);
x_235 = lean_st_ref_set(x_5, x_234, x_223);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_237 = x_235;
} else {
 lean_dec_ref(x_235);
 x_237 = lean_box(0);
}
x_238 = lean_box(0);
if (lean_is_scalar(x_237)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_237;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_236);
return x_239;
}
}
else
{
lean_object* x_240; uint8_t x_241; 
x_240 = lean_ctor_get(x_12, 0);
lean_inc(x_240);
lean_dec(x_12);
x_241 = !lean_is_exclusive(x_13);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_242 = lean_ctor_get(x_13, 0);
x_243 = lean_ctor_get(x_4, 0);
x_244 = lean_ctor_get(x_4, 1);
x_245 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = l_Lean_FileMap_toPosition(x_244, x_240);
x_249 = l_Lean_FileMap_toPosition(x_244, x_242);
lean_ctor_set(x_13, 0, x_249);
x_250 = l_Lean_Elab_Command_getScope___rarg(x_5, x_247);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_ctor_get(x_251, 2);
lean_inc(x_253);
lean_dec(x_251);
x_254 = l_Lean_Elab_Command_getScope___rarg(x_5, x_252);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_ctor_get(x_255, 3);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_253);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_246);
x_260 = l_Lean_instInhabitedParserDescr___closed__1;
lean_inc(x_243);
x_261 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_261, 0, x_243);
lean_ctor_set(x_261, 1, x_248);
lean_ctor_set(x_261, 2, x_13);
lean_ctor_set(x_261, 3, x_260);
lean_ctor_set(x_261, 4, x_259);
lean_ctor_set_uint8(x_261, sizeof(void*)*5, x_3);
x_262 = lean_st_ref_take(x_5, x_256);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = !lean_is_exclusive(x_263);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_266 = lean_ctor_get(x_263, 1);
x_267 = l_Std_PersistentArray_push___rarg(x_266, x_261);
lean_ctor_set(x_263, 1, x_267);
x_268 = lean_st_ref_set(x_5, x_263, x_264);
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_268, 0);
lean_dec(x_270);
x_271 = lean_box(0);
lean_ctor_set(x_268, 0, x_271);
return x_268;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_268, 1);
lean_inc(x_272);
lean_dec(x_268);
x_273 = lean_box(0);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_275 = lean_ctor_get(x_263, 0);
x_276 = lean_ctor_get(x_263, 1);
x_277 = lean_ctor_get(x_263, 2);
x_278 = lean_ctor_get(x_263, 3);
x_279 = lean_ctor_get(x_263, 4);
x_280 = lean_ctor_get(x_263, 5);
x_281 = lean_ctor_get(x_263, 6);
x_282 = lean_ctor_get(x_263, 7);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_263);
x_283 = l_Std_PersistentArray_push___rarg(x_276, x_261);
x_284 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_284, 0, x_275);
lean_ctor_set(x_284, 1, x_283);
lean_ctor_set(x_284, 2, x_277);
lean_ctor_set(x_284, 3, x_278);
lean_ctor_set(x_284, 4, x_279);
lean_ctor_set(x_284, 5, x_280);
lean_ctor_set(x_284, 6, x_281);
lean_ctor_set(x_284, 7, x_282);
x_285 = lean_st_ref_set(x_5, x_284, x_264);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_287 = x_285;
} else {
 lean_dec_ref(x_285);
 x_287 = lean_box(0);
}
x_288 = lean_box(0);
if (lean_is_scalar(x_287)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_287;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_286);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_290 = lean_ctor_get(x_13, 0);
lean_inc(x_290);
lean_dec(x_13);
x_291 = lean_ctor_get(x_4, 0);
x_292 = lean_ctor_get(x_4, 1);
x_293 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
x_296 = l_Lean_FileMap_toPosition(x_292, x_240);
x_297 = l_Lean_FileMap_toPosition(x_292, x_290);
x_298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_298, 0, x_297);
x_299 = l_Lean_Elab_Command_getScope___rarg(x_5, x_295);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_ctor_get(x_300, 2);
lean_inc(x_302);
lean_dec(x_300);
x_303 = l_Lean_Elab_Command_getScope___rarg(x_5, x_301);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = lean_ctor_get(x_304, 3);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_302);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_294);
x_309 = l_Lean_instInhabitedParserDescr___closed__1;
lean_inc(x_291);
x_310 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_310, 0, x_291);
lean_ctor_set(x_310, 1, x_296);
lean_ctor_set(x_310, 2, x_298);
lean_ctor_set(x_310, 3, x_309);
lean_ctor_set(x_310, 4, x_308);
lean_ctor_set_uint8(x_310, sizeof(void*)*5, x_3);
x_311 = lean_st_ref_take(x_5, x_305);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_314 = lean_ctor_get(x_312, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_312, 1);
lean_inc(x_315);
x_316 = lean_ctor_get(x_312, 2);
lean_inc(x_316);
x_317 = lean_ctor_get(x_312, 3);
lean_inc(x_317);
x_318 = lean_ctor_get(x_312, 4);
lean_inc(x_318);
x_319 = lean_ctor_get(x_312, 5);
lean_inc(x_319);
x_320 = lean_ctor_get(x_312, 6);
lean_inc(x_320);
x_321 = lean_ctor_get(x_312, 7);
lean_inc(x_321);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 lean_ctor_release(x_312, 2);
 lean_ctor_release(x_312, 3);
 lean_ctor_release(x_312, 4);
 lean_ctor_release(x_312, 5);
 lean_ctor_release(x_312, 6);
 lean_ctor_release(x_312, 7);
 x_322 = x_312;
} else {
 lean_dec_ref(x_312);
 x_322 = lean_box(0);
}
x_323 = l_Std_PersistentArray_push___rarg(x_315, x_310);
if (lean_is_scalar(x_322)) {
 x_324 = lean_alloc_ctor(0, 8, 0);
} else {
 x_324 = x_322;
}
lean_ctor_set(x_324, 0, x_314);
lean_ctor_set(x_324, 1, x_323);
lean_ctor_set(x_324, 2, x_316);
lean_ctor_set(x_324, 3, x_317);
lean_ctor_set(x_324, 4, x_318);
lean_ctor_set(x_324, 5, x_319);
lean_ctor_set(x_324, 6, x_320);
lean_ctor_set(x_324, 7, x_321);
x_325 = lean_st_ref_set(x_5, x_324, x_313);
x_326 = lean_ctor_get(x_325, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_327 = x_325;
} else {
 lean_dec_ref(x_325);
 x_327 = lean_box(0);
}
x_328 = lean_box(0);
if (lean_is_scalar(x_327)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_327;
}
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_326);
return x_329;
}
}
}
}
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_7, x_1, x_2, x_3, x_4, x_8);
lean_dec(x_7);
return x_9;
}
}
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = 2;
x_8 = l_Lean_Elab_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_5, x_6, x_7, x_2, x_3, x_4);
lean_dec(x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = l_Lean_Elab_isAbortExceptionId(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_InternalExceptionId_getName(x_10, x_4);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_free_object(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = l_Lean_Elab_logException___rarg___lambda__1___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_KernelException_toMessageData___closed__15;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = 2;
x_22 = l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3(x_20, x_21, x_2, x_3, x_15);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_2, 6);
x_26 = lean_io_error_to_string(x_24);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_inc(x_25);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_28);
lean_ctor_set(x_1, 0, x_25);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_ctor_get(x_2, 6);
x_32 = lean_io_error_to_string(x_29);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_inc(x_31);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_1);
lean_dec(x_10);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_4);
return x_37;
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = l_Lean_Elab_isAbortExceptionId(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Lean_InternalExceptionId_getName(x_38, x_4);
lean_dec(x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_43, 0, x_41);
x_44 = l_Lean_Elab_logException___rarg___lambda__1___closed__2;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_KernelException_toMessageData___closed__15;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = 2;
x_49 = l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3(x_47, x_48, x_2, x_3, x_42);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_40, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_52 = x_40;
} else {
 lean_dec_ref(x_40);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_2, 6);
x_54 = lean_io_error_to_string(x_50);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_inc(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_52)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_52;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_51);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_38);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_4);
return x_60;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_21; 
x_21 = x_4 < x_3;
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
x_23 = lean_st_ref_get(x_7, x_8);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_array_uget(x_2, x_4);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_27 = lean_apply_4(x_26, x_1, x_6, x_7, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_take(x_7, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_24, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_24, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_24, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_24, 5);
lean_inc(x_36);
x_37 = lean_ctor_get(x_24, 6);
lean_inc(x_37);
x_38 = lean_ctor_get(x_24, 7);
lean_inc(x_38);
lean_dec(x_24);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_40 = lean_ctor_get(x_30, 7);
lean_dec(x_40);
x_41 = lean_ctor_get(x_30, 6);
lean_dec(x_41);
x_42 = lean_ctor_get(x_30, 5);
lean_dec(x_42);
x_43 = lean_ctor_get(x_30, 4);
lean_dec(x_43);
x_44 = lean_ctor_get(x_30, 3);
lean_dec(x_44);
x_45 = lean_ctor_get(x_30, 2);
lean_dec(x_45);
x_46 = lean_ctor_get(x_30, 0);
lean_dec(x_46);
lean_ctor_set(x_30, 7, x_38);
lean_ctor_set(x_30, 6, x_37);
lean_ctor_set(x_30, 5, x_36);
lean_ctor_set(x_30, 4, x_35);
lean_ctor_set(x_30, 3, x_34);
lean_ctor_set(x_30, 2, x_33);
lean_ctor_set(x_30, 0, x_32);
x_47 = lean_st_ref_set(x_7, x_30, x_31);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_ctor_set(x_47, 0, x_50);
x_9 = x_47;
goto block_20;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_9 = x_53;
goto block_20;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_30, 1);
lean_inc(x_54);
lean_dec(x_30);
x_55 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_55, 0, x_32);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_33);
lean_ctor_set(x_55, 3, x_34);
lean_ctor_set(x_55, 4, x_35);
lean_ctor_set(x_55, 5, x_36);
lean_ctor_set(x_55, 6, x_37);
lean_ctor_set(x_55, 7, x_38);
x_56 = lean_st_ref_set(x_7, x_55, x_31);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
x_9 = x_60;
goto block_20;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_27, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_27, 1);
lean_inc(x_62);
lean_dec(x_27);
x_63 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_61, x_6, x_7, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_st_ref_take(x_7, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_24, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_24, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_24, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_24, 4);
lean_inc(x_71);
x_72 = lean_ctor_get(x_24, 5);
lean_inc(x_72);
x_73 = lean_ctor_get(x_24, 6);
lean_inc(x_73);
x_74 = lean_ctor_get(x_24, 7);
lean_inc(x_74);
lean_dec(x_24);
x_75 = !lean_is_exclusive(x_66);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_76 = lean_ctor_get(x_66, 7);
lean_dec(x_76);
x_77 = lean_ctor_get(x_66, 6);
lean_dec(x_77);
x_78 = lean_ctor_get(x_66, 5);
lean_dec(x_78);
x_79 = lean_ctor_get(x_66, 4);
lean_dec(x_79);
x_80 = lean_ctor_get(x_66, 3);
lean_dec(x_80);
x_81 = lean_ctor_get(x_66, 2);
lean_dec(x_81);
x_82 = lean_ctor_get(x_66, 0);
lean_dec(x_82);
lean_ctor_set(x_66, 7, x_74);
lean_ctor_set(x_66, 6, x_73);
lean_ctor_set(x_66, 5, x_72);
lean_ctor_set(x_66, 4, x_71);
lean_ctor_set(x_66, 3, x_70);
lean_ctor_set(x_66, 2, x_69);
lean_ctor_set(x_66, 0, x_68);
x_83 = lean_st_ref_set(x_7, x_66, x_67);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
x_86 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_ctor_set(x_83, 0, x_86);
x_9 = x_83;
goto block_20;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
x_88 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_9 = x_89;
goto block_20;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_66, 1);
lean_inc(x_90);
lean_dec(x_66);
x_91 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_91, 0, x_68);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_69);
lean_ctor_set(x_91, 3, x_70);
lean_ctor_set(x_91, 4, x_71);
lean_ctor_set(x_91, 5, x_72);
lean_ctor_set(x_91, 6, x_73);
lean_ctor_set(x_91, 7, x_74);
x_92 = lean_st_ref_set(x_7, x_91, x_67);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
x_9 = x_96;
goto block_20;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_97 = lean_ctor_get(x_63, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_63, 1);
lean_inc(x_98);
lean_dec(x_63);
x_99 = lean_st_ref_take(x_7, x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_ctor_get(x_24, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_24, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_24, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_24, 4);
lean_inc(x_105);
x_106 = lean_ctor_get(x_24, 5);
lean_inc(x_106);
x_107 = lean_ctor_get(x_24, 6);
lean_inc(x_107);
x_108 = lean_ctor_get(x_24, 7);
lean_inc(x_108);
lean_dec(x_24);
x_109 = !lean_is_exclusive(x_100);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_110 = lean_ctor_get(x_100, 7);
lean_dec(x_110);
x_111 = lean_ctor_get(x_100, 6);
lean_dec(x_111);
x_112 = lean_ctor_get(x_100, 5);
lean_dec(x_112);
x_113 = lean_ctor_get(x_100, 4);
lean_dec(x_113);
x_114 = lean_ctor_get(x_100, 3);
lean_dec(x_114);
x_115 = lean_ctor_get(x_100, 2);
lean_dec(x_115);
x_116 = lean_ctor_get(x_100, 0);
lean_dec(x_116);
lean_ctor_set(x_100, 7, x_108);
lean_ctor_set(x_100, 6, x_107);
lean_ctor_set(x_100, 5, x_106);
lean_ctor_set(x_100, 4, x_105);
lean_ctor_set(x_100, 3, x_104);
lean_ctor_set(x_100, 2, x_103);
lean_ctor_set(x_100, 0, x_102);
x_117 = lean_st_ref_set(x_7, x_100, x_101);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_117, 0);
lean_dec(x_119);
lean_ctor_set_tag(x_117, 1);
lean_ctor_set(x_117, 0, x_97);
x_9 = x_117;
goto block_20;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_97);
lean_ctor_set(x_121, 1, x_120);
x_9 = x_121;
goto block_20;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_122 = lean_ctor_get(x_100, 1);
lean_inc(x_122);
lean_dec(x_100);
x_123 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_123, 0, x_102);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_123, 2, x_103);
lean_ctor_set(x_123, 3, x_104);
lean_ctor_set(x_123, 4, x_105);
lean_ctor_set(x_123, 5, x_106);
lean_ctor_set(x_123, 6, x_107);
lean_ctor_set(x_123, 7, x_108);
x_124 = lean_st_ref_set(x_7, x_123, x_101);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
 lean_ctor_set_tag(x_127, 1);
}
lean_ctor_set(x_127, 0, x_97);
lean_ctor_set(x_127, 1, x_125);
x_9 = x_127;
goto block_20;
}
}
}
}
block_20:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = x_4 + x_13;
x_4 = x_14;
x_5 = x_12;
x_8 = x_11;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_runLinters(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Elab_Command_lintersRef;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Array_isEmpty___rarg(x_8);
if (x_10 == 0)
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_6);
x_11 = lean_array_get_size(x_8);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = lean_box(0);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4(x_1, x_8, x_12, x_13, x_14, x_2, x_3, x_9);
lean_dec(x_8);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
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
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_box(0);
lean_ctor_set(x_6, 0, x_24);
return x_6;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
x_27 = l_Array_isEmpty___rarg(x_25);
if (x_27 == 0)
{
lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_array_get_size(x_25);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = 0;
x_31 = lean_box(0);
x_32 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4(x_1, x_25, x_29, x_30, x_31, x_2, x_3, x_26);
lean_dec(x_25);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_38 = x_32;
} else {
 lean_dec_ref(x_32);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_26);
return x_41;
}
}
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_runLinters___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Elab_logAt___at_Lean_Elab_Command_runLinters___spec__2(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runLinters___spec__4(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getCurrMacroScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_getCurrMacroScope(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_environment_main_module(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_environment_main_module(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
lean_object* l_Lean_Elab_Command_getMainModule(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getMainModule___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_getMainModule___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getMainModule___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_getMainModule___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getMainModule(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_withFreshMacroScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_ctor_set(x_6, 3, x_11);
x_12 = lean_st_ref_set(x_3, x_6, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_2, 5);
lean_dec(x_15);
lean_ctor_set(x_2, 5, x_9);
x_16 = lean_apply_3(x_1, x_2, x_3, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
x_21 = lean_ctor_get(x_2, 4);
x_22 = lean_ctor_get(x_2, 6);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_9);
lean_ctor_set(x_23, 6, x_22);
x_24 = lean_apply_3(x_1, x_23, x_3, x_13);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
x_27 = lean_ctor_get(x_6, 2);
x_28 = lean_ctor_get(x_6, 3);
x_29 = lean_ctor_get(x_6, 4);
x_30 = lean_ctor_get(x_6, 5);
x_31 = lean_ctor_get(x_6, 6);
x_32 = lean_ctor_get(x_6, 7);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_28, x_33);
x_35 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_26);
lean_ctor_set(x_35, 2, x_27);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_35, 4, x_29);
lean_ctor_set(x_35, 5, x_30);
lean_ctor_set(x_35, 6, x_31);
lean_ctor_set(x_35, 7, x_32);
x_36 = lean_st_ref_set(x_3, x_35, x_7);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 4);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 6);
lean_inc(x_43);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_44 = x_2;
} else {
 lean_dec_ref(x_2);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 7, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_39);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set(x_45, 3, x_41);
lean_ctor_set(x_45, 4, x_42);
lean_ctor_set(x_45, 5, x_28);
lean_ctor_set(x_45, 6, x_43);
x_46 = lean_apply_3(x_1, x_45, x_3, x_37);
return x_46;
}
}
}
lean_object* l_Lean_Elab_Command_withFreshMacroScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withFreshMacroScope___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_instMonadQuotationCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_take(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_10, x_11);
lean_ctor_set(x_7, 3, x_12);
x_13 = lean_st_ref_set(x_4, x_7, x_8);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_3, 5);
lean_dec(x_16);
lean_ctor_set(x_3, 5, x_10);
x_17 = lean_apply_3(x_2, x_3, x_4, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
x_23 = lean_ctor_get(x_3, 6);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_24 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_10);
lean_ctor_set(x_24, 6, x_23);
x_25 = lean_apply_3(x_2, x_24, x_4, x_14);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
x_28 = lean_ctor_get(x_7, 2);
x_29 = lean_ctor_get(x_7, 3);
x_30 = lean_ctor_get(x_7, 4);
x_31 = lean_ctor_get(x_7, 5);
x_32 = lean_ctor_get(x_7, 6);
x_33 = lean_ctor_get(x_7, 7);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_29, x_34);
x_36 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_27);
lean_ctor_set(x_36, 2, x_28);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_36, 4, x_30);
lean_ctor_set(x_36, 5, x_31);
lean_ctor_set(x_36, 6, x_32);
lean_ctor_set(x_36, 7, x_33);
x_37 = lean_st_ref_set(x_4, x_36, x_8);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_3, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_3, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 4);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 6);
lean_inc(x_44);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 x_45 = x_3;
} else {
 lean_dec_ref(x_3);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 7, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_40);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_42);
lean_ctor_set(x_46, 4, x_43);
lean_ctor_set(x_46, 5, x_29);
lean_ctor_set(x_46, 6, x_44);
x_47 = lean_apply_3(x_2, x_46, x_4, x_38);
return x_47;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getCurrMacroScope___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getMainModule___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadQuotationCommandElabM___lambda__1), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_instMonadRefCommandElabM;
x_2 = l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__1;
x_3 = l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__2;
x_4 = l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_mkMacroAttributeUnsafe___closed__2;
x_2 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1128____closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("commandElabAttribute");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1;
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinCommandElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("commandElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CommandElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1;
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_mkCommandElabAttributeUnsafe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__3;
x_3 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__5;
x_4 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__7;
x_5 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1128____closed__3;
x_6 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__9;
x_7 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3997____closed__3;
x_8 = l_Lean_Elab_mkElabAttribute___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_mkCommandElabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_instInhabitedError___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1050_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_mkCommandElabAttributeUnsafe(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = l_Lean_indentD(x_7);
x_9 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabUsingElabFnsAux___closed__2;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_KernelException_toMessageData___closed__15;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_12, x_4, x_5, x_6);
lean_dec(x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_16 = lean_apply_4(x_14, x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_16, 1);
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
x_26 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_27 = lean_nat_dec_eq(x_26, x_25);
lean_dec(x_25);
if (x_27 == 0)
{
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_16);
lean_dec(x_17);
lean_inc(x_1);
x_28 = lean_st_ref_set(x_5, x_1, x_23);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_3 = x_15;
x_6 = x_29;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
x_33 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_34 = lean_nat_dec_eq(x_33, x_32);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_17);
lean_inc(x_1);
x_36 = lean_st_ref_set(x_5, x_1, x_31);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_3 = x_15;
x_6 = x_37;
goto _start;
}
}
}
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_withMacroExpansion___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_4, 4, x_10);
x_11 = lean_apply_3(x_3, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_ctor_get(x_4, 3);
x_16 = lean_ctor_get(x_4, 4);
x_17 = lean_ctor_get(x_4, 5);
x_18 = lean_ctor_get(x_4, 6);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_14);
lean_ctor_set(x_21, 3, x_15);
lean_ctor_set(x_21, 4, x_20);
lean_ctor_set(x_21, 5, x_17);
lean_ctor_set(x_21, 6, x_18);
x_22 = lean_apply_3(x_3, x_21, x_5, x_6);
return x_22;
}
}
}
lean_object* l_Lean_Elab_Command_withMacroExpansion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withMacroExpansion___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 3);
lean_dec(x_9);
lean_ctor_set(x_6, 3, x_1);
x_10 = lean_st_ref_set(x_3, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 2);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 5);
x_22 = lean_ctor_get(x_6, 6);
x_23 = lean_ctor_get(x_6, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_1);
lean_ctor_set(x_24, 4, x_20);
lean_ctor_set(x_24, 5, x_21);
lean_ctor_set(x_24, 6, x_22);
lean_ctor_set(x_24, 7, x_23);
x_25 = lean_st_ref_set(x_3, x_24, x_7);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadEnvCoreM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_instMonadInfoTreeCommandElabM___spec__1___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__2;
x_3 = l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__4;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 2);
lean_dec(x_8);
lean_ctor_set(x_4, 2, x_2);
x_9 = lean_apply_3(x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 3);
x_13 = lean_ctor_get(x_4, 4);
x_14 = lean_ctor_get(x_4, 5);
x_15 = lean_ctor_get(x_4, 6);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_2);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_13);
lean_ctor_set(x_16, 5, x_14);
lean_ctor_set(x_16, 6, x_15);
x_17 = lean_apply_3(x_3, x_16, x_5, x_6);
return x_17;
}
}
}
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_instMonadLogCommandElabM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_instMonadInfoTreeCommandElabM___spec__1___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__3___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadEnvCoreM___closed__1;
x_2 = l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__3;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Command_instMonadInfoTreeCommandElabM___spec__1___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__1), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__5;
x_2 = l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__2;
x_3 = l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__6;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instMonadRecDepthCommandElabM___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_withLogging_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Elab_Command_withLogging_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withLogging_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_331; uint8_t x_332; 
x_331 = 2;
x_332 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_99_(x_3, x_331);
if (x_332 == 0)
{
lean_object* x_333; 
x_333 = lean_box(0);
x_7 = x_333;
goto block_330;
}
else
{
uint8_t x_334; 
x_334 = l_Lean_MessageData_hasSyntheticSorry(x_2);
if (x_334 == 0)
{
lean_object* x_335; 
x_335 = lean_box(0);
x_7 = x_335;
goto block_330;
}
else
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_2);
x_336 = lean_box(0);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_6);
return x_337;
}
}
block_330:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
x_8 = l_Lean_Elab_Command_getRef(x_4, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_replaceRef(x_1, x_9);
lean_dec(x_9);
x_12 = l_Lean_Syntax_getPos(x_11);
x_13 = l_Lean_Syntax_getTailPos(x_11);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_FileMap_toPosition(x_15, x_19);
lean_inc(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Elab_Command_getScope___rarg(x_5, x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 2);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Command_getScope___rarg(x_5, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 3);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_17);
x_32 = l_Lean_instInhabitedParserDescr___closed__1;
lean_inc(x_14);
x_33 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_20);
lean_ctor_set(x_33, 2, x_21);
lean_ctor_set(x_33, 3, x_32);
lean_ctor_set(x_33, 4, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*5, x_3);
x_34 = lean_st_ref_take(x_5, x_28);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_35, 1);
x_39 = l_Std_PersistentArray_push___rarg(x_38, x_33);
lean_ctor_set(x_35, 1, x_39);
x_40 = lean_st_ref_set(x_5, x_35, x_36);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_47 = lean_ctor_get(x_35, 0);
x_48 = lean_ctor_get(x_35, 1);
x_49 = lean_ctor_get(x_35, 2);
x_50 = lean_ctor_get(x_35, 3);
x_51 = lean_ctor_get(x_35, 4);
x_52 = lean_ctor_get(x_35, 5);
x_53 = lean_ctor_get(x_35, 6);
x_54 = lean_ctor_get(x_35, 7);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_35);
x_55 = l_Std_PersistentArray_push___rarg(x_48, x_33);
x_56 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_49);
lean_ctor_set(x_56, 3, x_50);
lean_ctor_set(x_56, 4, x_51);
lean_ctor_set(x_56, 5, x_52);
lean_ctor_set(x_56, 6, x_53);
lean_ctor_set(x_56, 7, x_54);
x_57 = lean_st_ref_set(x_5, x_56, x_36);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_13);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_63 = lean_ctor_get(x_13, 0);
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get(x_4, 1);
x_66 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unsigned_to_nat(0u);
x_70 = l_Lean_FileMap_toPosition(x_65, x_69);
x_71 = l_Lean_FileMap_toPosition(x_65, x_63);
lean_ctor_set(x_13, 0, x_71);
x_72 = l_Lean_Elab_Command_getScope___rarg(x_5, x_68);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 2);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Elab_Command_getScope___rarg(x_5, x_74);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 3);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_67);
x_82 = l_Lean_instInhabitedParserDescr___closed__1;
lean_inc(x_64);
x_83 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_83, 0, x_64);
lean_ctor_set(x_83, 1, x_70);
lean_ctor_set(x_83, 2, x_13);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set(x_83, 4, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*5, x_3);
x_84 = lean_st_ref_take(x_5, x_78);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_85, 1);
x_89 = l_Std_PersistentArray_push___rarg(x_88, x_83);
lean_ctor_set(x_85, 1, x_89);
x_90 = lean_st_ref_set(x_5, x_85, x_86);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
x_93 = lean_box(0);
lean_ctor_set(x_90, 0, x_93);
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_97 = lean_ctor_get(x_85, 0);
x_98 = lean_ctor_get(x_85, 1);
x_99 = lean_ctor_get(x_85, 2);
x_100 = lean_ctor_get(x_85, 3);
x_101 = lean_ctor_get(x_85, 4);
x_102 = lean_ctor_get(x_85, 5);
x_103 = lean_ctor_get(x_85, 6);
x_104 = lean_ctor_get(x_85, 7);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_85);
x_105 = l_Std_PersistentArray_push___rarg(x_98, x_83);
x_106 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_106, 0, x_97);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_99);
lean_ctor_set(x_106, 3, x_100);
lean_ctor_set(x_106, 4, x_101);
lean_ctor_set(x_106, 5, x_102);
lean_ctor_set(x_106, 6, x_103);
lean_ctor_set(x_106, 7, x_104);
x_107 = lean_st_ref_set(x_5, x_106, x_86);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_112 = lean_ctor_get(x_13, 0);
lean_inc(x_112);
lean_dec(x_13);
x_113 = lean_ctor_get(x_4, 0);
x_114 = lean_ctor_get(x_4, 1);
x_115 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_unsigned_to_nat(0u);
x_119 = l_Lean_FileMap_toPosition(x_114, x_118);
x_120 = l_Lean_FileMap_toPosition(x_114, x_112);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = l_Lean_Elab_Command_getScope___rarg(x_5, x_117);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get(x_123, 2);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l_Lean_Elab_Command_getScope___rarg(x_5, x_124);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 3);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_125);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_116);
x_132 = l_Lean_instInhabitedParserDescr___closed__1;
lean_inc(x_113);
x_133 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_133, 0, x_113);
lean_ctor_set(x_133, 1, x_119);
lean_ctor_set(x_133, 2, x_121);
lean_ctor_set(x_133, 3, x_132);
lean_ctor_set(x_133, 4, x_131);
lean_ctor_set_uint8(x_133, sizeof(void*)*5, x_3);
x_134 = lean_st_ref_take(x_5, x_128);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_135, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_135, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 4);
lean_inc(x_141);
x_142 = lean_ctor_get(x_135, 5);
lean_inc(x_142);
x_143 = lean_ctor_get(x_135, 6);
lean_inc(x_143);
x_144 = lean_ctor_get(x_135, 7);
lean_inc(x_144);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 lean_ctor_release(x_135, 5);
 lean_ctor_release(x_135, 6);
 lean_ctor_release(x_135, 7);
 x_145 = x_135;
} else {
 lean_dec_ref(x_135);
 x_145 = lean_box(0);
}
x_146 = l_Std_PersistentArray_push___rarg(x_138, x_133);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 8, 0);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_137);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_139);
lean_ctor_set(x_147, 3, x_140);
lean_ctor_set(x_147, 4, x_141);
lean_ctor_set(x_147, 5, x_142);
lean_ctor_set(x_147, 6, x_143);
lean_ctor_set(x_147, 7, x_144);
x_148 = lean_st_ref_set(x_5, x_147, x_136);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
x_151 = lean_box(0);
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_150;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_149);
return x_152;
}
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_12);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_154 = lean_ctor_get(x_12, 0);
x_155 = lean_ctor_get(x_4, 0);
x_156 = lean_ctor_get(x_4, 1);
x_157 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Lean_FileMap_toPosition(x_156, x_154);
lean_inc(x_160);
lean_ctor_set(x_12, 0, x_160);
x_161 = l_Lean_Elab_Command_getScope___rarg(x_5, x_159);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get(x_162, 2);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_Lean_Elab_Command_getScope___rarg(x_5, x_163);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_ctor_get(x_166, 3);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_164);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_158);
x_171 = l_Lean_instInhabitedParserDescr___closed__1;
lean_inc(x_155);
x_172 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_172, 0, x_155);
lean_ctor_set(x_172, 1, x_160);
lean_ctor_set(x_172, 2, x_12);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set(x_172, 4, x_170);
lean_ctor_set_uint8(x_172, sizeof(void*)*5, x_3);
x_173 = lean_st_ref_take(x_5, x_167);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = !lean_is_exclusive(x_174);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_177 = lean_ctor_get(x_174, 1);
x_178 = l_Std_PersistentArray_push___rarg(x_177, x_172);
lean_ctor_set(x_174, 1, x_178);
x_179 = lean_st_ref_set(x_5, x_174, x_175);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_179, 0);
lean_dec(x_181);
x_182 = lean_box(0);
lean_ctor_set(x_179, 0, x_182);
return x_179;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_179, 1);
lean_inc(x_183);
lean_dec(x_179);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_186 = lean_ctor_get(x_174, 0);
x_187 = lean_ctor_get(x_174, 1);
x_188 = lean_ctor_get(x_174, 2);
x_189 = lean_ctor_get(x_174, 3);
x_190 = lean_ctor_get(x_174, 4);
x_191 = lean_ctor_get(x_174, 5);
x_192 = lean_ctor_get(x_174, 6);
x_193 = lean_ctor_get(x_174, 7);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_174);
x_194 = l_Std_PersistentArray_push___rarg(x_187, x_172);
x_195 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_195, 0, x_186);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_195, 2, x_188);
lean_ctor_set(x_195, 3, x_189);
lean_ctor_set(x_195, 4, x_190);
lean_ctor_set(x_195, 5, x_191);
lean_ctor_set(x_195, 6, x_192);
lean_ctor_set(x_195, 7, x_193);
x_196 = lean_st_ref_set(x_5, x_195, x_175);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
x_199 = lean_box(0);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_197);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_201 = lean_ctor_get(x_12, 0);
lean_inc(x_201);
lean_dec(x_12);
x_202 = lean_ctor_get(x_4, 0);
x_203 = lean_ctor_get(x_4, 1);
x_204 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = l_Lean_FileMap_toPosition(x_203, x_201);
lean_inc(x_207);
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_207);
x_209 = l_Lean_Elab_Command_getScope___rarg(x_5, x_206);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_ctor_get(x_210, 2);
lean_inc(x_212);
lean_dec(x_210);
x_213 = l_Lean_Elab_Command_getScope___rarg(x_5, x_211);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_ctor_get(x_214, 3);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_212);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_205);
x_219 = l_Lean_instInhabitedParserDescr___closed__1;
lean_inc(x_202);
x_220 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_220, 0, x_202);
lean_ctor_set(x_220, 1, x_207);
lean_ctor_set(x_220, 2, x_208);
lean_ctor_set(x_220, 3, x_219);
lean_ctor_set(x_220, 4, x_218);
lean_ctor_set_uint8(x_220, sizeof(void*)*5, x_3);
x_221 = lean_st_ref_take(x_5, x_215);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_222, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_222, 3);
lean_inc(x_227);
x_228 = lean_ctor_get(x_222, 4);
lean_inc(x_228);
x_229 = lean_ctor_get(x_222, 5);
lean_inc(x_229);
x_230 = lean_ctor_get(x_222, 6);
lean_inc(x_230);
x_231 = lean_ctor_get(x_222, 7);
lean_inc(x_231);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 lean_ctor_release(x_222, 2);
 lean_ctor_release(x_222, 3);
 lean_ctor_release(x_222, 4);
 lean_ctor_release(x_222, 5);
 lean_ctor_release(x_222, 6);
 lean_ctor_release(x_222, 7);
 x_232 = x_222;
} else {
 lean_dec_ref(x_222);
 x_232 = lean_box(0);
}
x_233 = l_Std_PersistentArray_push___rarg(x_225, x_220);
if (lean_is_scalar(x_232)) {
 x_234 = lean_alloc_ctor(0, 8, 0);
} else {
 x_234 = x_232;
}
lean_ctor_set(x_234, 0, x_224);
lean_ctor_set(x_234, 1, x_233);
lean_ctor_set(x_234, 2, x_226);
lean_ctor_set(x_234, 3, x_227);
lean_ctor_set(x_234, 4, x_228);
lean_ctor_set(x_234, 5, x_229);
lean_ctor_set(x_234, 6, x_230);
lean_ctor_set(x_234, 7, x_231);
x_235 = lean_st_ref_set(x_5, x_234, x_223);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_237 = x_235;
} else {
 lean_dec_ref(x_235);
 x_237 = lean_box(0);
}
x_238 = lean_box(0);
if (lean_is_scalar(x_237)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_237;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_236);
return x_239;
}
}
else
{
lean_object* x_240; uint8_t x_241; 
x_240 = lean_ctor_get(x_12, 0);
lean_inc(x_240);
lean_dec(x_12);
x_241 = !lean_is_exclusive(x_13);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_242 = lean_ctor_get(x_13, 0);
x_243 = lean_ctor_get(x_4, 0);
x_244 = lean_ctor_get(x_4, 1);
x_245 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = l_Lean_FileMap_toPosition(x_244, x_240);
x_249 = l_Lean_FileMap_toPosition(x_244, x_242);
lean_ctor_set(x_13, 0, x_249);
x_250 = l_Lean_Elab_Command_getScope___rarg(x_5, x_247);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_ctor_get(x_251, 2);
lean_inc(x_253);
lean_dec(x_251);
x_254 = l_Lean_Elab_Command_getScope___rarg(x_5, x_252);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_ctor_get(x_255, 3);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_253);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_246);
x_260 = l_Lean_instInhabitedParserDescr___closed__1;
lean_inc(x_243);
x_261 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_261, 0, x_243);
lean_ctor_set(x_261, 1, x_248);
lean_ctor_set(x_261, 2, x_13);
lean_ctor_set(x_261, 3, x_260);
lean_ctor_set(x_261, 4, x_259);
lean_ctor_set_uint8(x_261, sizeof(void*)*5, x_3);
x_262 = lean_st_ref_take(x_5, x_256);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = !lean_is_exclusive(x_263);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_266 = lean_ctor_get(x_263, 1);
x_267 = l_Std_PersistentArray_push___rarg(x_266, x_261);
lean_ctor_set(x_263, 1, x_267);
x_268 = lean_st_ref_set(x_5, x_263, x_264);
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_268, 0);
lean_dec(x_270);
x_271 = lean_box(0);
lean_ctor_set(x_268, 0, x_271);
return x_268;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_268, 1);
lean_inc(x_272);
lean_dec(x_268);
x_273 = lean_box(0);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_275 = lean_ctor_get(x_263, 0);
x_276 = lean_ctor_get(x_263, 1);
x_277 = lean_ctor_get(x_263, 2);
x_278 = lean_ctor_get(x_263, 3);
x_279 = lean_ctor_get(x_263, 4);
x_280 = lean_ctor_get(x_263, 5);
x_281 = lean_ctor_get(x_263, 6);
x_282 = lean_ctor_get(x_263, 7);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_263);
x_283 = l_Std_PersistentArray_push___rarg(x_276, x_261);
x_284 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_284, 0, x_275);
lean_ctor_set(x_284, 1, x_283);
lean_ctor_set(x_284, 2, x_277);
lean_ctor_set(x_284, 3, x_278);
lean_ctor_set(x_284, 4, x_279);
lean_ctor_set(x_284, 5, x_280);
lean_ctor_set(x_284, 6, x_281);
lean_ctor_set(x_284, 7, x_282);
x_285 = lean_st_ref_set(x_5, x_284, x_264);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_287 = x_285;
} else {
 lean_dec_ref(x_285);
 x_287 = lean_box(0);
}
x_288 = lean_box(0);
if (lean_is_scalar(x_287)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_287;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_286);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_290 = lean_ctor_get(x_13, 0);
lean_inc(x_290);
lean_dec(x_13);
x_291 = lean_ctor_get(x_4, 0);
x_292 = lean_ctor_get(x_4, 1);
x_293 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_2, x_4, x_5, x_10);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
x_296 = l_Lean_FileMap_toPosition(x_292, x_240);
x_297 = l_Lean_FileMap_toPosition(x_292, x_290);
x_298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_298, 0, x_297);
x_299 = l_Lean_Elab_Command_getScope___rarg(x_5, x_295);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_ctor_get(x_300, 2);
lean_inc(x_302);
lean_dec(x_300);
x_303 = l_Lean_Elab_Command_getScope___rarg(x_5, x_301);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = lean_ctor_get(x_304, 3);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_302);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_294);
x_309 = l_Lean_instInhabitedParserDescr___closed__1;
lean_inc(x_291);
x_310 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_310, 0, x_291);
lean_ctor_set(x_310, 1, x_296);
lean_ctor_set(x_310, 2, x_298);
lean_ctor_set(x_310, 3, x_309);
lean_ctor_set(x_310, 4, x_308);
lean_ctor_set_uint8(x_310, sizeof(void*)*5, x_3);
x_311 = lean_st_ref_take(x_5, x_305);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_314 = lean_ctor_get(x_312, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_312, 1);
lean_inc(x_315);
x_316 = lean_ctor_get(x_312, 2);
lean_inc(x_316);
x_317 = lean_ctor_get(x_312, 3);
lean_inc(x_317);
x_318 = lean_ctor_get(x_312, 4);
lean_inc(x_318);
x_319 = lean_ctor_get(x_312, 5);
lean_inc(x_319);
x_320 = lean_ctor_get(x_312, 6);
lean_inc(x_320);
x_321 = lean_ctor_get(x_312, 7);
lean_inc(x_321);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 lean_ctor_release(x_312, 2);
 lean_ctor_release(x_312, 3);
 lean_ctor_release(x_312, 4);
 lean_ctor_release(x_312, 5);
 lean_ctor_release(x_312, 6);
 lean_ctor_release(x_312, 7);
 x_322 = x_312;
} else {
 lean_dec_ref(x_312);
 x_322 = lean_box(0);
}
x_323 = l_Std_PersistentArray_push___rarg(x_315, x_310);
if (lean_is_scalar(x_322)) {
 x_324 = lean_alloc_ctor(0, 8, 0);
} else {
 x_324 = x_322;
}
lean_ctor_set(x_324, 0, x_314);
lean_ctor_set(x_324, 1, x_323);
lean_ctor_set(x_324, 2, x_316);
lean_ctor_set(x_324, 3, x_317);
lean_ctor_set(x_324, 4, x_318);
lean_ctor_set(x_324, 5, x_319);
lean_ctor_set(x_324, 6, x_320);
lean_ctor_set(x_324, 7, x_321);
x_325 = lean_st_ref_set(x_5, x_324, x_313);
x_326 = lean_ctor_get(x_325, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_327 = x_325;
} else {
 lean_dec_ref(x_325);
 x_327 = lean_box(0);
}
x_328 = lean_box(0);
if (lean_is_scalar(x_327)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_327;
}
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_326);
return x_329;
}
}
}
}
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2(x_7, x_1, x_2, x_3, x_4, x_8);
lean_dec(x_7);
return x_9;
}
}
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = 2;
x_8 = l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2(x_5, x_6, x_7, x_2, x_3, x_4);
lean_dec(x_5);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = l_Lean_Elab_isAbortExceptionId(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_InternalExceptionId_getName(x_10, x_4);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_free_object(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = l_Lean_Elab_logException___rarg___lambda__1___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_KernelException_toMessageData___closed__15;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = 2;
x_22 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_20, x_21, x_2, x_3, x_15);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_2, 6);
x_26 = lean_io_error_to_string(x_24);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_inc(x_25);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_28);
lean_ctor_set(x_1, 0, x_25);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_ctor_get(x_2, 6);
x_32 = lean_io_error_to_string(x_29);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_inc(x_31);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_1);
lean_dec(x_10);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_4);
return x_37;
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = l_Lean_Elab_isAbortExceptionId(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Lean_InternalExceptionId_getName(x_38, x_4);
lean_dec(x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_43, 0, x_41);
x_44 = l_Lean_Elab_logException___rarg___lambda__1___closed__2;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_KernelException_toMessageData___closed__15;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = 2;
x_49 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_47, x_48, x_2, x_3, x_42);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_40, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_52 = x_40;
} else {
 lean_dec_ref(x_40);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_2, 6);
x_54 = lean_io_error_to_string(x_50);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_inc(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_52)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_52;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_51);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_38);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_4);
return x_60;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_withLogging___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("internal exception ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_withLogging___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_withLogging___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_withLogging(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1(x_6, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_5, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_dec(x_14);
x_15 = l_Lean_Elab_isAbortExceptionId(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_free_object(x_5);
x_16 = l_Lean_InternalExceptionId_getName(x_13, x_10);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
lean_free_object(x_6);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = l_Lean_Elab_Command_withLogging___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_KernelException_toMessageData___closed__15;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = 2;
x_25 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_23, x_24, x_2, x_3, x_18);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_2, 6);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_io_error_to_string(x_27);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_31);
lean_ctor_set(x_6, 0, x_28);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_ctor_get(x_2, 6);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_io_error_to_string(x_32);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_37);
lean_ctor_set(x_6, 0, x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
else
{
lean_object* x_39; 
lean_free_object(x_6);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_box(0);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_39);
return x_5;
}
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_6, 0);
lean_inc(x_40);
lean_dec(x_6);
x_41 = l_Lean_Elab_isAbortExceptionId(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_free_object(x_5);
x_42 = l_Lean_InternalExceptionId_getName(x_40, x_10);
lean_dec(x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_43);
x_46 = l_Lean_Elab_Command_withLogging___closed__2;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_KernelException_toMessageData___closed__15;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = 2;
x_51 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_49, x_50, x_2, x_3, x_44);
lean_dec(x_3);
lean_dec(x_2);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_3);
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_54 = x_42;
} else {
 lean_dec_ref(x_42);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_2, 6);
lean_inc(x_55);
lean_dec(x_2);
x_56 = lean_io_error_to_string(x_52);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_54;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_53);
return x_60;
}
}
else
{
lean_object* x_61; 
lean_dec(x_40);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_box(0);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_61);
return x_5;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_5, 1);
lean_inc(x_62);
lean_dec(x_5);
x_63 = lean_ctor_get(x_6, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_64 = x_6;
} else {
 lean_dec_ref(x_6);
 x_64 = lean_box(0);
}
x_65 = l_Lean_Elab_isAbortExceptionId(x_63);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = l_Lean_InternalExceptionId_getName(x_63, x_62);
lean_dec(x_63);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
lean_dec(x_64);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_69, 0, x_67);
x_70 = l_Lean_Elab_Command_withLogging___closed__2;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_KernelException_toMessageData___closed__15;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = 2;
x_75 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_73, x_74, x_2, x_3, x_68);
lean_dec(x_3);
lean_dec(x_2);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_3);
x_76 = lean_ctor_get(x_66, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_66, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_2, 6);
lean_inc(x_79);
lean_dec(x_2);
x_80 = lean_io_error_to_string(x_76);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
if (lean_is_scalar(x_64)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_64;
 lean_ctor_set_tag(x_83, 0);
}
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
if (lean_is_scalar(x_78)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_78;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_77);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_3);
lean_dec(x_2);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_62);
return x_86;
}
}
}
}
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1345____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1080____closed__1;
x_2 = l_Lean_Parser_initFn____x40_Lean_Parser_Extension___hyg_3997____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1345_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1345____closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabCommand_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_elabCommand_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabCommand_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_elabCommand_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabCommand_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Command_elabCommand_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCommand_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_Command_elabCommand___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_Command_elabCommand___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_Command_elabCommand___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Elab_Command_elabCommand___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(x_4, x_2);
lean_dec(x_4);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(x_11, x_2);
lean_dec(x_11);
return x_12;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__8(x_2, x_3, x_4, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_19 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_18);
lean_ctor_set(x_19, 6, x_9);
x_20 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__8(x_2, x_19, x_4, x_8);
return x_20;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
x_7 = 0;
x_8 = l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_2 == x_3;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_array_uget(x_1, x_2);
lean_inc(x_6);
x_10 = l_Lean_Elab_Command_elabCommand(x_9, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = x_2 + x_13;
x_2 = x_14;
x_4 = x_11;
x_7 = x_12;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
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
else
{
lean_object* x_20; 
lean_dec(x_6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
lean_object* l_Lean_Elab_Command_elabCommand___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 3);
x_13 = lean_ctor_get(x_4, 4);
x_14 = lean_ctor_get(x_4, 6);
x_15 = lean_ctor_get(x_4, 5);
lean_dec(x_15);
x_16 = lean_ctor_get(x_4, 2);
lean_dec(x_16);
x_17 = lean_st_ref_take(x_5, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_118; 
x_21 = lean_ctor_get(x_18, 3);
x_22 = lean_nat_add(x_21, x_7);
lean_ctor_set(x_18, 3, x_22);
x_23 = lean_st_ref_set(x_5, x_18, x_19);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_14);
lean_inc(x_21);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_8);
lean_inc(x_11);
lean_inc(x_10);
lean_ctor_set(x_4, 5, x_21);
lean_ctor_set(x_4, 2, x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_118 = l_Lean_Elab_Command_runLinters(x_2, x_4, x_5, x_24);
if (lean_obj_tag(x_118) == 0)
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_120 = lean_ctor_get(x_118, 1);
x_121 = lean_ctor_get(x_118, 0);
lean_dec(x_121);
x_122 = lean_ctor_get(x_2, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_2, 1);
lean_inc(x_123);
x_124 = l_Lean_nullKind;
x_125 = lean_name_eq(x_122, x_124);
lean_dec(x_122);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_123);
lean_free_object(x_118);
x_126 = lean_st_ref_get(x_5, x_120);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 2);
lean_inc(x_129);
lean_dec(x_127);
x_130 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_129);
lean_dec(x_129);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1345____closed__1;
x_133 = l_Lean_checkTraceOption(x_131, x_132);
lean_dec(x_131);
if (x_133 == 0)
{
x_25 = x_128;
goto block_117;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_inc(x_2);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_2);
x_135 = l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10(x_132, x_134, x_4, x_5, x_128);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_25 = x_136;
goto block_117;
}
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_137 = lean_array_get_size(x_123);
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_nat_dec_lt(x_138, x_137);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_137);
lean_dec(x_123);
lean_dec(x_4);
lean_dec(x_5);
x_140 = lean_box(0);
lean_ctor_set(x_118, 0, x_140);
return x_118;
}
else
{
uint8_t x_141; 
x_141 = lean_nat_dec_le(x_137, x_137);
if (x_141 == 0)
{
lean_object* x_142; 
lean_dec(x_137);
lean_dec(x_123);
lean_dec(x_4);
lean_dec(x_5);
x_142 = lean_box(0);
lean_ctor_set(x_118, 0, x_142);
return x_118;
}
else
{
size_t x_143; size_t x_144; lean_object* x_145; lean_object* x_146; 
lean_free_object(x_118);
x_143 = 0;
x_144 = lean_usize_of_nat(x_137);
lean_dec(x_137);
x_145 = lean_box(0);
x_146 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__11(x_123, x_143, x_144, x_145, x_4, x_5, x_120);
lean_dec(x_4);
lean_dec(x_123);
return x_146;
}
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_147 = lean_ctor_get(x_118, 1);
lean_inc(x_147);
lean_dec(x_118);
x_148 = lean_ctor_get(x_2, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_2, 1);
lean_inc(x_149);
x_150 = l_Lean_nullKind;
x_151 = lean_name_eq(x_148, x_150);
lean_dec(x_148);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
lean_dec(x_149);
x_152 = lean_st_ref_get(x_5, x_147);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_ctor_get(x_153, 2);
lean_inc(x_155);
lean_dec(x_153);
x_156 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_155);
lean_dec(x_155);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_158 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1345____closed__1;
x_159 = l_Lean_checkTraceOption(x_157, x_158);
lean_dec(x_157);
if (x_159 == 0)
{
x_25 = x_154;
goto block_117;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_inc(x_2);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_2);
x_161 = l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10(x_158, x_160, x_4, x_5, x_154);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_25 = x_162;
goto block_117;
}
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_163 = lean_array_get_size(x_149);
x_164 = lean_unsigned_to_nat(0u);
x_165 = lean_nat_dec_lt(x_164, x_163);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_163);
lean_dec(x_149);
lean_dec(x_4);
lean_dec(x_5);
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_147);
return x_167;
}
else
{
uint8_t x_168; 
x_168 = lean_nat_dec_le(x_163, x_163);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_163);
lean_dec(x_149);
lean_dec(x_4);
lean_dec(x_5);
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_147);
return x_170;
}
else
{
size_t x_171; size_t x_172; lean_object* x_173; lean_object* x_174; 
x_171 = 0;
x_172 = lean_usize_of_nat(x_163);
lean_dec(x_163);
x_173 = lean_box(0);
x_174 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__11(x_149, x_171, x_172, x_173, x_4, x_5, x_147);
lean_dec(x_4);
lean_dec(x_149);
return x_174;
}
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_175 = lean_ctor_get(x_118, 1);
lean_inc(x_175);
lean_dec(x_118);
x_176 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__3;
x_177 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_176, x_4, x_5, x_175);
lean_dec(x_5);
return x_177;
}
}
else
{
uint8_t x_178; 
lean_dec(x_4);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_178 = !lean_is_exclusive(x_118);
if (x_178 == 0)
{
return x_118;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_118, 0);
x_180 = lean_ctor_get(x_118, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_118);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
block_117:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_53; lean_object* x_54; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_26 = lean_st_ref_get(x_5, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
x_62 = lean_st_ref_get(x_5, x_28);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Elab_Command_getRef(x_4, x_5, x_64);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Elab_Command_getCurrMacroScope(x_4, x_5, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_st_ref_get(x_5, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 4);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_st_ref_get(x_5, x_74);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 3);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_65);
x_80 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_80, 0, x_65);
x_81 = x_80;
x_82 = lean_environment_main_module(x_65);
lean_inc(x_8);
x_83 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_70);
lean_ctor_set(x_83, 3, x_8);
lean_ctor_set(x_83, 4, x_75);
lean_ctor_set(x_83, 5, x_67);
lean_inc(x_2);
x_84 = l_Lean_Elab_getMacros(x_30, x_2, x_83, x_79);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_29);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_st_ref_take(x_5, x_78);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = !lean_is_exclusive(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_88, 3);
lean_dec(x_91);
lean_ctor_set(x_88, 3, x_86);
x_92 = lean_st_ref_set(x_5, x_88, x_89);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_85);
x_31 = x_94;
x_32 = x_93;
goto block_52;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_95 = lean_ctor_get(x_88, 0);
x_96 = lean_ctor_get(x_88, 1);
x_97 = lean_ctor_get(x_88, 2);
x_98 = lean_ctor_get(x_88, 4);
x_99 = lean_ctor_get(x_88, 5);
x_100 = lean_ctor_get(x_88, 6);
x_101 = lean_ctor_get(x_88, 7);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_88);
x_102 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_102, 0, x_95);
lean_ctor_set(x_102, 1, x_96);
lean_ctor_set(x_102, 2, x_97);
lean_ctor_set(x_102, 3, x_86);
lean_ctor_set(x_102, 4, x_98);
lean_ctor_set(x_102, 5, x_99);
lean_ctor_set(x_102, 6, x_100);
lean_ctor_set(x_102, 7, x_101);
x_103 = lean_st_ref_set(x_5, x_102, x_89);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_85);
x_31 = x_105;
x_32 = x_104;
goto block_52;
}
}
else
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_84, 0);
lean_inc(x_106);
lean_dec(x_84);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_109);
lean_inc(x_4);
x_111 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__7(x_107, x_110, x_4, x_5, x_78);
lean_dec(x_107);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_53 = x_112;
x_54 = x_113;
goto block_61;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg(x_78);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_53 = x_115;
x_54 = x_116;
goto block_61;
}
}
block_52:
{
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_33 = l_Lean_Elab_Command_commandElabAttribute;
x_34 = lean_ctor_get(x_33, 2);
lean_inc(x_34);
x_35 = l_Lean_PersistentEnvExtension_getState___rarg(x_34, x_30);
lean_dec(x_30);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_2);
x_37 = l_Lean_Syntax_getKind(x_2);
x_38 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1(x_36, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_27);
lean_dec(x_2);
x_39 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabUsingElabFns___closed__2;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabUsingElabFns___closed__4;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_43, x_4, x_5, x_32);
lean_dec(x_5);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_37);
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
lean_dec(x_38);
x_46 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing(x_27, x_2, x_45, x_4, x_5, x_32);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_4);
x_47 = lean_ctor_get(x_31, 0);
lean_inc(x_47);
lean_dec(x_31);
lean_inc(x_47);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_2);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_13);
x_50 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_50, 0, x_10);
lean_ctor_set(x_50, 1, x_11);
lean_ctor_set(x_50, 2, x_8);
lean_ctor_set(x_50, 3, x_12);
lean_ctor_set(x_50, 4, x_49);
lean_ctor_set(x_50, 5, x_21);
lean_ctor_set(x_50, 6, x_14);
x_51 = l_Lean_Elab_Command_elabCommand(x_47, x_50, x_5, x_32);
lean_dec(x_50);
return x_51;
}
}
block_61:
{
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_55; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_4);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_29)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_29;
 lean_ctor_set_tag(x_55, 1);
}
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
x_57 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_58 = lean_nat_dec_eq(x_57, x_56);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_4);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_29)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_29;
 lean_ctor_set_tag(x_59, 1);
}
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
else
{
lean_object* x_60; 
lean_dec(x_53);
lean_dec(x_29);
x_60 = lean_box(0);
x_31 = x_60;
x_32 = x_54;
goto block_52;
}
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_283; 
x_182 = lean_ctor_get(x_18, 0);
x_183 = lean_ctor_get(x_18, 1);
x_184 = lean_ctor_get(x_18, 2);
x_185 = lean_ctor_get(x_18, 3);
x_186 = lean_ctor_get(x_18, 4);
x_187 = lean_ctor_get(x_18, 5);
x_188 = lean_ctor_get(x_18, 6);
x_189 = lean_ctor_get(x_18, 7);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_18);
x_190 = lean_nat_add(x_185, x_7);
x_191 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_191, 0, x_182);
lean_ctor_set(x_191, 1, x_183);
lean_ctor_set(x_191, 2, x_184);
lean_ctor_set(x_191, 3, x_190);
lean_ctor_set(x_191, 4, x_186);
lean_ctor_set(x_191, 5, x_187);
lean_ctor_set(x_191, 6, x_188);
lean_ctor_set(x_191, 7, x_189);
x_192 = lean_st_ref_set(x_5, x_191, x_19);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
lean_inc(x_14);
lean_inc(x_185);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_8);
lean_inc(x_11);
lean_inc(x_10);
lean_ctor_set(x_4, 5, x_185);
lean_ctor_set(x_4, 2, x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_283 = l_Lean_Elab_Command_runLinters(x_2, x_4, x_5, x_193);
if (lean_obj_tag(x_283) == 0)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_285 = x_283;
} else {
 lean_dec_ref(x_283);
 x_285 = lean_box(0);
}
x_286 = lean_ctor_get(x_2, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_2, 1);
lean_inc(x_287);
x_288 = l_Lean_nullKind;
x_289 = lean_name_eq(x_286, x_288);
lean_dec(x_286);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; 
lean_dec(x_287);
lean_dec(x_285);
x_290 = lean_st_ref_get(x_5, x_284);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = lean_ctor_get(x_291, 2);
lean_inc(x_293);
lean_dec(x_291);
x_294 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_293);
lean_dec(x_293);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_296 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1345____closed__1;
x_297 = l_Lean_checkTraceOption(x_295, x_296);
lean_dec(x_295);
if (x_297 == 0)
{
x_194 = x_292;
goto block_282;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_inc(x_2);
x_298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_298, 0, x_2);
x_299 = l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10(x_296, x_298, x_4, x_5, x_292);
x_300 = lean_ctor_get(x_299, 1);
lean_inc(x_300);
lean_dec(x_299);
x_194 = x_300;
goto block_282;
}
}
else
{
lean_object* x_301; lean_object* x_302; uint8_t x_303; 
lean_dec(x_185);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_301 = lean_array_get_size(x_287);
x_302 = lean_unsigned_to_nat(0u);
x_303 = lean_nat_dec_lt(x_302, x_301);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_301);
lean_dec(x_287);
lean_dec(x_4);
lean_dec(x_5);
x_304 = lean_box(0);
if (lean_is_scalar(x_285)) {
 x_305 = lean_alloc_ctor(0, 2, 0);
} else {
 x_305 = x_285;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_284);
return x_305;
}
else
{
uint8_t x_306; 
x_306 = lean_nat_dec_le(x_301, x_301);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; 
lean_dec(x_301);
lean_dec(x_287);
lean_dec(x_4);
lean_dec(x_5);
x_307 = lean_box(0);
if (lean_is_scalar(x_285)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_285;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_284);
return x_308;
}
else
{
size_t x_309; size_t x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_285);
x_309 = 0;
x_310 = lean_usize_of_nat(x_301);
lean_dec(x_301);
x_311 = lean_box(0);
x_312 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__11(x_287, x_309, x_310, x_311, x_4, x_5, x_284);
lean_dec(x_4);
lean_dec(x_287);
return x_312;
}
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_185);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_313 = lean_ctor_get(x_283, 1);
lean_inc(x_313);
lean_dec(x_283);
x_314 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__3;
x_315 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_314, x_4, x_5, x_313);
lean_dec(x_5);
return x_315;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_4);
lean_dec(x_185);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_316 = lean_ctor_get(x_283, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_283, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_318 = x_283;
} else {
 lean_dec_ref(x_283);
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
block_282:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_222; lean_object* x_223; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_195 = lean_st_ref_get(x_5, x_194);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_198 = x_195;
} else {
 lean_dec_ref(x_195);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get(x_196, 0);
lean_inc(x_199);
x_231 = lean_st_ref_get(x_5, x_197);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
lean_dec(x_232);
x_235 = l_Lean_Elab_Command_getRef(x_4, x_5, x_233);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_238 = l_Lean_Elab_Command_getCurrMacroScope(x_4, x_5, x_237);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_st_ref_get(x_5, x_240);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_ctor_get(x_242, 4);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_st_ref_get(x_5, x_243);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_ctor_get(x_246, 3);
lean_inc(x_248);
lean_dec(x_246);
lean_inc(x_234);
x_249 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_249, 0, x_234);
x_250 = x_249;
x_251 = lean_environment_main_module(x_234);
lean_inc(x_8);
x_252 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
lean_ctor_set(x_252, 2, x_239);
lean_ctor_set(x_252, 3, x_8);
lean_ctor_set(x_252, 4, x_244);
lean_ctor_set(x_252, 5, x_236);
lean_inc(x_2);
x_253 = l_Lean_Elab_getMacros(x_199, x_2, x_252, x_248);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_198);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_st_ref_take(x_5, x_247);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_ctor_get(x_257, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_257, 1);
lean_inc(x_260);
x_261 = lean_ctor_get(x_257, 2);
lean_inc(x_261);
x_262 = lean_ctor_get(x_257, 4);
lean_inc(x_262);
x_263 = lean_ctor_get(x_257, 5);
lean_inc(x_263);
x_264 = lean_ctor_get(x_257, 6);
lean_inc(x_264);
x_265 = lean_ctor_get(x_257, 7);
lean_inc(x_265);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 lean_ctor_release(x_257, 2);
 lean_ctor_release(x_257, 3);
 lean_ctor_release(x_257, 4);
 lean_ctor_release(x_257, 5);
 lean_ctor_release(x_257, 6);
 lean_ctor_release(x_257, 7);
 x_266 = x_257;
} else {
 lean_dec_ref(x_257);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(0, 8, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_259);
lean_ctor_set(x_267, 1, x_260);
lean_ctor_set(x_267, 2, x_261);
lean_ctor_set(x_267, 3, x_255);
lean_ctor_set(x_267, 4, x_262);
lean_ctor_set(x_267, 5, x_263);
lean_ctor_set(x_267, 6, x_264);
lean_ctor_set(x_267, 7, x_265);
x_268 = lean_st_ref_set(x_5, x_267, x_258);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec(x_268);
x_270 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_270, 0, x_254);
x_200 = x_270;
x_201 = x_269;
goto block_221;
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_253, 0);
lean_inc(x_271);
lean_dec(x_253);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_274, 0, x_273);
x_275 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_275, 0, x_274);
lean_inc(x_4);
x_276 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__7(x_272, x_275, x_4, x_5, x_247);
lean_dec(x_272);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_222 = x_277;
x_223 = x_278;
goto block_230;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg(x_247);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_222 = x_280;
x_223 = x_281;
goto block_230;
}
}
block_221:
{
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_185);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_202 = l_Lean_Elab_Command_commandElabAttribute;
x_203 = lean_ctor_get(x_202, 2);
lean_inc(x_203);
x_204 = l_Lean_PersistentEnvExtension_getState___rarg(x_203, x_199);
lean_dec(x_199);
lean_dec(x_203);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
lean_inc(x_2);
x_206 = l_Lean_Syntax_getKind(x_2);
x_207 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1(x_205, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_196);
lean_dec(x_2);
x_208 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_208, 0, x_206);
x_209 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabUsingElabFns___closed__2;
x_210 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
x_211 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabUsingElabFns___closed__4;
x_212 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_212, x_4, x_5, x_201);
lean_dec(x_5);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_206);
x_214 = lean_ctor_get(x_207, 0);
lean_inc(x_214);
lean_dec(x_207);
x_215 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing(x_196, x_2, x_214, x_4, x_5, x_201);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_199);
lean_dec(x_196);
lean_dec(x_4);
x_216 = lean_ctor_get(x_200, 0);
lean_inc(x_216);
lean_dec(x_200);
lean_inc(x_216);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_2);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_13);
x_219 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_219, 0, x_10);
lean_ctor_set(x_219, 1, x_11);
lean_ctor_set(x_219, 2, x_8);
lean_ctor_set(x_219, 3, x_12);
lean_ctor_set(x_219, 4, x_218);
lean_ctor_set(x_219, 5, x_185);
lean_ctor_set(x_219, 6, x_14);
x_220 = l_Lean_Elab_Command_elabCommand(x_216, x_219, x_5, x_201);
lean_dec(x_219);
return x_220;
}
}
block_230:
{
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_224; 
lean_dec(x_199);
lean_dec(x_196);
lean_dec(x_4);
lean_dec(x_185);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_198)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_198;
 lean_ctor_set_tag(x_224, 1);
}
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_225 = lean_ctor_get(x_222, 0);
lean_inc(x_225);
x_226 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_227 = lean_nat_dec_eq(x_226, x_225);
lean_dec(x_225);
if (x_227 == 0)
{
lean_object* x_228; 
lean_dec(x_199);
lean_dec(x_196);
lean_dec(x_4);
lean_dec(x_185);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_198)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_198;
 lean_ctor_set_tag(x_228, 1);
}
lean_ctor_set(x_228, 0, x_222);
lean_ctor_set(x_228, 1, x_223);
return x_228;
}
else
{
lean_object* x_229; 
lean_dec(x_222);
lean_dec(x_198);
x_229 = lean_box(0);
x_200 = x_229;
x_201 = x_223;
goto block_221;
}
}
}
}
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_431; 
x_320 = lean_ctor_get(x_4, 0);
x_321 = lean_ctor_get(x_4, 1);
x_322 = lean_ctor_get(x_4, 3);
x_323 = lean_ctor_get(x_4, 4);
x_324 = lean_ctor_get(x_4, 6);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_4);
x_325 = lean_st_ref_take(x_5, x_6);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
lean_dec(x_325);
x_328 = lean_ctor_get(x_326, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_326, 1);
lean_inc(x_329);
x_330 = lean_ctor_get(x_326, 2);
lean_inc(x_330);
x_331 = lean_ctor_get(x_326, 3);
lean_inc(x_331);
x_332 = lean_ctor_get(x_326, 4);
lean_inc(x_332);
x_333 = lean_ctor_get(x_326, 5);
lean_inc(x_333);
x_334 = lean_ctor_get(x_326, 6);
lean_inc(x_334);
x_335 = lean_ctor_get(x_326, 7);
lean_inc(x_335);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 lean_ctor_release(x_326, 2);
 lean_ctor_release(x_326, 3);
 lean_ctor_release(x_326, 4);
 lean_ctor_release(x_326, 5);
 lean_ctor_release(x_326, 6);
 lean_ctor_release(x_326, 7);
 x_336 = x_326;
} else {
 lean_dec_ref(x_326);
 x_336 = lean_box(0);
}
x_337 = lean_nat_add(x_331, x_7);
if (lean_is_scalar(x_336)) {
 x_338 = lean_alloc_ctor(0, 8, 0);
} else {
 x_338 = x_336;
}
lean_ctor_set(x_338, 0, x_328);
lean_ctor_set(x_338, 1, x_329);
lean_ctor_set(x_338, 2, x_330);
lean_ctor_set(x_338, 3, x_337);
lean_ctor_set(x_338, 4, x_332);
lean_ctor_set(x_338, 5, x_333);
lean_ctor_set(x_338, 6, x_334);
lean_ctor_set(x_338, 7, x_335);
x_339 = lean_st_ref_set(x_5, x_338, x_327);
x_340 = lean_ctor_get(x_339, 1);
lean_inc(x_340);
lean_dec(x_339);
lean_inc(x_324);
lean_inc(x_331);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_8);
lean_inc(x_321);
lean_inc(x_320);
x_341 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_341, 0, x_320);
lean_ctor_set(x_341, 1, x_321);
lean_ctor_set(x_341, 2, x_8);
lean_ctor_set(x_341, 3, x_322);
lean_ctor_set(x_341, 4, x_323);
lean_ctor_set(x_341, 5, x_331);
lean_ctor_set(x_341, 6, x_324);
lean_inc(x_5);
lean_inc(x_341);
lean_inc(x_2);
x_431 = l_Lean_Elab_Command_runLinters(x_2, x_341, x_5, x_340);
if (lean_obj_tag(x_431) == 0)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; 
x_432 = lean_ctor_get(x_431, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_433 = x_431;
} else {
 lean_dec_ref(x_431);
 x_433 = lean_box(0);
}
x_434 = lean_ctor_get(x_2, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_2, 1);
lean_inc(x_435);
x_436 = l_Lean_nullKind;
x_437 = lean_name_eq(x_434, x_436);
lean_dec(x_434);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; 
lean_dec(x_435);
lean_dec(x_433);
x_438 = lean_st_ref_get(x_5, x_432);
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec(x_438);
x_441 = lean_ctor_get(x_439, 2);
lean_inc(x_441);
lean_dec(x_439);
x_442 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_441);
lean_dec(x_441);
x_443 = lean_ctor_get(x_442, 1);
lean_inc(x_443);
lean_dec(x_442);
x_444 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1345____closed__1;
x_445 = l_Lean_checkTraceOption(x_443, x_444);
lean_dec(x_443);
if (x_445 == 0)
{
x_342 = x_440;
goto block_430;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_inc(x_2);
x_446 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_446, 0, x_2);
x_447 = l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10(x_444, x_446, x_341, x_5, x_440);
x_448 = lean_ctor_get(x_447, 1);
lean_inc(x_448);
lean_dec(x_447);
x_342 = x_448;
goto block_430;
}
}
else
{
lean_object* x_449; lean_object* x_450; uint8_t x_451; 
lean_dec(x_331);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_8);
lean_dec(x_2);
x_449 = lean_array_get_size(x_435);
x_450 = lean_unsigned_to_nat(0u);
x_451 = lean_nat_dec_lt(x_450, x_449);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; 
lean_dec(x_449);
lean_dec(x_435);
lean_dec(x_341);
lean_dec(x_5);
x_452 = lean_box(0);
if (lean_is_scalar(x_433)) {
 x_453 = lean_alloc_ctor(0, 2, 0);
} else {
 x_453 = x_433;
}
lean_ctor_set(x_453, 0, x_452);
lean_ctor_set(x_453, 1, x_432);
return x_453;
}
else
{
uint8_t x_454; 
x_454 = lean_nat_dec_le(x_449, x_449);
if (x_454 == 0)
{
lean_object* x_455; lean_object* x_456; 
lean_dec(x_449);
lean_dec(x_435);
lean_dec(x_341);
lean_dec(x_5);
x_455 = lean_box(0);
if (lean_is_scalar(x_433)) {
 x_456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_456 = x_433;
}
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_432);
return x_456;
}
else
{
size_t x_457; size_t x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_433);
x_457 = 0;
x_458 = lean_usize_of_nat(x_449);
lean_dec(x_449);
x_459 = lean_box(0);
x_460 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__11(x_435, x_457, x_458, x_459, x_341, x_5, x_432);
lean_dec(x_341);
lean_dec(x_435);
return x_460;
}
}
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_331);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_8);
lean_dec(x_2);
x_461 = lean_ctor_get(x_431, 1);
lean_inc(x_461);
lean_dec(x_431);
x_462 = l_Lean_Elab_Tactic_evalTacticAux___lambda__1___closed__3;
x_463 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_462, x_341, x_5, x_461);
lean_dec(x_5);
return x_463;
}
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_dec(x_341);
lean_dec(x_331);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_464 = lean_ctor_get(x_431, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_431, 1);
lean_inc(x_465);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_466 = x_431;
} else {
 lean_dec_ref(x_431);
 x_466 = lean_box(0);
}
if (lean_is_scalar(x_466)) {
 x_467 = lean_alloc_ctor(1, 2, 0);
} else {
 x_467 = x_466;
}
lean_ctor_set(x_467, 0, x_464);
lean_ctor_set(x_467, 1, x_465);
return x_467;
}
block_430:
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_370; lean_object* x_371; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_343 = lean_st_ref_get(x_5, x_342);
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_346 = x_343;
} else {
 lean_dec_ref(x_343);
 x_346 = lean_box(0);
}
x_347 = lean_ctor_get(x_344, 0);
lean_inc(x_347);
x_379 = lean_st_ref_get(x_5, x_345);
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec(x_379);
x_382 = lean_ctor_get(x_380, 0);
lean_inc(x_382);
lean_dec(x_380);
x_383 = l_Lean_Elab_Command_getRef(x_341, x_5, x_381);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec(x_383);
x_386 = l_Lean_Elab_Command_getCurrMacroScope(x_341, x_5, x_385);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_389 = lean_st_ref_get(x_5, x_388);
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
lean_dec(x_389);
x_392 = lean_ctor_get(x_390, 4);
lean_inc(x_392);
lean_dec(x_390);
x_393 = lean_st_ref_get(x_5, x_391);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_396 = lean_ctor_get(x_394, 3);
lean_inc(x_396);
lean_dec(x_394);
lean_inc(x_382);
x_397 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_397, 0, x_382);
x_398 = x_397;
x_399 = lean_environment_main_module(x_382);
lean_inc(x_8);
x_400 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
lean_ctor_set(x_400, 2, x_387);
lean_ctor_set(x_400, 3, x_8);
lean_ctor_set(x_400, 4, x_392);
lean_ctor_set(x_400, 5, x_384);
lean_inc(x_2);
x_401 = l_Lean_Elab_getMacros(x_347, x_2, x_400, x_396);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_346);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = lean_st_ref_take(x_5, x_395);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
x_407 = lean_ctor_get(x_405, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_405, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_405, 2);
lean_inc(x_409);
x_410 = lean_ctor_get(x_405, 4);
lean_inc(x_410);
x_411 = lean_ctor_get(x_405, 5);
lean_inc(x_411);
x_412 = lean_ctor_get(x_405, 6);
lean_inc(x_412);
x_413 = lean_ctor_get(x_405, 7);
lean_inc(x_413);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 lean_ctor_release(x_405, 2);
 lean_ctor_release(x_405, 3);
 lean_ctor_release(x_405, 4);
 lean_ctor_release(x_405, 5);
 lean_ctor_release(x_405, 6);
 lean_ctor_release(x_405, 7);
 x_414 = x_405;
} else {
 lean_dec_ref(x_405);
 x_414 = lean_box(0);
}
if (lean_is_scalar(x_414)) {
 x_415 = lean_alloc_ctor(0, 8, 0);
} else {
 x_415 = x_414;
}
lean_ctor_set(x_415, 0, x_407);
lean_ctor_set(x_415, 1, x_408);
lean_ctor_set(x_415, 2, x_409);
lean_ctor_set(x_415, 3, x_403);
lean_ctor_set(x_415, 4, x_410);
lean_ctor_set(x_415, 5, x_411);
lean_ctor_set(x_415, 6, x_412);
lean_ctor_set(x_415, 7, x_413);
x_416 = lean_st_ref_set(x_5, x_415, x_406);
x_417 = lean_ctor_get(x_416, 1);
lean_inc(x_417);
lean_dec(x_416);
x_418 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_418, 0, x_402);
x_348 = x_418;
x_349 = x_417;
goto block_369;
}
else
{
lean_object* x_419; 
x_419 = lean_ctor_get(x_401, 0);
lean_inc(x_419);
lean_dec(x_401);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
x_422 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_422, 0, x_421);
x_423 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_423, 0, x_422);
lean_inc(x_341);
x_424 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__7(x_420, x_423, x_341, x_5, x_395);
lean_dec(x_420);
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
x_370 = x_425;
x_371 = x_426;
goto block_378;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___rarg(x_395);
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_370 = x_428;
x_371 = x_429;
goto block_378;
}
}
block_369:
{
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_331);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_8);
x_350 = l_Lean_Elab_Command_commandElabAttribute;
x_351 = lean_ctor_get(x_350, 2);
lean_inc(x_351);
x_352 = l_Lean_PersistentEnvExtension_getState___rarg(x_351, x_347);
lean_dec(x_347);
lean_dec(x_351);
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
lean_dec(x_352);
lean_inc(x_2);
x_354 = l_Lean_Syntax_getKind(x_2);
x_355 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1(x_353, x_354);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_344);
lean_dec(x_2);
x_356 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_356, 0, x_354);
x_357 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabUsingElabFns___closed__2;
x_358 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_356);
x_359 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabUsingElabFns___closed__4;
x_360 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
x_361 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_360, x_341, x_5, x_349);
lean_dec(x_5);
return x_361;
}
else
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_354);
x_362 = lean_ctor_get(x_355, 0);
lean_inc(x_362);
lean_dec(x_355);
x_363 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing(x_344, x_2, x_362, x_341, x_5, x_349);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_347);
lean_dec(x_344);
lean_dec(x_341);
x_364 = lean_ctor_get(x_348, 0);
lean_inc(x_364);
lean_dec(x_348);
lean_inc(x_364);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_2);
lean_ctor_set(x_365, 1, x_364);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_323);
x_367 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_367, 0, x_320);
lean_ctor_set(x_367, 1, x_321);
lean_ctor_set(x_367, 2, x_8);
lean_ctor_set(x_367, 3, x_322);
lean_ctor_set(x_367, 4, x_366);
lean_ctor_set(x_367, 5, x_331);
lean_ctor_set(x_367, 6, x_324);
x_368 = l_Lean_Elab_Command_elabCommand(x_364, x_367, x_5, x_349);
lean_dec(x_367);
return x_368;
}
}
block_378:
{
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_372; 
lean_dec(x_347);
lean_dec(x_344);
lean_dec(x_341);
lean_dec(x_331);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_346)) {
 x_372 = lean_alloc_ctor(1, 2, 0);
} else {
 x_372 = x_346;
 lean_ctor_set_tag(x_372, 1);
}
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
else
{
lean_object* x_373; lean_object* x_374; uint8_t x_375; 
x_373 = lean_ctor_get(x_370, 0);
lean_inc(x_373);
x_374 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_375 = lean_nat_dec_eq(x_374, x_373);
lean_dec(x_373);
if (x_375 == 0)
{
lean_object* x_376; 
lean_dec(x_347);
lean_dec(x_344);
lean_dec(x_341);
lean_dec(x_331);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
if (lean_is_scalar(x_346)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_346;
 lean_ctor_set_tag(x_376, 1);
}
lean_ctor_set(x_376, 0, x_370);
lean_ctor_set(x_376, 1, x_371);
return x_376;
}
else
{
lean_object* x_377; 
lean_dec(x_370);
lean_dec(x_346);
x_377 = lean_box(0);
x_348 = x_377;
x_349 = x_371;
goto block_369;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_61 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_replaceRef(x_1, x_62);
lean_dec(x_62);
x_65 = lean_ctor_get(x_2, 0);
x_66 = lean_ctor_get(x_2, 1);
x_67 = lean_ctor_get(x_2, 2);
x_68 = lean_ctor_get(x_2, 3);
x_69 = lean_ctor_get(x_2, 4);
x_70 = lean_ctor_get(x_2, 5);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
x_71 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_66);
lean_ctor_set(x_71, 2, x_67);
lean_ctor_set(x_71, 3, x_68);
lean_ctor_set(x_71, 4, x_69);
lean_ctor_set(x_71, 5, x_70);
lean_ctor_set(x_71, 6, x_64);
x_72 = lean_st_ref_get(x_3, x_63);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 4);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_nat_dec_eq(x_67, x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_box(0);
lean_inc(x_3);
x_78 = l_Lean_Elab_Command_elabCommand___lambda__1(x_67, x_1, x_77, x_71, x_3, x_74);
if (lean_obj_tag(x_78) == 0)
{
lean_dec(x_3);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_5 = x_79;
x_6 = x_80;
goto block_60;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_1);
x_81 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_82 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(x_81, x_71, x_3, x_74);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_5 = x_83;
x_6 = x_84;
goto block_60;
}
block_60:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1(x_5, x_2, x_3, x_6);
lean_dec(x_3);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_dec(x_10);
x_11 = l_Lean_Elab_isAbortExceptionId(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_InternalExceptionId_getName(x_9, x_6);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
lean_free_object(x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_13);
x_16 = l_Lean_Elab_Command_withLogging___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_KernelException_toMessageData___closed__15;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 2;
x_21 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_19, x_20, x_2, x_3, x_14);
lean_dec(x_3);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_2, 6);
x_25 = lean_io_error_to_string(x_23);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_inc(x_24);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 1, x_27);
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_12, 0, x_5);
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_ctor_get(x_2, 6);
x_31 = lean_io_error_to_string(x_28);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_inc(x_30);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_free_object(x_5);
lean_dec(x_9);
lean_dec(x_3);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_6);
return x_36;
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_5, 0);
lean_inc(x_37);
lean_dec(x_5);
x_38 = l_Lean_Elab_isAbortExceptionId(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = l_Lean_InternalExceptionId_getName(x_37, x_6);
lean_dec(x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_42, 0, x_40);
x_43 = l_Lean_Elab_Command_withLogging___closed__2;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Lean_KernelException_toMessageData___closed__15;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = 2;
x_48 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_46, x_47, x_2, x_3, x_41);
lean_dec(x_3);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_3);
x_49 = lean_ctor_get(x_39, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_51 = x_39;
} else {
 lean_dec_ref(x_39);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_2, 6);
x_53 = lean_io_error_to_string(x_49);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_inc(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
if (lean_is_scalar(x_51)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_51;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_50);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_37);
lean_dec(x_3);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_6);
return x_59;
}
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_Command_elabCommand___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Elab_Command_elabCommand___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Elab_Command_elabCommand___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Elab_Command_elabCommand___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Elab_Command_elabCommand___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Elab_Command_elabCommand___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_Elab_Command_elabCommand___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__9(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_logTrace___at_Lean_Elab_Command_elabCommand___spec__10(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabCommand___spec__11(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabCommand___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Command_elabCommand___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elabCommand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabCommand(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = lean_apply_4(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 4);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_7);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_3, 4, x_12);
x_13 = l_Lean_Elab_Command_elabCommand(x_7, x_3, x_4, x_8);
lean_dec(x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
x_17 = lean_ctor_get(x_3, 3);
x_18 = lean_ctor_get(x_3, 4);
x_19 = lean_ctor_get(x_3, 5);
x_20 = lean_ctor_get(x_3, 6);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_7);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
x_23 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_17);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
x_24 = l_Lean_Elab_Command_elabCommand(x_7, x_23, x_4, x_8);
lean_dec(x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
return x_6;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_2);
x_4 = lean_ctor_get(x_3, 5);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_instInhabitedCommandElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedCommandElabM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedException___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_instInhabitedCommandElabM___lambda__1___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_instInhabitedCommandElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_instInhabitedCommandElabM___closed__1;
return x_2;
}
}
lean_object* l_Lean_Elab_Command_instInhabitedCommandElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_instInhabitedCommandElabM___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 1;
x_2 = 0;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, 2, x_1);
lean_ctor_set_uint8(x_4, 3, x_2);
lean_ctor_set_uint8(x_4, 4, x_2);
lean_ctor_set_uint8(x_4, 5, x_3);
lean_ctor_set_uint8(x_4, 6, x_1);
lean_ctor_set_uint8(x_4, 7, x_2);
lean_ctor_set_uint8(x_4, 8, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1;
x_2 = l_Lean_LocalContext_mkEmpty___closed__1;
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2;
return x_1;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_ctor_get(x_1, 5);
x_8 = 1;
x_9 = 0;
x_10 = l_Std_PersistentArray_empty___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_3);
lean_ctor_set(x_11, 3, x_6);
lean_ctor_set(x_11, 4, x_7);
lean_ctor_set(x_11, 5, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*6, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*6 + 1, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*6 + 2, x_9);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermState(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 4);
x_4 = lean_box(0);
x_5 = lean_ctor_get(x_2, 7);
lean_inc(x_5);
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 1);
lean_dec(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_10 = l_Std_PersistentArray_empty___closed__1;
lean_ctor_set(x_5, 1, x_10);
lean_ctor_set(x_5, 0, x_9);
lean_inc(x_3);
x_11 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set(x_11, 4, x_4);
lean_ctor_set(x_11, 5, x_5);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
lean_dec(x_5);
x_13 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_14 = l_Std_PersistentArray_empty___closed__1;
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_12);
lean_inc(x_3);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_4);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_16, 4, x_4);
lean_ctor_set(x_16, 5, x_15);
return x_16;
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermState___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermState(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__3(x_1, x_7, x_5);
lean_dec(x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 6);
lean_inc(x_9);
x_10 = l_Lean_replaceRef(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getPos(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = 1;
x_16 = x_3 + x_15;
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Elab_mkMessageCore(x_12, x_13, x_14, x_17, x_18);
lean_dec(x_13);
x_20 = l_Std_PersistentArray_push___rarg(x_5, x_19);
x_3 = x_16;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = 0;
x_24 = l_Lean_Elab_mkMessageCore(x_12, x_13, x_14, x_23, x_22);
lean_dec(x_13);
x_25 = l_Std_PersistentArray_push___rarg(x_5, x_24);
x_3 = x_16;
x_5 = x_25;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__4(x_1, x_4, x_9, x_10, x_3);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
lean_dec(x_13);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__5(x_1, x_12, x_17, x_18, x_3);
return x_19;
}
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__3(x_1, x_7, x_5);
lean_dec(x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 6);
lean_inc(x_9);
x_10 = l_Lean_replaceRef(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getPos(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = 1;
x_16 = x_3 + x_15;
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Elab_mkMessageCore(x_12, x_13, x_14, x_17, x_18);
lean_dec(x_13);
x_20 = l_Std_PersistentArray_push___rarg(x_5, x_19);
x_3 = x_16;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = 0;
x_24 = l_Lean_Elab_mkMessageCore(x_12, x_13, x_14, x_23, x_22);
lean_dec(x_13);
x_25 = l_Std_PersistentArray_push___rarg(x_5, x_24);
x_3 = x_16;
x_5 = x_25;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = x_3 >> x_4;
x_8 = lean_usize_to_nat(x_7);
x_9 = l_Std_PersistentArray_getAux___rarg___closed__1;
x_10 = lean_array_get(x_9, x_6, x_8);
x_11 = 1;
x_12 = x_11 << x_4;
x_13 = x_12 - x_11;
x_14 = x_3 & x_13;
x_15 = 5;
x_16 = x_4 - x_15;
lean_inc(x_1);
x_17 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__2(x_1, x_10, x_14, x_16, x_5);
lean_dec(x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_8, x_18);
lean_dec(x_8);
x_20 = lean_array_get_size(x_6);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
return x_17;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_20, x_20);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
return x_17;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__6(x_1, x_6, x_23, x_24, x_17);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_usize_to_nat(x_3);
x_28 = lean_array_get_size(x_26);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
return x_5;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_28, x_28);
if (x_30 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
return x_5;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_33 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__7(x_1, x_26, x_31, x_32, x_5);
return x_33;
}
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 6);
lean_inc(x_9);
x_10 = l_Lean_replaceRef(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getPos(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = 1;
x_16 = x_3 + x_15;
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Elab_mkMessageCore(x_12, x_13, x_14, x_17, x_18);
lean_dec(x_13);
x_20 = l_Std_PersistentArray_push___rarg(x_5, x_19);
x_3 = x_16;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = 0;
x_24 = l_Lean_Elab_mkMessageCore(x_12, x_13, x_14, x_23, x_22);
lean_dec(x_13);
x_25 = l_Std_PersistentArray_push___rarg(x_5, x_24);
x_3 = x_16;
x_5 = x_25;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 6);
lean_inc(x_9);
x_10 = l_Lean_replaceRef(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getPos(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = 1;
x_16 = x_3 + x_15;
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Elab_mkMessageCore(x_12, x_13, x_14, x_17, x_18);
lean_dec(x_13);
x_20 = l_Std_PersistentArray_push___rarg(x_5, x_19);
x_3 = x_16;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = 0;
x_24 = l_Lean_Elab_mkMessageCore(x_12, x_13, x_14, x_23, x_22);
lean_dec(x_13);
x_25 = l_Std_PersistentArray_push___rarg(x_5, x_24);
x_3 = x_16;
x_5 = x_25;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__10(x_1, x_7, x_5);
lean_dec(x_7);
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__12(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 6);
lean_inc(x_9);
x_10 = l_Lean_replaceRef(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getPos(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = 1;
x_16 = x_3 + x_15;
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Elab_mkMessageCore(x_12, x_13, x_14, x_17, x_18);
lean_dec(x_13);
x_20 = l_Std_PersistentArray_push___rarg(x_5, x_19);
x_3 = x_16;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = 0;
x_24 = l_Lean_Elab_mkMessageCore(x_12, x_13, x_14, x_23, x_22);
lean_dec(x_13);
x_25 = l_Std_PersistentArray_push___rarg(x_5, x_24);
x_3 = x_16;
x_5 = x_25;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__11(x_1, x_4, x_9, x_10, x_3);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
lean_dec(x_13);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__12(x_1, x_12, x_17, x_18, x_3);
return x_19;
}
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 6);
lean_inc(x_9);
x_10 = l_Lean_replaceRef(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getPos(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_dec(x_7);
x_15 = 1;
x_16 = x_3 + x_15;
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Elab_mkMessageCore(x_12, x_13, x_14, x_17, x_18);
lean_dec(x_13);
x_20 = l_Std_PersistentArray_push___rarg(x_5, x_19);
x_3 = x_16;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = 0;
x_24 = l_Lean_Elab_mkMessageCore(x_12, x_13, x_14, x_23, x_22);
lean_dec(x_13);
x_25 = l_Std_PersistentArray_push___rarg(x_5, x_24);
x_3 = x_16;
x_5 = x_25;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_nat_dec_le(x_7, x_4);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_usize_of_nat(x_4);
x_11 = lean_ctor_get_usize(x_2, 4);
lean_inc(x_1);
x_12 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__2(x_1, x_9, x_10, x_11, x_3);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_lt(x_5, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_1);
return x_12;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_14, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_1);
return x_12;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_19 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__8(x_1, x_13, x_17, x_18, x_12);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_nat_sub(x_4, x_7);
x_22 = lean_array_get_size(x_20);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_22, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_27 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__9(x_1, x_20, x_25, x_26, x_3);
return x_27;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_29 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__10(x_1, x_28, x_3);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_array_get_size(x_30);
x_32 = lean_nat_dec_lt(x_5, x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_1);
return x_29;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_31, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_1);
return x_29;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_36 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__13(x_1, x_30, x_34, x_35, x_29);
return x_36;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__1(x_1, x_4, x_2, x_5);
return x_6;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__4(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__5(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__6(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__7(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__8(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__9(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__11(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__12(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__10(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__13(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PersistentArray_foldlM___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_liftTermElabM_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Command_liftTermElabM_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_liftTermElabM_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_apply_4(x_2, x_7, x_8, x_6, x_5);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_liftTermElabM_match__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM_match__2___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_7 < x_6;
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = x_8;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_array_uget(x_8, x_7);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_8, x_7, x_12);
x_14 = x_11;
lean_inc(x_5);
x_15 = l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__2(x_1, x_2, x_3, x_4, x_5, x_14);
x_16 = 1;
x_17 = x_7 + x_16;
x_18 = x_15;
x_19 = lean_array_uset(x_13, x_7, x_18);
x_7 = x_17;
x_8 = x_19;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_7 < x_6;
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = x_8;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_11 = lean_array_uget(x_8, x_7);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_8, x_7, x_12);
x_14 = x_11;
x_15 = lean_ctor_get(x_5, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_InfoTree_substitute(x_14, x_16);
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
x_26 = 1;
x_27 = x_7 + x_26;
x_28 = x_25;
x_29 = lean_array_uset(x_13, x_7, x_28);
x_7 = x_27;
x_8 = x_29;
goto _start;
}
}
}
lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = x_8;
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__3(x_1, x_2, x_3, x_4, x_5, x_10, x_11, x_12);
x_14 = x_13;
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_array_get_size(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = x_15;
x_20 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__3(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_19);
x_21 = x_20;
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_array_get_size(x_24);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = x_24;
x_29 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__4(x_1, x_2, x_3, x_4, x_5, x_26, x_27, x_28);
x_30 = x_29;
lean_ctor_set(x_6, 0, x_30);
return x_6;
}
else
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_6, 0);
lean_inc(x_31);
lean_dec(x_6);
x_32 = lean_array_get_size(x_31);
x_33 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_34 = 0;
x_35 = x_31;
x_36 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__4(x_1, x_2, x_3, x_4, x_5, x_33, x_34, x_35);
x_37 = x_36;
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_7 < x_6;
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = x_8;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_11 = lean_array_uget(x_8, x_7);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_8, x_7, x_12);
x_14 = x_11;
x_15 = lean_ctor_get(x_5, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_InfoTree_substitute(x_14, x_16);
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
x_26 = 1;
x_27 = x_7 + x_26;
x_28 = x_25;
x_29 = lean_array_uset(x_13, x_7, x_28);
x_7 = x_27;
x_8 = x_29;
goto _start;
}
}
}
lean_object* l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_5);
x_10 = l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__2(x_1, x_2, x_3, x_4, x_5, x_8);
x_11 = lean_array_get_size(x_9);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = x_9;
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__5(x_1, x_2, x_3, x_4, x_5, x_12, x_13, x_14);
x_16 = x_15;
lean_ctor_set(x_6, 1, x_16);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 2);
x_20 = lean_ctor_get_usize(x_6, 4);
x_21 = lean_ctor_get(x_6, 3);
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
lean_inc(x_5);
x_22 = l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__2(x_1, x_2, x_3, x_4, x_5, x_17);
x_23 = lean_array_get_size(x_18);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = x_18;
x_27 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__5(x_1, x_2, x_3, x_4, x_5, x_24, x_25, x_26);
x_28 = x_27;
x_29 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_19);
lean_ctor_set(x_29, 3, x_21);
lean_ctor_set_usize(x_29, 4, x_20);
return x_29;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_MetavarContext_instInhabitedMetavarContext___closed__1;
x_2 = l_Lean_Meta_instInhabitedCache___closed__1;
x_3 = l_Lean_NameSet_empty;
x_4 = l_Std_PersistentArray_empty___closed__1;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1;
x_2 = l_Lean_Elab_Term_setElabConfig(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__2;
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 6);
lean_inc(x_12);
x_13 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_10);
lean_dec(x_10);
x_14 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermContext(x_3, x_7, x_1);
lean_inc(x_7);
x_15 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkTermState(x_13, x_7);
x_16 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkCoreContext(x_3, x_7);
lean_dec(x_7);
x_17 = l_Lean_resetTraceState___rarg___lambda__1___closed__1;
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_12);
lean_ctor_set(x_18, 3, x_17);
x_19 = lean_st_mk_ref(x_18, x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_20, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_25 = lean_st_mk_ref(x_24, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_114 = lean_st_ref_get(x_20, x_27);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_st_mk_ref(x_15, x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__3;
lean_inc(x_20);
lean_inc(x_26);
lean_inc(x_117);
x_120 = lean_apply_7(x_2, x_14, x_117, x_119, x_26, x_16, x_20, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_121);
x_124 = lean_st_ref_get(x_20, x_122);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_st_ref_get(x_117, x_125);
lean_dec(x_117);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_123);
lean_ctor_set(x_129, 1, x_127);
x_28 = x_129;
x_29 = x_128;
goto block_113;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_130 = lean_ctor_get(x_120, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_120, 1);
lean_inc(x_131);
lean_dec(x_120);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_130);
x_133 = lean_st_ref_get(x_20, x_131);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_st_ref_get(x_117, x_134);
lean_dec(x_117);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_132);
lean_ctor_set(x_138, 1, x_136);
x_28 = x_138;
x_29 = x_137;
goto block_113;
}
block_113:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_30 = lean_st_ref_get(x_20, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_st_ref_get(x_26, x_31);
lean_dec(x_26);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_20, x_34);
lean_dec(x_20);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_ctor_get(x_39, 5);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
lean_inc(x_39);
x_42 = l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__1(x_3, x_13, x_33, x_36, x_39, x_41);
lean_dec(x_33);
lean_dec(x_13);
x_43 = lean_st_ref_take(x_4, x_37);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_36, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_36, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_36, 3);
lean_inc(x_49);
lean_dec(x_36);
x_50 = !lean_is_exclusive(x_44);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_51 = lean_ctor_get(x_44, 1);
x_52 = lean_ctor_get(x_44, 7);
x_53 = lean_ctor_get(x_44, 6);
lean_dec(x_53);
x_54 = lean_ctor_get(x_44, 3);
lean_dec(x_54);
x_55 = lean_ctor_get(x_44, 0);
lean_dec(x_55);
x_56 = lean_ctor_get(x_39, 3);
lean_inc(x_56);
lean_dec(x_39);
x_57 = l_Std_PersistentArray_append___rarg(x_51, x_56);
lean_dec(x_56);
x_58 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages(x_3, x_57, x_49);
lean_dec(x_49);
x_59 = !lean_is_exclusive(x_52);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_52, 1);
x_61 = l_Std_PersistentArray_append___rarg(x_60, x_42);
lean_dec(x_42);
lean_ctor_set(x_52, 1, x_61);
lean_ctor_set(x_44, 6, x_48);
lean_ctor_set(x_44, 3, x_47);
lean_ctor_set(x_44, 1, x_58);
lean_ctor_set(x_44, 0, x_46);
x_62 = lean_st_ref_set(x_4, x_44, x_45);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_38, 0);
lean_inc(x_65);
lean_dec(x_38);
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 0, x_65);
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_67 = lean_ctor_get(x_38, 0);
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_62);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_62, 0);
lean_dec(x_70);
x_71 = lean_ctor_get(x_38, 0);
lean_inc(x_71);
lean_dec(x_38);
lean_ctor_set(x_62, 0, x_71);
return x_62;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_62, 1);
lean_inc(x_72);
lean_dec(x_62);
x_73 = lean_ctor_get(x_38, 0);
lean_inc(x_73);
lean_dec(x_38);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get_uint8(x_52, sizeof(void*)*2);
x_76 = lean_ctor_get(x_52, 0);
x_77 = lean_ctor_get(x_52, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_52);
x_78 = l_Std_PersistentArray_append___rarg(x_77, x_42);
lean_dec(x_42);
x_79 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_75);
lean_ctor_set(x_44, 7, x_79);
lean_ctor_set(x_44, 6, x_48);
lean_ctor_set(x_44, 3, x_47);
lean_ctor_set(x_44, 1, x_58);
lean_ctor_set(x_44, 0, x_46);
x_80 = lean_st_ref_set(x_4, x_44, x_45);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_38, 0);
lean_inc(x_83);
lean_dec(x_38);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_82;
 lean_ctor_set_tag(x_84, 1);
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_86 = x_80;
} else {
 lean_dec_ref(x_80);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_38, 0);
lean_inc(x_87);
lean_dec(x_38);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_89 = lean_ctor_get(x_44, 1);
x_90 = lean_ctor_get(x_44, 2);
x_91 = lean_ctor_get(x_44, 4);
x_92 = lean_ctor_get(x_44, 5);
x_93 = lean_ctor_get(x_44, 7);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_44);
x_94 = lean_ctor_get(x_39, 3);
lean_inc(x_94);
lean_dec(x_39);
x_95 = l_Std_PersistentArray_append___rarg(x_89, x_94);
lean_dec(x_94);
x_96 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addTraceAsMessages(x_3, x_95, x_49);
lean_dec(x_49);
x_97 = lean_ctor_get_uint8(x_93, sizeof(void*)*2);
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_100 = x_93;
} else {
 lean_dec_ref(x_93);
 x_100 = lean_box(0);
}
x_101 = l_Std_PersistentArray_append___rarg(x_99, x_42);
lean_dec(x_42);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 1);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_97);
x_103 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_103, 0, x_46);
lean_ctor_set(x_103, 1, x_96);
lean_ctor_set(x_103, 2, x_90);
lean_ctor_set(x_103, 3, x_47);
lean_ctor_set(x_103, 4, x_91);
lean_ctor_set(x_103, 5, x_92);
lean_ctor_set(x_103, 6, x_48);
lean_ctor_set(x_103, 7, x_102);
x_104 = lean_st_ref_set(x_4, x_103, x_45);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_38, 0);
lean_inc(x_107);
lean_dec(x_38);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_106;
 lean_ctor_set_tag(x_108, 1);
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_110 = x_104;
} else {
 lean_dec_ref(x_104);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_38, 0);
lean_inc(x_111);
lean_dec(x_38);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
return x_112;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_liftTermElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__3(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__4(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentArray_mapMAux___at_Lean_Elab_Command_liftTermElabM___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_liftTermElabM___spec__5(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentArray_mapM___at_Lean_Elab_Command_liftTermElabM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_liftTermElabM___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_runTermElabM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Elab_Term_resetMessageLog(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_3);
x_12 = l_Lean_Elab_Term_addAutoBoundImplicits(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_apply_1(x_1, x_13);
x_16 = 0;
x_17 = l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg(x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Command_runTermElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_7);
lean_dec(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___rarg___lambda__1___boxed), 9, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 10, 3);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_12);
x_14 = lean_box(x_11);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg___boxed), 9, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_Command_liftTermElabM___rarg(x_1, x_15, x_3, x_4, x_8);
return x_16;
}
}
lean_object* l_Lean_Elab_Command_runTermElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_runTermElabM___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_runTermElabM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_runTermElabM___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_runTermElabM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_runTermElabM___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_catchExceptions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = l_Lean_Elab_logException___at_Lean_Elab_Command_withLogging___spec__1(x_10, x_2, x_3, x_11);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
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
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_dec(x_10);
x_27 = l_Lean_Elab_isAbortExceptionId(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_free_object(x_5);
x_28 = l_Lean_InternalExceptionId_getName(x_26, x_24);
lean_dec(x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_31, 0, x_29);
x_32 = l_Lean_Elab_Command_withLogging___closed__2;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_KernelException_toMessageData___closed__15;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = 2;
x_37 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_35, x_36, x_2, x_3, x_30);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_28);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_28, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_44);
return x_28;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_dec(x_28);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_box(0);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_48);
return x_5;
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_5, 1);
lean_inc(x_49);
lean_dec(x_5);
x_50 = lean_ctor_get(x_10, 0);
lean_inc(x_50);
lean_dec(x_10);
x_51 = l_Lean_Elab_isAbortExceptionId(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Lean_InternalExceptionId_getName(x_50, x_49);
lean_dec(x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_55, 0, x_53);
x_56 = l_Lean_Elab_Command_withLogging___closed__2;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_KernelException_toMessageData___closed__15;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = 2;
x_61 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_59, x_60, x_2, x_3, x_54);
lean_dec(x_3);
lean_dec(x_2);
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
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_3);
lean_dec(x_2);
x_66 = lean_ctor_get(x_52, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_67 = x_52;
} else {
 lean_dec_ref(x_52);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
 lean_ctor_set_tag(x_69, 0);
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_49);
return x_71;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_liftAttrM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_liftCoreM___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_liftAttrM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_0__Lean_Elab_Command_liftAttrM___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_liftAttrM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_liftAttrM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_3 < x_2;
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_4);
x_10 = lean_array_uget(x_1, x_3);
x_11 = lean_st_ref_take(x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l_Lean_ScopedEnvExtension_pushScope___rarg(x_10, x_15);
lean_dec(x_10);
lean_ctor_set(x_12, 0, x_16);
x_17 = lean_st_ref_set(x_6, x_12, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 1;
x_20 = x_3 + x_19;
x_21 = lean_box(0);
x_3 = x_20;
x_4 = x_21;
x_7 = x_18;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 2);
x_26 = lean_ctor_get(x_12, 3);
x_27 = lean_ctor_get(x_12, 4);
x_28 = lean_ctor_get(x_12, 5);
x_29 = lean_ctor_get(x_12, 6);
x_30 = lean_ctor_get(x_12, 7);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_31 = l_Lean_ScopedEnvExtension_pushScope___rarg(x_10, x_23);
lean_dec(x_10);
x_32 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_26);
lean_ctor_set(x_32, 4, x_27);
lean_ctor_set(x_32, 5, x_28);
lean_ctor_set(x_32, 6, x_29);
lean_ctor_set(x_32, 7, x_30);
x_33 = lean_st_ref_set(x_6, x_32, x_13);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = 1;
x_36 = x_3 + x_35;
x_37 = lean_box(0);
x_3 = x_36;
x_4 = x_37;
x_7 = x_34;
goto _start;
}
}
}
}
lean_object* l_Lean_pushScope___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = l_Lean_scopedEnvExtensionsRef;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_array_get_size(x_6);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = lean_box(0);
x_12 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__2(x_6, x_9, x_10, x_11, x_1, x_2, x_7);
lean_dec(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_4 < x_3;
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_5);
x_11 = lean_array_uget(x_2, x_4);
x_12 = lean_st_ref_take(x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_1);
x_17 = l_Lean_ScopedEnvExtension_activateScoped___rarg(x_11, x_16, x_1);
lean_ctor_set(x_13, 0, x_17);
x_18 = lean_st_ref_set(x_7, x_13, x_14);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = x_4 + x_20;
x_22 = lean_box(0);
x_4 = x_21;
x_5 = x_22;
x_8 = x_19;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
x_26 = lean_ctor_get(x_13, 2);
x_27 = lean_ctor_get(x_13, 3);
x_28 = lean_ctor_get(x_13, 4);
x_29 = lean_ctor_get(x_13, 5);
x_30 = lean_ctor_get(x_13, 6);
x_31 = lean_ctor_get(x_13, 7);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
lean_inc(x_1);
x_32 = l_Lean_ScopedEnvExtension_activateScoped___rarg(x_11, x_24, x_1);
x_33 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set(x_33, 2, x_26);
lean_ctor_set(x_33, 3, x_27);
lean_ctor_set(x_33, 4, x_28);
lean_ctor_set(x_33, 5, x_29);
lean_ctor_set(x_33, 6, x_30);
lean_ctor_set(x_33, 7, x_31);
x_34 = lean_st_ref_set(x_7, x_33, x_14);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = 1;
x_37 = x_4 + x_36;
x_38 = lean_box(0);
x_4 = x_37;
x_5 = x_38;
x_8 = x_35;
goto _start;
}
}
}
}
lean_object* l_Lean_activateScoped___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_scopedEnvExtensionsRef;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_array_get_size(x_7);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__4(x_1, x_7, x_10, x_11, x_12, x_2, x_3, x_8);
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 2);
lean_inc(x_3);
x_13 = l_Lean_Environment_registerNamespace(x_11, x_3);
x_14 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_inc(x_3);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 0, x_2);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_8, 2, x_18);
lean_ctor_set(x_8, 0, x_13);
x_19 = lean_st_ref_set(x_5, x_8, x_9);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_pushScope___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__1(x_4, x_5, x_20);
if (x_1 == 0)
{
uint8_t x_22; 
lean_dec(x_3);
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
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_29 = l_Lean_activateScoped___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__3(x_3, x_4, x_5, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_14, 1);
x_31 = lean_ctor_get(x_14, 3);
x_32 = lean_ctor_get(x_14, 4);
x_33 = lean_ctor_get(x_14, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
lean_inc(x_3);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_3);
lean_ctor_set(x_34, 3, x_31);
lean_ctor_set(x_34, 4, x_32);
lean_ctor_set(x_34, 5, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_12);
lean_ctor_set(x_8, 2, x_35);
lean_ctor_set(x_8, 0, x_13);
x_36 = lean_st_ref_set(x_5, x_8, x_9);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_pushScope___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__1(x_4, x_5, x_37);
if (x_1 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_3);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = l_Lean_activateScoped___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__3(x_3, x_4, x_5, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_45 = lean_ctor_get(x_8, 0);
x_46 = lean_ctor_get(x_8, 1);
x_47 = lean_ctor_get(x_8, 2);
x_48 = lean_ctor_get(x_8, 3);
x_49 = lean_ctor_get(x_8, 4);
x_50 = lean_ctor_get(x_8, 5);
x_51 = lean_ctor_get(x_8, 6);
x_52 = lean_ctor_get(x_8, 7);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_8);
lean_inc(x_3);
x_53 = l_Lean_Environment_registerNamespace(x_45, x_3);
x_54 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_47);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 5);
lean_inc(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 lean_ctor_release(x_54, 4);
 lean_ctor_release(x_54, 5);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
lean_inc(x_3);
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 6, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_2);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_3);
lean_ctor_set(x_60, 3, x_56);
lean_ctor_set(x_60, 4, x_57);
lean_ctor_set(x_60, 5, x_58);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_47);
x_62 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_62, 0, x_53);
lean_ctor_set(x_62, 1, x_46);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_48);
lean_ctor_set(x_62, 4, x_49);
lean_ctor_set(x_62, 5, x_50);
lean_ctor_set(x_62, 6, x_51);
lean_ctor_set(x_62, 7, x_52);
x_63 = lean_st_ref_set(x_5, x_62, x_9);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Lean_pushScope___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__1(x_4, x_5, x_64);
if (x_1 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_3);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_dec(x_65);
x_71 = l_Lean_activateScoped___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__3(x_3, x_4, x_5, x_70);
return x_71;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__2(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_pushScope___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_pushScope___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__4(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_activateScoped___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_activateScoped___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_10 = lean_box_usize(x_9);
x_11 = lean_apply_3(x_3, x_7, x_8, x_10);
return x_11;
}
default: 
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_apply_1(x_4, x_1);
return x_12;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid scope");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_3);
x_10 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes(x_1, x_8, x_3, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Command_getScope___rarg(x_4, x_11);
if (x_1 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope(x_1, x_9, x_15, x_3, x_4, x_14);
lean_dec(x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_9);
x_20 = lean_name_mk_string(x_19, x_9);
x_21 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope(x_1, x_9, x_20, x_3, x_4, x_18);
lean_dec(x_3);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_3);
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
default: 
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_26 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__3;
x_27 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_26, x_3, x_4, x_5);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addNamespace(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Parser_Command_namespace___elambda__1___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_Syntax_getId(x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes(x_11, x_10, x_2, x_3, x_4);
return x_12;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabNamespace(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNamespace___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_namespace___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabSection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Parser_Command_section___elambda__1___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_27; uint8_t x_28; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_27 = l_Lean_nullKind___closed__2;
lean_inc(x_9);
x_28 = l_Lean_Syntax_isOfKind(x_9, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_box(0);
x_10 = x_29;
goto block_26;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Syntax_getArgs(x_9);
x_31 = lean_array_get_size(x_30);
lean_dec(x_30);
x_32 = lean_nat_dec_eq(x_31, x_8);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
x_10 = x_33;
goto block_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_Syntax_getArg(x_9, x_34);
lean_dec(x_9);
x_36 = l_Lean_identKind___closed__2;
lean_inc(x_35);
x_37 = l_Lean_Syntax_isOfKind(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_2);
x_38 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_38;
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_39 = l_Lean_Syntax_getId(x_35);
lean_dec(x_35);
x_40 = 0;
x_41 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes(x_40, x_39, x_2, x_3, x_4);
return x_41;
}
}
}
block_26:
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_10);
x_11 = l_Lean_nullKind___closed__2;
lean_inc(x_9);
x_12 = l_Lean_Syntax_isOfKind(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_2);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_15 = lean_array_get_size(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_2);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_19 = l_Lean_Elab_Command_getScope___rarg(x_3, x_4);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 2);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 0;
x_24 = l_Lean_instInhabitedParserDescr___closed__1;
x_25 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope(x_23, x_24, x_22, x_2, x_3, x_21);
lean_dec(x_2);
return x_25;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabSection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabSection(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSection___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSection___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabSection(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_section___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSection___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getScopes___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
lean_object* l_Lean_Elab_Command_getScopes(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getScopes___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_getScopes___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getScopes___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_getScopes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getScopes(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 5);
lean_inc(x_12);
lean_dec(x_5);
x_13 = l_Lean_instInhabitedParserDescr___closed__1;
x_14 = lean_string_dec_eq(x_7, x_13);
lean_dec(x_7);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_15 = lean_apply_1(x_3, x_1);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_apply_6(x_2, x_6, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_instInhabitedParserDescr___closed__1;
x_6 = lean_string_dec_eq(x_4, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_3, x_2);
return x_6;
}
case 1:
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_apply_2(x_5, x_1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
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
x_18 = lean_ctor_get(x_8, 5);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box_usize(x_11);
x_20 = lean_apply_10(x_4, x_9, x_10, x_19, x_13, x_12, x_14, x_15, x_16, x_17, x_18);
return x_20;
}
}
default: 
{
lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_apply_2(x_5, x_1, x_2);
return x_21;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader_match__1___rarg), 5, 0);
return x_2;
}
}
uint8_t l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 1:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_string_dec_eq(x_9, x_7);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_6;
x_2 = x_8;
goto _start;
}
}
}
default: 
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes_match__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes_match__1___rarg), 1, 0);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes_match__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_3 < x_2;
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_4);
x_10 = lean_array_uget(x_1, x_3);
x_11 = lean_st_ref_take(x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l_Lean_ScopedEnvExtension_popScope___rarg(x_10, x_15);
lean_dec(x_10);
lean_ctor_set(x_12, 0, x_16);
x_17 = lean_st_ref_set(x_6, x_12, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 1;
x_20 = x_3 + x_19;
x_21 = lean_box(0);
x_3 = x_20;
x_4 = x_21;
x_7 = x_18;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 2);
x_26 = lean_ctor_get(x_12, 3);
x_27 = lean_ctor_get(x_12, 4);
x_28 = lean_ctor_get(x_12, 5);
x_29 = lean_ctor_get(x_12, 6);
x_30 = lean_ctor_get(x_12, 7);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_31 = l_Lean_ScopedEnvExtension_popScope___rarg(x_10, x_23);
lean_dec(x_10);
x_32 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_26);
lean_ctor_set(x_32, 4, x_27);
lean_ctor_set(x_32, 5, x_28);
lean_ctor_set(x_32, 6, x_29);
lean_ctor_set(x_32, 7, x_30);
x_33 = lean_st_ref_set(x_6, x_32, x_13);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = 1;
x_36 = x_3 + x_35;
x_37 = lean_box(0);
x_3 = x_36;
x_4 = x_37;
x_7 = x_34;
goto _start;
}
}
}
}
lean_object* l_Lean_popScope___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = l_Lean_scopedEnvExtensionsRef;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_array_get_size(x_6);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = lean_box(0);
x_12 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__2(x_6, x_9, x_10, x_11, x_1, x_2, x_7);
lean_dec(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_nat_dec_le(x_8, x_3);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_2, x_12);
lean_dec(x_2);
x_14 = l_Lean_popScope___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__1(x_5, x_6, x_7);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_18 = lean_box(0);
x_2 = x_13;
x_3 = x_17;
x_4 = x_18;
x_7 = x_15;
goto _start;
}
else
{
lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_box(0);
x_9 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__3(x_7, x_1, x_5, x_8, x_2, x_3, x_4);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__2(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_popScope___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_popScope___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabEnd_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_elabEnd_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEnd_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabEnd_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_elabEnd_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEnd_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabEnd___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', name is missing");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', name mismatch");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_7; 
x_7 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkAnonymousScope(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Elab_Command_elabEnd___lambda__1___closed__3;
x_9 = l_Lean_throwError___at_Lean_Elab_Command_elabEnd___spec__1(x_8, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_checkEndHeader(x_12, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Elab_Command_elabEnd___lambda__1___closed__6;
x_15 = l_Lean_throwError___at_Lean_Elab_Command_elabEnd___spec__1(x_14, x_4, x_5, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'end', insufficient scopes");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabEnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getOptionalIdent_x3f(x_6);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_getScopes___rarg(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_8, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_8, 1);
lean_inc(x_87);
lean_dec(x_8);
x_9 = x_5;
x_10 = x_86;
x_11 = x_87;
goto block_85;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_7, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_8, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_8, 1);
lean_inc(x_90);
lean_dec(x_8);
x_91 = l_Lean_Name_getNumParts(x_88);
lean_dec(x_88);
x_9 = x_91;
x_10 = x_89;
x_11 = x_90;
goto block_85;
}
block_85:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_List_lengthAux___rarg(x_10, x_12);
x_14 = lean_nat_dec_lt(x_9, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_15 = lean_st_ref_get(x_3, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_List_lengthAux___rarg(x_18, x_12);
lean_dec(x_18);
x_20 = lean_nat_sub(x_19, x_5);
lean_dec(x_19);
x_21 = lean_st_ref_take(x_3, x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_22, 2);
lean_inc(x_20);
x_26 = l_List_drop___rarg(x_20, x_25);
lean_dec(x_25);
lean_ctor_set(x_22, 2, x_26);
x_27 = lean_st_ref_set(x_3, x_22, x_23);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes(x_20, x_2, x_3, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Elab_Command_elabEnd___closed__3;
x_32 = l_Lean_throwError___at_Lean_Elab_Command_elabEnd___spec__1(x_31, x_2, x_3, x_30);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
x_39 = lean_ctor_get(x_22, 2);
x_40 = lean_ctor_get(x_22, 3);
x_41 = lean_ctor_get(x_22, 4);
x_42 = lean_ctor_get(x_22, 5);
x_43 = lean_ctor_get(x_22, 6);
x_44 = lean_ctor_get(x_22, 7);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
lean_inc(x_20);
x_45 = l_List_drop___rarg(x_20, x_39);
lean_dec(x_39);
x_46 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_40);
lean_ctor_set(x_46, 4, x_41);
lean_ctor_set(x_46, 5, x_42);
lean_ctor_set(x_46, 6, x_43);
lean_ctor_set(x_46, 7, x_44);
x_47 = lean_st_ref_set(x_3, x_46, x_23);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes(x_20, x_2, x_3, x_48);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_Elab_Command_elabEnd___closed__3;
x_52 = l_Lean_throwError___at_Lean_Elab_Command_elabEnd___spec__1(x_51, x_2, x_3, x_50);
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
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_st_ref_take(x_3, x_11);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_58, 2);
lean_inc(x_9);
x_62 = l_List_drop___rarg(x_9, x_61);
lean_dec(x_61);
lean_ctor_set(x_58, 2, x_62);
x_63 = lean_st_ref_set(x_3, x_58, x_59);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes(x_9, x_2, x_3, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Elab_Command_elabEnd___lambda__1(x_7, x_10, x_66, x_2, x_3, x_67);
lean_dec(x_66);
lean_dec(x_10);
lean_dec(x_7);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_69 = lean_ctor_get(x_58, 0);
x_70 = lean_ctor_get(x_58, 1);
x_71 = lean_ctor_get(x_58, 2);
x_72 = lean_ctor_get(x_58, 3);
x_73 = lean_ctor_get(x_58, 4);
x_74 = lean_ctor_get(x_58, 5);
x_75 = lean_ctor_get(x_58, 6);
x_76 = lean_ctor_get(x_58, 7);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_58);
lean_inc(x_9);
x_77 = l_List_drop___rarg(x_9, x_71);
lean_dec(x_71);
x_78 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_70);
lean_ctor_set(x_78, 2, x_77);
lean_ctor_set(x_78, 3, x_72);
lean_ctor_set(x_78, 4, x_73);
lean_ctor_set(x_78, 5, x_74);
lean_ctor_set(x_78, 6, x_75);
lean_ctor_set(x_78, 7, x_76);
x_79 = lean_st_ref_set(x_3, x_78, x_59);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_popScopes(x_9, x_2, x_3, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Elab_Command_elabEnd___lambda__1(x_7, x_10, x_82, x_2, x_3, x_83);
lean_dec(x_82);
lean_dec(x_10);
lean_dec(x_7);
return x_84;
}
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabEnd___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabEnd___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Command_elabEnd___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elabEnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabEnd(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEnd___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_end___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_withNamespace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 1;
lean_inc(x_3);
lean_inc(x_1);
x_7 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes(x_6, x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_4);
x_9 = lean_apply_3(x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_take(x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_13, 2);
x_17 = l_Lean_Name_getNumParts(x_1);
lean_dec(x_1);
x_18 = l_List_drop___rarg(x_17, x_16);
lean_dec(x_16);
lean_ctor_set(x_13, 2, x_18);
x_19 = lean_st_ref_set(x_4, x_13, x_14);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_10);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
x_26 = lean_ctor_get(x_13, 2);
x_27 = lean_ctor_get(x_13, 3);
x_28 = lean_ctor_get(x_13, 4);
x_29 = lean_ctor_get(x_13, 5);
x_30 = lean_ctor_get(x_13, 6);
x_31 = lean_ctor_get(x_13, 7);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_32 = l_Lean_Name_getNumParts(x_1);
lean_dec(x_1);
x_33 = l_List_drop___rarg(x_32, x_26);
lean_dec(x_26);
x_34 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_27);
lean_ctor_set(x_34, 4, x_28);
lean_ctor_set(x_34, 5, x_29);
lean_ctor_set(x_34, 6, x_30);
lean_ctor_set(x_34, 7, x_31);
x_35 = lean_st_ref_set(x_4, x_34, x_14);
lean_dec(x_4);
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
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_10);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_4);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
return x_9;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_9, 0);
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_9);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_7);
if (x_43 == 0)
{
return x_7;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_7, 0);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_7);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l_Lean_Elab_Command_withNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withNamespace___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_modifyScope_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_modifyScope_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_modifyScope___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Command");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_modifyScope___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Command.modifyScope");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_modifyScope___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Command_modifyScope___closed__1;
x_2 = l_Lean_Elab_Command_modifyScope___closed__2;
x_3 = lean_unsigned_to_nat(398u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_modifyScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_6, 2);
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Command_modifyScope___closed__3;
x_13 = lean_panic_fn(x_11, x_12);
lean_ctor_set(x_6, 2, x_13);
x_14 = lean_st_ref_set(x_3, x_6, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 5);
x_26 = lean_ctor_get(x_6, 6);
x_27 = lean_ctor_get(x_6, 7);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Command_modifyScope___closed__3;
x_30 = lean_panic_fn(x_28, x_29);
x_31 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_23);
lean_ctor_set(x_31, 4, x_24);
lean_ctor_set(x_31, 5, x_25);
lean_ctor_set(x_31, 6, x_26);
lean_ctor_set(x_31, 7, x_27);
x_32 = lean_st_ref_set(x_3, x_31, x_8);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_6);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_6, 2);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_7);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_7, 0);
x_42 = lean_apply_1(x_1, x_41);
lean_ctor_set(x_7, 0, x_42);
x_43 = lean_st_ref_set(x_3, x_6, x_37);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_7, 0);
x_51 = lean_ctor_get(x_7, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_7);
x_52 = lean_apply_1(x_1, x_50);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_6, 2, x_53);
x_54 = lean_st_ref_set(x_3, x_6, x_37);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_59 = lean_ctor_get(x_6, 0);
x_60 = lean_ctor_get(x_6, 1);
x_61 = lean_ctor_get(x_6, 3);
x_62 = lean_ctor_get(x_6, 4);
x_63 = lean_ctor_get(x_6, 5);
x_64 = lean_ctor_get(x_6, 6);
x_65 = lean_ctor_get(x_6, 7);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_6);
x_66 = lean_ctor_get(x_7, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_7, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_68 = x_7;
} else {
 lean_dec_ref(x_7);
 x_68 = lean_box(0);
}
x_69 = lean_apply_1(x_1, x_66);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_71 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_71, 0, x_59);
lean_ctor_set(x_71, 1, x_60);
lean_ctor_set(x_71, 2, x_70);
lean_ctor_set(x_71, 3, x_61);
lean_ctor_set(x_71, 4, x_62);
lean_ctor_set(x_71, 5, x_63);
lean_ctor_set(x_71, 6, x_64);
lean_ctor_set(x_71, 7, x_65);
x_72 = lean_st_ref_set(x_3, x_71, x_37);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
x_75 = lean_box(0);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_modifyScope(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_getLevelNames___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_Command_getScope___rarg(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 4);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
lean_object* l_Lean_Elab_Command_getLevelNames(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_getLevelNames___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_getLevelNames___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_getLevelNames___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_getLevelNames___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_getLevelNames(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_6, 2);
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Command_modifyScope___closed__3;
x_13 = lean_panic_fn(x_11, x_12);
lean_ctor_set(x_6, 2, x_13);
x_14 = lean_st_ref_set(x_3, x_6, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 5);
x_26 = lean_ctor_get(x_6, 6);
x_27 = lean_ctor_get(x_6, 7);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Command_modifyScope___closed__3;
x_30 = lean_panic_fn(x_28, x_29);
x_31 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_23);
lean_ctor_set(x_31, 4, x_24);
lean_ctor_set(x_31, 5, x_25);
lean_ctor_set(x_31, 6, x_26);
lean_ctor_set(x_31, 7, x_27);
x_32 = lean_st_ref_set(x_3, x_31, x_8);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_7, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_6);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_6, 2);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_7, 1);
x_43 = lean_ctor_get(x_7, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_37, 4);
lean_ctor_set(x_7, 1, x_45);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_37, 4, x_7);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_6, 2, x_46);
x_47 = lean_st_ref_set(x_3, x_6, x_38);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_54 = lean_ctor_get(x_37, 0);
x_55 = lean_ctor_get(x_37, 1);
x_56 = lean_ctor_get(x_37, 2);
x_57 = lean_ctor_get(x_37, 3);
x_58 = lean_ctor_get(x_37, 4);
x_59 = lean_ctor_get(x_37, 5);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_37);
lean_ctor_set(x_7, 1, x_58);
lean_ctor_set(x_7, 0, x_1);
x_60 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_57);
lean_ctor_set(x_60, 4, x_7);
lean_ctor_set(x_60, 5, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_6, 2, x_61);
x_62 = lean_st_ref_set(x_3, x_6, x_38);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_67 = lean_ctor_get(x_7, 1);
lean_inc(x_67);
lean_dec(x_7);
x_68 = lean_ctor_get(x_37, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_37, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_37, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_37, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_37, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_37, 5);
lean_inc(x_73);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_74 = x_37;
} else {
 lean_dec_ref(x_37);
 x_74 = lean_box(0);
}
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_72);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 6, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set(x_76, 1, x_69);
lean_ctor_set(x_76, 2, x_70);
lean_ctor_set(x_76, 3, x_71);
lean_ctor_set(x_76, 4, x_75);
lean_ctor_set(x_76, 5, x_73);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_67);
lean_ctor_set(x_6, 2, x_77);
x_78 = lean_st_ref_set(x_3, x_6, x_38);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = lean_box(0);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_83 = lean_ctor_get(x_6, 0);
x_84 = lean_ctor_get(x_6, 1);
x_85 = lean_ctor_get(x_6, 3);
x_86 = lean_ctor_get(x_6, 4);
x_87 = lean_ctor_get(x_6, 5);
x_88 = lean_ctor_get(x_6, 6);
x_89 = lean_ctor_get(x_6, 7);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_6);
x_90 = lean_ctor_get(x_7, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_91 = x_7;
} else {
 lean_dec_ref(x_7);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_37, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_37, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_37, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_37, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_37, 4);
lean_inc(x_96);
x_97 = lean_ctor_get(x_37, 5);
lean_inc(x_97);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_98 = x_37;
} else {
 lean_dec_ref(x_37);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_91;
}
lean_ctor_set(x_99, 0, x_1);
lean_ctor_set(x_99, 1, x_96);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 6, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_92);
lean_ctor_set(x_100, 1, x_93);
lean_ctor_set(x_100, 2, x_94);
lean_ctor_set(x_100, 3, x_95);
lean_ctor_set(x_100, 4, x_99);
lean_ctor_set(x_100, 5, x_97);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_90);
x_102 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_102, 0, x_83);
lean_ctor_set(x_102, 1, x_84);
lean_ctor_set(x_102, 2, x_101);
lean_ctor_set(x_102, 3, x_85);
lean_ctor_set(x_102, 4, x_86);
lean_ctor_set(x_102, 5, x_87);
lean_ctor_set(x_102, 6, x_88);
lean_ctor_set(x_102, 7, x_89);
x_103 = lean_st_ref_set(x_3, x_102, x_38);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_box(0);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
}
}
}
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__2;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_9, x_2, x_3, x_4);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_addUnivLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = l_Lean_Syntax_getId(x_1);
x_6 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_2, 6);
lean_dec(x_11);
lean_ctor_set(x_2, 6, x_9);
x_12 = l_Lean_Elab_Command_getLevelNames___rarg(x_3, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_5, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(x_5, x_2, x_3, x_14);
lean_dec(x_2);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__2(x_5, x_2, x_3, x_14);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_ctor_get(x_2, 3);
x_22 = lean_ctor_get(x_2, 4);
x_23 = lean_ctor_get(x_2, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_23);
lean_ctor_set(x_24, 6, x_9);
x_25 = l_Lean_Elab_Command_getLevelNames___rarg(x_3, x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_5, x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(x_5, x_24, x_3, x_27);
lean_dec(x_24);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__2(x_5, x_24, x_3, x_27);
return x_30;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addUnivLevel___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_addUnivLevel___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_addUnivLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_addUnivLevel(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabChoiceAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_1, x_2);
lean_inc(x_4);
x_10 = l_Lean_Elab_Command_elabCommand(x_9, x_3, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
x_20 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_21 = lean_nat_dec_eq(x_20, x_19);
lean_dec(x_19);
if (x_21 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_10);
lean_dec(x_11);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
lean_dec(x_2);
x_2 = x_23;
x_5 = x_17;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_dec(x_10);
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
x_27 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_28 = lean_nat_dec_eq(x_27, x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_2, x_30);
lean_dec(x_2);
x_2 = x_31;
x_5 = x_25;
goto _start;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabChoiceAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabChoiceAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elbChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Syntax_getArgs(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Elab_Command_elabChoiceAux(x_5, x_6, x_2, x_3, x_4);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elbChoice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elbChoice(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elbChoice___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elbChoice(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_choiceKind___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Elab_Command_addUnivLevel(x_6, x_2, x_3, x_4);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elabUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabUniverse(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabUniverse___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_universe___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverses___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_2 == x_3;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_10 = l_Lean_Elab_Command_addUnivLevel(x_9, x_5, x_6, x_7);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = x_2 + x_13;
x_2 = x_14;
x_4 = x_11;
x_7 = x_12;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_5);
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
else
{
lean_object* x_20; 
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
}
lean_object* l_Lean_Elab_Command_elabUniverses(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
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
lean_dec(x_7);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverses___spec__1(x_7, x_16, x_17, x_18, x_2, x_3, x_4);
lean_dec(x_7);
return x_19;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverses___spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabUniverses___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabUniverses(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabUniverses___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_universes___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabInitQuot_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Command_elabInitQuot_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInitQuot_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_1);
x_10 = lean_st_ref_set(x_3, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_ctor_get(x_6, 3);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 5);
x_22 = lean_ctor_get(x_6, 6);
x_23 = lean_ctor_get(x_6, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_20);
lean_ctor_set(x_24, 5, x_21);
lean_ctor_set(x_24, 6, x_22);
lean_ctor_set(x_24, 7, x_23);
x_25 = lean_st_ref_set(x_3, x_24, x_7);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
lean_object* l_Lean_Elab_Command_elabInitQuot___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(4);
x_9 = lean_add_decl(x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_2, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_head_x21___at_Lean_Elab_Command_instMonadOptionsCommandElabM___spec__1(x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_KernelException_toMessageData(x_10, x_16);
x_18 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_17, x_1, x_2, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_19, x_1, x_2, x_6);
lean_dec(x_1);
return x_20;
}
}
}
lean_object* l_Lean_Elab_Command_elabInitQuot(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInitQuot___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabInitQuot___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabInitQuot___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabInitQuot___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabInitQuot(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInitQuot___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_init__quot___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_logUnknownDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addClass___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_logUnknownDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_Command_logUnknownDecl___closed__1;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_KernelException_toMessageData___closed__3;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = 2;
x_11 = l_Lean_Elab_log___at_Lean_Elab_Command_withLogging___spec__3(x_9, x_10, x_2, x_3, x_4);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_logUnknownDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_logUnknownDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_getScope___rarg(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getScope___rarg(x_3, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_1);
x_18 = l_Lean_ResolveName_resolveNamespace_x3f(x_8, x_12, x_17, x_1);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_13);
x_19 = l_Lean_Name_toString___closed__1;
x_20 = l_Lean_Name_toStringWithSep(x_19, x_1);
x_21 = l_Lean_resolveNamespace___rarg___lambda__1___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Char_quote___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__2(x_26, x_2, x_3, x_16);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
lean_ctor_set(x_13, 0, x_28);
return x_13;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_ctor_get(x_29, 3);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_1);
x_32 = l_Lean_ResolveName_resolveNamespace_x3f(x_8, x_12, x_31, x_1);
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_8);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = l_Lean_Name_toString___closed__1;
x_34 = l_Lean_Name_toStringWithSep(x_33, x_1);
x_35 = l_Lean_resolveNamespace___rarg___lambda__1___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Char_quote___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__2(x_40, x_2, x_3, x_30);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_30);
return x_43;
}
}
}
}
lean_object* l_List_foldl___at_Lean_Elab_Command_elabExport___spec__3(lean_object* x_1, lean_object* x_2) {
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
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_add_alias(x_1, x_5, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabExport___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_5 == x_6;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_uget(x_4, x_5);
x_13 = l_Lean_Syntax_getId(x_12);
lean_inc(x_13);
x_14 = l_Lean_Name_append(x_1, x_13);
lean_inc(x_3);
x_15 = l_Lean_Environment_contains(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
lean_dec(x_13);
x_16 = l_Lean_Elab_Command_getRef(x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_replaceRef(x_12, x_17);
lean_dec(x_17);
lean_dec(x_12);
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 2);
x_23 = lean_ctor_get(x_8, 3);
x_24 = lean_ctor_get(x_8, 4);
x_25 = lean_ctor_get(x_8, 5);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_26 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set(x_26, 4, x_24);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_26, 6, x_19);
x_27 = l_Lean_Elab_Command_logUnknownDecl(x_14, x_26, x_9, x_18);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = 1;
x_30 = x_5 + x_29;
x_5 = x_30;
x_10 = x_28;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; 
lean_dec(x_12);
x_32 = l_Lean_Name_append(x_2, x_13);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_14);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
x_35 = 1;
x_36 = x_5 + x_35;
x_5 = x_36;
x_7 = x_34;
goto _start;
}
}
else
{
lean_object* x_38; 
lean_dec(x_3);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_7);
lean_ctor_set(x_38, 1, x_10);
return x_38;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
lean_object* l_Lean_Elab_Command_elabExport___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_39 = lean_st_ref_get(x_6, x_7);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_unsigned_to_nat(3u);
x_44 = l_Lean_Syntax_getArg(x_1, x_43);
x_45 = l_Lean_Syntax_getArgs(x_44);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = lean_array_get_size(x_45);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_lt(x_48, x_47);
if (x_49 == 0)
{
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_42);
x_8 = x_46;
x_9 = x_41;
goto block_38;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_47, x_47);
if (x_50 == 0)
{
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_42);
x_8 = x_46;
x_9 = x_41;
goto block_38;
}
else
{
size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = 0;
x_52 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_53 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabExport___spec__4(x_2, x_3, x_42, x_45, x_51, x_52, x_46, x_5, x_6, x_41);
lean_dec(x_45);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_8 = x_54;
x_9 = x_55;
goto block_38;
}
}
block_38:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_6, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = l_List_foldl___at_Lean_Elab_Command_elabExport___spec__3(x_14, x_8);
lean_ctor_set(x_11, 0, x_15);
x_16 = lean_st_ref_set(x_6, x_11, x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get(x_11, 4);
x_28 = lean_ctor_get(x_11, 5);
x_29 = lean_ctor_get(x_11, 6);
x_30 = lean_ctor_get(x_11, 7);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_31 = l_List_foldl___at_Lean_Elab_Command_elabExport___spec__3(x_23, x_8);
x_32 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_26);
lean_ctor_set(x_32, 4, x_27);
lean_ctor_set(x_32, 5, x_28);
lean_ctor_set(x_32, 6, x_29);
lean_ctor_set(x_32, 7, x_30);
x_33 = lean_st_ref_set(x_6, x_32, x_12);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'export', self export");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabExport___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabExport___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabExport___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabExport___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabExport(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getId(x_6);
lean_dec(x_6);
lean_inc(x_2);
x_8 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(x_7, x_2, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Command_getScope___rarg(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_name_eq(x_9, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Command_elabExport___lambda__1(x_1, x_9, x_14, x_16, x_2, x_3, x_13);
lean_dec(x_2);
lean_dec(x_14);
lean_dec(x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_9);
x_18 = l_Lean_Elab_Command_elabExport___closed__3;
x_19 = l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__5(x_18, x_2, x_3, x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
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
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
return x_8;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabExport___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabExport___spec__4(x_1, x_2, x_3, x_4, x_11, x_12, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabExport___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Command_elabExport___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_elabExport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabExport(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabExport___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabExport(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_export___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Command_elabExport___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_6, 2);
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Command_modifyScope___closed__3;
x_13 = lean_panic_fn(x_11, x_12);
lean_ctor_set(x_6, 2, x_13);
x_14 = lean_st_ref_set(x_3, x_6, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 5);
x_26 = lean_ctor_get(x_6, 6);
x_27 = lean_ctor_get(x_6, 7);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Command_modifyScope___closed__3;
x_30 = lean_panic_fn(x_28, x_29);
x_31 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_23);
lean_ctor_set(x_31, 4, x_24);
lean_ctor_set(x_31, 5, x_25);
lean_ctor_set(x_31, 6, x_26);
lean_ctor_set(x_31, 7, x_27);
x_32 = lean_st_ref_set(x_3, x_31, x_8);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_7, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_6);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_6, 2);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_7, 1);
x_43 = lean_ctor_get(x_7, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_37, 3);
lean_ctor_set(x_7, 1, x_45);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_37, 3, x_7);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_6, 2, x_46);
x_47 = lean_st_ref_set(x_3, x_6, x_38);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_54 = lean_ctor_get(x_37, 0);
x_55 = lean_ctor_get(x_37, 1);
x_56 = lean_ctor_get(x_37, 2);
x_57 = lean_ctor_get(x_37, 3);
x_58 = lean_ctor_get(x_37, 4);
x_59 = lean_ctor_get(x_37, 5);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_37);
lean_ctor_set(x_7, 1, x_57);
lean_ctor_set(x_7, 0, x_1);
x_60 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_7);
lean_ctor_set(x_60, 4, x_58);
lean_ctor_set(x_60, 5, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_6, 2, x_61);
x_62 = lean_st_ref_set(x_3, x_6, x_38);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_67 = lean_ctor_get(x_7, 1);
lean_inc(x_67);
lean_dec(x_7);
x_68 = lean_ctor_get(x_37, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_37, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_37, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_37, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_37, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_37, 5);
lean_inc(x_73);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_74 = x_37;
} else {
 lean_dec_ref(x_37);
 x_74 = lean_box(0);
}
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_71);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 6, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set(x_76, 1, x_69);
lean_ctor_set(x_76, 2, x_70);
lean_ctor_set(x_76, 3, x_75);
lean_ctor_set(x_76, 4, x_72);
lean_ctor_set(x_76, 5, x_73);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_67);
lean_ctor_set(x_6, 2, x_77);
x_78 = lean_st_ref_set(x_3, x_6, x_38);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = lean_box(0);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_83 = lean_ctor_get(x_6, 0);
x_84 = lean_ctor_get(x_6, 1);
x_85 = lean_ctor_get(x_6, 3);
x_86 = lean_ctor_get(x_6, 4);
x_87 = lean_ctor_get(x_6, 5);
x_88 = lean_ctor_get(x_6, 6);
x_89 = lean_ctor_get(x_6, 7);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_6);
x_90 = lean_ctor_get(x_7, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_91 = x_7;
} else {
 lean_dec_ref(x_7);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_37, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_37, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_37, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_37, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_37, 4);
lean_inc(x_96);
x_97 = lean_ctor_get(x_37, 5);
lean_inc(x_97);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_98 = x_37;
} else {
 lean_dec_ref(x_37);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_91;
}
lean_ctor_set(x_99, 0, x_1);
lean_ctor_set(x_99, 1, x_95);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 6, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_92);
lean_ctor_set(x_100, 1, x_93);
lean_ctor_set(x_100, 2, x_94);
lean_ctor_set(x_100, 3, x_99);
lean_ctor_set(x_100, 4, x_96);
lean_ctor_set(x_100, 5, x_97);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_90);
x_102 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_102, 0, x_83);
lean_ctor_set(x_102, 1, x_84);
lean_ctor_set(x_102, 2, x_101);
lean_ctor_set(x_102, 3, x_85);
lean_ctor_set(x_102, 4, x_86);
lean_ctor_set(x_102, 5, x_87);
lean_ctor_set(x_102, 6, x_88);
lean_ctor_set(x_102, 7, x_89);
x_103 = lean_st_ref_set(x_3, x_102, x_38);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_box(0);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
}
}
}
lean_object* l_Lean_Elab_Command_addOpenDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_addOpenDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_addOpenDecl(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenSimple___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_2 == x_3;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_9 = lean_array_uget(x_1, x_2);
x_10 = l_Lean_Syntax_getId(x_9);
lean_dec(x_9);
lean_inc(x_5);
x_11 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(x_10, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
lean_inc(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_15, x_5, x_6, x_13);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_activateScoped___at___private_Lean_Elab_Command_0__Lean_Elab_Command_addScope___spec__3(x_12, x_5, x_6, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = x_2 + x_21;
x_2 = x_22;
x_4 = x_19;
x_7 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_7);
return x_28;
}
}
}
lean_object* l_Lean_Elab_Command_elabOpenSimple(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_instInhabitedSyntax;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get(x_6, x_5, x_7);
x_9 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_10 = lean_array_get_size(x_9);
x_11 = lean_nat_dec_lt(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_10, x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_19 = lean_box(0);
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenSimple___spec__1(x_9, x_17, x_18, x_19, x_2, x_3, x_4);
lean_dec(x_9);
return x_20;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenSimple___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenSimple___spec__1(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabOpenSimple___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabOpenSimple(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenOnly___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_3 == x_4;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_5);
x_10 = lean_array_uget(x_2, x_3);
x_11 = l_Lean_Syntax_getId(x_10);
lean_inc(x_11);
x_12 = l_Lean_Name_append(x_1, x_11);
x_13 = lean_st_ref_get(x_7, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Environment_contains(x_16, x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_11);
x_18 = l_Lean_Elab_Command_getRef(x_6, x_7, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_replaceRef(x_10, x_19);
lean_dec(x_19);
lean_dec(x_10);
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
x_24 = lean_ctor_get(x_6, 2);
x_25 = lean_ctor_get(x_6, 3);
x_26 = lean_ctor_get(x_6, 4);
x_27 = lean_ctor_get(x_6, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_28 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_25);
lean_ctor_set(x_28, 4, x_26);
lean_ctor_set(x_28, 5, x_27);
lean_ctor_set(x_28, 6, x_21);
x_29 = l_Lean_Elab_Command_logUnknownDecl(x_12, x_28, x_7, x_20);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = 1;
x_33 = x_3 + x_32;
x_3 = x_33;
x_5 = x_30;
x_8 = x_31;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; 
lean_dec(x_10);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_11);
lean_ctor_set(x_35, 1, x_12);
x_36 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_35, x_6, x_7, x_15);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = 1;
x_40 = x_3 + x_39;
x_3 = x_40;
x_5 = x_37;
x_8 = x_38;
goto _start;
}
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_5);
lean_ctor_set(x_42, 1, x_8);
return x_42;
}
}
}
lean_object* l_Lean_Elab_Command_elabOpenOnly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_instInhabitedSyntax;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get(x_6, x_5, x_7);
x_9 = l_Lean_Syntax_getId(x_8);
lean_dec(x_8);
lean_inc(x_2);
x_10 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(x_9, x_2, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_array_get(x_6, x_5, x_14);
x_16 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_17 = lean_array_get_size(x_16);
x_18 = lean_nat_dec_lt(x_7, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_2);
x_19 = lean_box(0);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_17, x_17);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_2);
x_21 = lean_box(0);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_10);
x_22 = 0;
x_23 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenOnly___spec__1(x_12, x_16, x_22, x_23, x_24, x_2, x_3, x_13);
lean_dec(x_2);
lean_dec(x_16);
lean_dec(x_12);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_array_get(x_6, x_5, x_28);
x_30 = l_Lean_Syntax_getArgs(x_29);
lean_dec(x_29);
x_31 = lean_array_get_size(x_30);
x_32 = lean_nat_dec_lt(x_7, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_31, x_31);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_40 = lean_box(0);
x_41 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenOnly___spec__1(x_26, x_30, x_38, x_39, x_40, x_2, x_3, x_27);
lean_dec(x_2);
lean_dec(x_30);
lean_dec(x_26);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
return x_10;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_10);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenOnly___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenOnly___spec__1(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_elabOpenOnly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabOpenOnly(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenHiding___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_4 == x_5;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_3, x_4);
x_12 = l_Lean_Syntax_getId(x_11);
lean_inc(x_12);
x_13 = l_Lean_Name_append(x_1, x_12);
lean_inc(x_2);
x_14 = l_Lean_Environment_contains(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; 
lean_dec(x_12);
x_15 = l_Lean_Elab_Command_getRef(x_7, x_8, x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_replaceRef(x_11, x_16);
lean_dec(x_16);
lean_dec(x_11);
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
x_21 = lean_ctor_get(x_7, 2);
x_22 = lean_ctor_get(x_7, 3);
x_23 = lean_ctor_get(x_7, 4);
x_24 = lean_ctor_get(x_7, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_25 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_24);
lean_ctor_set(x_25, 6, x_18);
x_26 = l_Lean_Elab_Command_logUnknownDecl(x_13, x_25, x_8, x_17);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = 1;
x_29 = x_4 + x_28;
x_4 = x_29;
x_9 = x_27;
goto _start;
}
else
{
lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_13);
lean_dec(x_11);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_6);
x_32 = 1;
x_33 = x_4 + x_32;
x_4 = x_33;
x_6 = x_31;
goto _start;
}
}
else
{
lean_object* x_35; 
lean_dec(x_2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_6);
lean_ctor_set(x_35, 1, x_9);
return x_35;
}
}
}
lean_object* l_Lean_Elab_Command_elabOpenHiding(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_instInhabitedSyntax;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get(x_6, x_5, x_7);
x_9 = l_Lean_Syntax_getId(x_8);
lean_dec(x_8);
lean_inc(x_2);
x_10 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(x_9, x_2, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_array_get(x_6, x_5, x_16);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_21 = lean_array_get_size(x_20);
x_22 = lean_nat_dec_lt(x_7, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_19);
x_24 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_23, x_2, x_3, x_15);
lean_dec(x_2);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_21, x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_19);
x_27 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_26, x_2, x_3, x_15);
lean_dec(x_2);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_30 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenHiding___spec__1(x_11, x_18, x_20, x_28, x_29, x_19, x_2, x_3, x_15);
lean_dec(x_20);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_33, x_2, x_3, x_32);
lean_dec(x_2);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
return x_10;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_10);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenHiding___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenHiding___spec__1(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Command_elabOpenHiding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabOpenHiding(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenRenaming___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_3 == x_4;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_5);
x_10 = lean_array_uget(x_2, x_3);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getIdAt(x_10, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getIdAt(x_10, x_13);
x_15 = l_Lean_Name_append(x_1, x_12);
x_16 = lean_st_ref_get(x_7, x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Environment_contains(x_19, x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; 
lean_dec(x_14);
x_21 = l_Lean_Elab_Command_getRef(x_6, x_7, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_replaceRef(x_10, x_22);
lean_dec(x_22);
lean_dec(x_10);
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
x_27 = lean_ctor_get(x_6, 2);
x_28 = lean_ctor_get(x_6, 3);
x_29 = lean_ctor_get(x_6, 4);
x_30 = lean_ctor_get(x_6, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_31 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_28);
lean_ctor_set(x_31, 4, x_29);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_24);
x_32 = l_Lean_Elab_Command_logUnknownDecl(x_15, x_31, x_7, x_23);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = 1;
x_36 = x_3 + x_35;
x_3 = x_36;
x_5 = x_33;
x_8 = x_34;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; 
lean_dec(x_10);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_14);
lean_ctor_set(x_38, 1, x_15);
x_39 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_addOpenDecl___spec__1(x_38, x_6, x_7, x_18);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = 1;
x_43 = x_3 + x_42;
x_3 = x_43;
x_5 = x_40;
x_8 = x_41;
goto _start;
}
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_8);
return x_45;
}
}
}
lean_object* l_Lean_Elab_Command_elabOpenRenaming(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_instInhabitedSyntax;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get(x_6, x_5, x_7);
x_9 = l_Lean_Syntax_getId(x_8);
lean_dec(x_8);
lean_inc(x_2);
x_10 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(x_9, x_2, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_array_get(x_6, x_5, x_14);
x_16 = l_Lean_Syntax_getSepArgs(x_15);
lean_dec(x_15);
x_17 = lean_array_get_size(x_16);
x_18 = lean_nat_dec_lt(x_7, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_2);
x_19 = lean_box(0);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_17, x_17);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_2);
x_21 = lean_box(0);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_10);
x_22 = 0;
x_23 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenRenaming___spec__1(x_12, x_16, x_22, x_23, x_24, x_2, x_3, x_13);
lean_dec(x_2);
lean_dec(x_16);
lean_dec(x_12);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_array_get(x_6, x_5, x_28);
x_30 = l_Lean_Syntax_getSepArgs(x_29);
lean_dec(x_29);
x_31 = lean_array_get_size(x_30);
x_32 = lean_nat_dec_lt(x_7, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_31, x_31);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_40 = lean_box(0);
x_41 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenRenaming___spec__1(x_26, x_30, x_38, x_39, x_40, x_2, x_3, x_27);
lean_dec(x_2);
lean_dec(x_30);
lean_dec(x_26);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
return x_10;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_10);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenRenaming___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabOpenRenaming___spec__1(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_elabOpenRenaming___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabOpenRenaming(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabOpen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_asNode(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = l_Lean_Parser_Command_openSimple___elambda__1___closed__2;
x_10 = lean_name_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Parser_Command_openOnly___elambda__1___closed__2;
x_12 = lean_name_eq(x_8, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Parser_Command_openHiding___elambda__1___closed__2;
x_14 = lean_name_eq(x_8, x_13);
lean_dec(x_8);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Command_elabOpenRenaming(x_7, x_2, x_3, x_4);
lean_dec(x_7);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Command_elabOpenHiding(x_7, x_2, x_3, x_4);
lean_dec(x_7);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_8);
x_17 = l_Lean_Elab_Command_elabOpenOnly(x_7, x_2, x_3, x_4);
lean_dec(x_7);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_8);
x_18 = l_Lean_Elab_Command_elabOpenSimple(x_7, x_2, x_3, x_4);
lean_dec(x_7);
return x_18;
}
}
}
lean_object* l_Lean_Elab_Command_elabOpen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabOpen(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabOpen___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_open___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_6, 2);
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Command_modifyScope___closed__3;
x_13 = lean_panic_fn(x_11, x_12);
lean_ctor_set(x_6, 2, x_13);
x_14 = lean_st_ref_set(x_3, x_6, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 5);
x_26 = lean_ctor_get(x_6, 6);
x_27 = lean_ctor_get(x_6, 7);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Command_modifyScope___closed__3;
x_30 = lean_panic_fn(x_28, x_29);
x_31 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_23);
lean_ctor_set(x_31, 4, x_24);
lean_ctor_set(x_31, 5, x_25);
lean_ctor_set(x_31, 6, x_26);
lean_ctor_set(x_31, 7, x_27);
x_32 = lean_st_ref_set(x_3, x_31, x_8);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_7, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_6);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_6, 2);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_7, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_37, 5);
x_45 = lean_array_push(x_44, x_1);
lean_ctor_set(x_37, 5, x_45);
x_46 = lean_st_ref_set(x_3, x_6, x_38);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_53 = lean_ctor_get(x_37, 0);
x_54 = lean_ctor_get(x_37, 1);
x_55 = lean_ctor_get(x_37, 2);
x_56 = lean_ctor_get(x_37, 3);
x_57 = lean_ctor_get(x_37, 4);
x_58 = lean_ctor_get(x_37, 5);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_37);
x_59 = lean_array_push(x_58, x_1);
x_60 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_54);
lean_ctor_set(x_60, 2, x_55);
lean_ctor_set(x_60, 3, x_56);
lean_ctor_set(x_60, 4, x_57);
lean_ctor_set(x_60, 5, x_59);
lean_ctor_set(x_7, 0, x_60);
x_61 = lean_st_ref_set(x_3, x_6, x_38);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_66 = lean_ctor_get(x_7, 1);
lean_inc(x_66);
lean_dec(x_7);
x_67 = lean_ctor_get(x_37, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_37, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_37, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_37, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_37, 4);
lean_inc(x_71);
x_72 = lean_ctor_get(x_37, 5);
lean_inc(x_72);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_73 = x_37;
} else {
 lean_dec_ref(x_37);
 x_73 = lean_box(0);
}
x_74 = lean_array_push(x_72, x_1);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 6, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_68);
lean_ctor_set(x_75, 2, x_69);
lean_ctor_set(x_75, 3, x_70);
lean_ctor_set(x_75, 4, x_71);
lean_ctor_set(x_75, 5, x_74);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_66);
lean_ctor_set(x_6, 2, x_76);
x_77 = lean_st_ref_set(x_3, x_6, x_38);
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
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_82 = lean_ctor_get(x_6, 0);
x_83 = lean_ctor_get(x_6, 1);
x_84 = lean_ctor_get(x_6, 3);
x_85 = lean_ctor_get(x_6, 4);
x_86 = lean_ctor_get(x_6, 5);
x_87 = lean_ctor_get(x_6, 6);
x_88 = lean_ctor_get(x_6, 7);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_6);
x_89 = lean_ctor_get(x_7, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_90 = x_7;
} else {
 lean_dec_ref(x_7);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_37, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_37, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_37, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_37, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_37, 4);
lean_inc(x_95);
x_96 = lean_ctor_get(x_37, 5);
lean_inc(x_96);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_97 = x_37;
} else {
 lean_dec_ref(x_37);
 x_97 = lean_box(0);
}
x_98 = lean_array_push(x_96, x_1);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 6, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_91);
lean_ctor_set(x_99, 1, x_92);
lean_ctor_set(x_99, 2, x_93);
lean_ctor_set(x_99, 3, x_94);
lean_ctor_set(x_99, 4, x_95);
lean_ctor_set(x_99, 5, x_98);
if (lean_is_scalar(x_90)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_90;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_89);
x_101 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_101, 0, x_82);
lean_ctor_set(x_101, 1, x_83);
lean_ctor_set(x_101, 2, x_100);
lean_ctor_set(x_101, 3, x_84);
lean_ctor_set(x_101, 4, x_85);
lean_ctor_set(x_101, 5, x_86);
lean_ctor_set(x_101, 6, x_87);
lean_ctor_set(x_101, 7, x_88);
x_102 = lean_st_ref_set(x_3, x_101, x_38);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_box(0);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabVariable___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariable___lambda__1___boxed), 8, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Command_elabVariable___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Elab_Term_resetMessageLog(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_3);
x_12 = l_Lean_Elab_Term_addAutoBoundImplicits(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Elab_Command_elabVariable___lambda__2___closed__1;
x_15 = 1;
x_16 = lean_box(x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinder___rarg___boxed), 10, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_16);
x_18 = lean_box(x_15);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg___boxed), 9, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = 0;
x_21 = l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg(x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabVariable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_box(0);
x_8 = lean_st_ref_get(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_9);
lean_dec(x_9);
lean_inc(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariable___lambda__2___boxed), 9, 1);
lean_closure_set(x_12, 0, x_6);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 10, 3);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_14);
x_16 = lean_box(x_13);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg___boxed), 9, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
lean_inc(x_2);
x_18 = l_Lean_Elab_Command_liftTermElabM___rarg(x_7, x_17, x_2, x_3, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(x_6, x_2, x_3, x_19);
lean_dec(x_2);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariable___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabVariable___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_elabVariable___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_elabVariable___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabVariable___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabVariable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabVariable(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariable___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_variable___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_6, 2);
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Command_modifyScope___closed__3;
x_13 = lean_panic_fn(x_11, x_12);
lean_ctor_set(x_6, 2, x_13);
x_14 = lean_st_ref_set(x_3, x_6, x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 5);
x_26 = lean_ctor_get(x_6, 6);
x_27 = lean_ctor_get(x_6, 7);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Command_modifyScope___closed__3;
x_30 = lean_panic_fn(x_28, x_29);
x_31 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_23);
lean_ctor_set(x_31, 4, x_24);
lean_ctor_set(x_31, 5, x_25);
lean_ctor_set(x_31, 6, x_26);
lean_ctor_set(x_31, 7, x_27);
x_32 = lean_st_ref_set(x_3, x_31, x_8);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_7, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_6);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_6, 2);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_7, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_37, 5);
x_45 = l_Array_append___rarg(x_44, x_1);
lean_ctor_set(x_37, 5, x_45);
x_46 = lean_st_ref_set(x_3, x_6, x_38);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_53 = lean_ctor_get(x_37, 0);
x_54 = lean_ctor_get(x_37, 1);
x_55 = lean_ctor_get(x_37, 2);
x_56 = lean_ctor_get(x_37, 3);
x_57 = lean_ctor_get(x_37, 4);
x_58 = lean_ctor_get(x_37, 5);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_37);
x_59 = l_Array_append___rarg(x_58, x_1);
x_60 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_54);
lean_ctor_set(x_60, 2, x_55);
lean_ctor_set(x_60, 3, x_56);
lean_ctor_set(x_60, 4, x_57);
lean_ctor_set(x_60, 5, x_59);
lean_ctor_set(x_7, 0, x_60);
x_61 = lean_st_ref_set(x_3, x_6, x_38);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_66 = lean_ctor_get(x_7, 1);
lean_inc(x_66);
lean_dec(x_7);
x_67 = lean_ctor_get(x_37, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_37, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_37, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_37, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_37, 4);
lean_inc(x_71);
x_72 = lean_ctor_get(x_37, 5);
lean_inc(x_72);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_73 = x_37;
} else {
 lean_dec_ref(x_37);
 x_73 = lean_box(0);
}
x_74 = l_Array_append___rarg(x_72, x_1);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 6, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_67);
lean_ctor_set(x_75, 1, x_68);
lean_ctor_set(x_75, 2, x_69);
lean_ctor_set(x_75, 3, x_70);
lean_ctor_set(x_75, 4, x_71);
lean_ctor_set(x_75, 5, x_74);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_66);
lean_ctor_set(x_6, 2, x_76);
x_77 = lean_st_ref_set(x_3, x_6, x_38);
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
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_82 = lean_ctor_get(x_6, 0);
x_83 = lean_ctor_get(x_6, 1);
x_84 = lean_ctor_get(x_6, 3);
x_85 = lean_ctor_get(x_6, 4);
x_86 = lean_ctor_get(x_6, 5);
x_87 = lean_ctor_get(x_6, 6);
x_88 = lean_ctor_get(x_6, 7);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_6);
x_89 = lean_ctor_get(x_7, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_90 = x_7;
} else {
 lean_dec_ref(x_7);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_37, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_37, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_37, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_37, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_37, 4);
lean_inc(x_95);
x_96 = lean_ctor_get(x_37, 5);
lean_inc(x_96);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_97 = x_37;
} else {
 lean_dec_ref(x_37);
 x_97 = lean_box(0);
}
x_98 = l_Array_append___rarg(x_96, x_1);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 6, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_91);
lean_ctor_set(x_99, 1, x_92);
lean_ctor_set(x_99, 2, x_93);
lean_ctor_set(x_99, 3, x_94);
lean_ctor_set(x_99, 4, x_95);
lean_ctor_set(x_99, 5, x_98);
if (lean_is_scalar(x_90)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_90;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_89);
x_101 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_101, 0, x_82);
lean_ctor_set(x_101, 1, x_83);
lean_ctor_set(x_101, 2, x_100);
lean_ctor_set(x_101, 3, x_84);
lean_ctor_set(x_101, 4, x_85);
lean_ctor_set(x_101, 5, x_86);
lean_ctor_set(x_101, 6, x_87);
lean_ctor_set(x_101, 7, x_88);
x_102 = lean_st_ref_set(x_3, x_101, x_38);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_box(0);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Elab_Term_resetMessageLog(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_3);
x_12 = l_Lean_Elab_Term_addAutoBoundImplicits(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Elab_Command_elabVariable___lambda__2___closed__1;
x_15 = 1;
x_16 = lean_box(x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 10, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_16);
x_18 = lean_box(x_15);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg___boxed), 9, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = 0;
x_21 = l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg(x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabVariables(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_st_ref_get(x_3, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_10);
lean_dec(x_10);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariables___lambda__1___boxed), 9, 1);
lean_closure_set(x_13, 0, x_7);
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 10, 3);
lean_closure_set(x_16, 0, x_12);
lean_closure_set(x_16, 1, x_13);
lean_closure_set(x_16, 2, x_15);
x_17 = lean_box(x_14);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg___boxed), 9, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
lean_inc(x_2);
x_19 = l_Lean_Elab_Command_liftTermElabM___rarg(x_8, x_18, x_2, x_3, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(x_7, x_2, x_3, x_20);
lean_dec(x_2);
lean_dec(x_7);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabVariables___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabVariables___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabVariables___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabVariables___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabVariables(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariables___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabVariables(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_variables___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabCheck_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Command_elabCheck_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheck_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Meta_instantiateMVars(x_2, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Elab_Term_levelMVarToParam(x_15, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_21);
x_22 = l_Lean_Meta_inferType(x_21, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = l_Lean_Expr_isSyntheticSorry(x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
lean_free_object(x_22);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_21);
x_28 = l_Lean_KernelException_toMessageData___closed__15;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_24);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
x_35 = 0;
x_36 = l_Lean_Elab_logAt___at_Lean_Elab_Term_traceAtCmdPos___spec__3(x_1, x_34, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_36;
}
else
{
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_22, 0, x_11);
return x_22;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
x_39 = l_Lean_Expr_isSyntheticSorry(x_21);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_21);
x_41 = l_Lean_KernelException_toMessageData___closed__15;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_37);
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
x_48 = 0;
x_49 = l_Lean_Elab_logAt___at_Lean_Elab_Term_traceAtCmdPos___spec__3(x_1, x_47, x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_11);
lean_ctor_set(x_50, 1, x_38);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
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
x_55 = !lean_is_exclusive(x_14);
if (x_55 == 0)
{
return x_14;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_14, 0);
x_57 = lean_ctor_get(x_14, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_14);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_12);
if (x_59 == 0)
{
return x_12;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_12, 0);
x_61 = lean_ctor_get(x_12, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_12);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabCheck___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Elab_Term_resetMessageLog(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_4);
x_13 = l_Lean_Elab_Term_addAutoBoundImplicits(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 10, 3);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_15);
lean_closure_set(x_18, 2, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheck___lambda__1___boxed), 9, 1);
lean_closure_set(x_19, 0, x_2);
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg), 9, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = 0;
x_22 = l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg(x_20, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
static lean_object* _init_l_Lean_Elab_Command_elabCheck___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1128____closed__3;
x_2 = l_Lean_Meta_check___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheck___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_check");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheck___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabCheck___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheck___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabCheck___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabCheck___closed__1;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_st_ref_get(x_3, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_3, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_17);
lean_dec(x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheck___lambda__2___boxed), 10, 2);
lean_closure_set(x_20, 0, x_11);
lean_closure_set(x_20, 1, x_9);
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 10, 3);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_20);
lean_closure_set(x_23, 2, x_22);
x_24 = lean_box(x_21);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg___boxed), 9, 2);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_Command_elabCheck___closed__4;
lean_inc(x_2);
x_27 = l_Lean_Elab_Command_liftTermElabM___rarg(x_26, x_25, x_2, x_3, x_18);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_15, x_2, x_3, x_29);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
x_37 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_15, x_2, x_3, x_36);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabCheck___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabCheck___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabCheck___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabCheck___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_elabCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabCheck(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheck___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Elab_Command_elabCheck___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabReduce_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Command_elabReduce_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabReduce_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabReduce___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Meta_instantiateMVars(x_2, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Elab_Term_levelMVarToParam(x_15, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_7);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__2;
x_25 = l_Lean_KVMap_setBool(x_23, x_24, x_10);
lean_ctor_set(x_7, 0, x_25);
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_5, 2);
lean_inc(x_28);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_30 = 0;
lean_ctor_set_uint8(x_26, 5, x_30);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_28);
x_32 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_33 = l_Lean_Meta_reduce(x_21, x_32, x_10, x_10, x_31, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_34);
x_37 = 0;
x_38 = l_Lean_Elab_logAt___at_Lean_Elab_Term_traceAtCmdPos___spec__3(x_1, x_36, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_43 = lean_ctor_get_uint8(x_26, 0);
x_44 = lean_ctor_get_uint8(x_26, 1);
x_45 = lean_ctor_get_uint8(x_26, 2);
x_46 = lean_ctor_get_uint8(x_26, 3);
x_47 = lean_ctor_get_uint8(x_26, 4);
x_48 = lean_ctor_get_uint8(x_26, 6);
x_49 = lean_ctor_get_uint8(x_26, 7);
x_50 = lean_ctor_get_uint8(x_26, 8);
lean_dec(x_26);
x_51 = 0;
x_52 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_52, 0, x_43);
lean_ctor_set_uint8(x_52, 1, x_44);
lean_ctor_set_uint8(x_52, 2, x_45);
lean_ctor_set_uint8(x_52, 3, x_46);
lean_ctor_set_uint8(x_52, 4, x_47);
lean_ctor_set_uint8(x_52, 5, x_51);
lean_ctor_set_uint8(x_52, 6, x_48);
lean_ctor_set_uint8(x_52, 7, x_49);
lean_ctor_set_uint8(x_52, 8, x_50);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_27);
lean_ctor_set(x_53, 2, x_28);
x_54 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_55 = l_Lean_Meta_reduce(x_21, x_54, x_10, x_10, x_53, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_58, 0, x_56);
x_59 = 0;
x_60 = l_Lean_Elab_logAt___at_Lean_Elab_Term_traceAtCmdPos___spec__3(x_1, x_58, x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_57);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_63 = x_55;
} else {
 lean_dec_ref(x_55);
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
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_65 = lean_ctor_get(x_7, 0);
x_66 = lean_ctor_get(x_7, 1);
x_67 = lean_ctor_get(x_7, 2);
x_68 = lean_ctor_get(x_7, 3);
x_69 = lean_ctor_get(x_7, 4);
x_70 = lean_ctor_get(x_7, 5);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_7);
x_71 = l_Lean_Meta_initFn____x40_Lean_Meta_WHNF___hyg_15____closed__2;
x_72 = l_Lean_KVMap_setBool(x_65, x_71, x_10);
x_73 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_66);
lean_ctor_set(x_73, 2, x_67);
lean_ctor_set(x_73, 3, x_68);
lean_ctor_set(x_73, 4, x_69);
lean_ctor_set(x_73, 5, x_70);
x_74 = lean_ctor_get(x_5, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_5, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_5, 2);
lean_inc(x_76);
x_77 = lean_ctor_get_uint8(x_74, 0);
x_78 = lean_ctor_get_uint8(x_74, 1);
x_79 = lean_ctor_get_uint8(x_74, 2);
x_80 = lean_ctor_get_uint8(x_74, 3);
x_81 = lean_ctor_get_uint8(x_74, 4);
x_82 = lean_ctor_get_uint8(x_74, 6);
x_83 = lean_ctor_get_uint8(x_74, 7);
x_84 = lean_ctor_get_uint8(x_74, 8);
if (lean_is_exclusive(x_74)) {
 x_85 = x_74;
} else {
 lean_dec_ref(x_74);
 x_85 = lean_box(0);
}
x_86 = 0;
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 0, 9);
} else {
 x_87 = x_85;
}
lean_ctor_set_uint8(x_87, 0, x_77);
lean_ctor_set_uint8(x_87, 1, x_78);
lean_ctor_set_uint8(x_87, 2, x_79);
lean_ctor_set_uint8(x_87, 3, x_80);
lean_ctor_set_uint8(x_87, 4, x_81);
lean_ctor_set_uint8(x_87, 5, x_86);
lean_ctor_set_uint8(x_87, 6, x_82);
lean_ctor_set_uint8(x_87, 7, x_83);
lean_ctor_set_uint8(x_87, 8, x_84);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_75);
lean_ctor_set(x_88, 2, x_76);
x_89 = 1;
lean_inc(x_8);
lean_inc(x_73);
lean_inc(x_6);
x_90 = l_Lean_Meta_reduce(x_21, x_89, x_10, x_10, x_88, x_6, x_73, x_8, x_20);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_93, 0, x_91);
x_94 = 0;
x_95 = l_Lean_Elab_logAt___at_Lean_Elab_Term_traceAtCmdPos___spec__3(x_1, x_93, x_94, x_3, x_4, x_5, x_6, x_73, x_8, x_92);
lean_dec(x_8);
lean_dec(x_73);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_73);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_98 = x_90;
} else {
 lean_dec_ref(x_90);
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
}
else
{
uint8_t x_100; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_14);
if (x_100 == 0)
{
return x_14;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_14, 0);
x_102 = lean_ctor_get(x_14, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_14);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = !lean_is_exclusive(x_12);
if (x_104 == 0)
{
return x_12;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_12, 0);
x_106 = lean_ctor_get(x_12, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_12);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabReduce___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Elab_Term_resetMessageLog(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_4);
x_13 = l_Lean_Elab_Term_addAutoBoundImplicits(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 10, 3);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_15);
lean_closure_set(x_18, 2, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabReduce___lambda__1___boxed), 9, 1);
lean_closure_set(x_19, 0, x_2);
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg), 9, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = 0;
x_22 = l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg(x_20, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Command_elabReduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Parser_Command_reduce___elambda__1___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_st_ref_get(x_3, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_3, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_17);
lean_dec(x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabReduce___lambda__2___boxed), 10, 2);
lean_closure_set(x_20, 0, x_11);
lean_closure_set(x_20, 1, x_9);
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 10, 3);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_20);
lean_closure_set(x_23, 2, x_22);
x_24 = lean_box(x_21);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg___boxed), 9, 2);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_Command_elabCheck___closed__4;
lean_inc(x_2);
x_27 = l_Lean_Elab_Command_liftTermElabM___rarg(x_26, x_25, x_2, x_3, x_18);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_15, x_2, x_3, x_29);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
x_37 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_15, x_2, x_3, x_36);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabReduce___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabReduce___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabReduce___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabReduce___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_elabReduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabReduce(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabReduce___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabReduce___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_reduce___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabReduce___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_hasNoErrorMessages___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = lean_box(x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
}
}
}
lean_object* l_Lean_Elab_Command_hasNoErrorMessages(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_hasNoErrorMessages___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_hasNoErrorMessages___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_hasNoErrorMessages___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_hasNoErrorMessages___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_hasNoErrorMessages(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_failIfSucceeds_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_apply_3(x_2, x_1, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Elab_Command_failIfSucceeds_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_failIfSucceeds_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected success");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__3;
x_8 = l_Lean_throwError___at_Lean_Elab_Command_elabEnd___spec__1(x_7, x_2, x_3, x_4);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_failIfSucceeds___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("internal");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_failIfSucceeds___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_failIfSucceeds___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_failIfSucceeds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_take(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_77; 
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_14 = l_Std_PersistentArray_empty___closed__1;
lean_ctor_set(x_10, 1, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_47 = l_Lean_Elab_Command_failIfSucceeds___closed__1;
lean_inc(x_3);
lean_inc(x_2);
x_77 = lean_apply_3(x_1, x_2, x_3, x_16);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = l_Lean_Elab_Command_hasNoErrorMessages___rarg(x_3, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_unbox(x_80);
lean_dec(x_80);
x_48 = x_82;
x_49 = x_81;
goto block_76;
}
else
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_85 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_83, x_2, x_3, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = 0;
x_48 = x_87;
x_49 = x_86;
goto block_76;
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_2);
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_17 = x_88;
x_18 = x_89;
goto block_46;
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_83);
x_90 = lean_ctor_get(x_77, 1);
lean_inc(x_90);
lean_dec(x_77);
x_91 = l_Lean_Elab_Command_failIfSucceeds___closed__4;
x_92 = 2;
x_93 = l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3(x_91, x_92, x_2, x_3, x_90);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = 0;
x_48 = x_95;
x_49 = x_94;
goto block_76;
}
}
block_46:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_st_ref_take(x_3, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_23);
x_25 = l_Std_PersistentArray_append___rarg(x_8, x_24);
lean_dec(x_24);
lean_ctor_set(x_20, 1, x_25);
x_26 = lean_st_ref_set(x_3, x_20, x_21);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_17);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
x_33 = lean_ctor_get(x_20, 2);
x_34 = lean_ctor_get(x_20, 3);
x_35 = lean_ctor_get(x_20, 4);
x_36 = lean_ctor_get(x_20, 5);
x_37 = lean_ctor_get(x_20, 6);
x_38 = lean_ctor_get(x_20, 7);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_39 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_32);
x_40 = l_Std_PersistentArray_append___rarg(x_8, x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_33);
lean_ctor_set(x_41, 3, x_34);
lean_ctor_set(x_41, 4, x_35);
lean_ctor_set(x_41, 5, x_36);
lean_ctor_set(x_41, 6, x_37);
lean_ctor_set(x_41, 7, x_38);
x_42 = lean_st_ref_set(x_3, x_41, x_21);
lean_dec(x_3);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
 lean_ctor_set_tag(x_45, 1);
}
lean_ctor_set(x_45, 0, x_17);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
block_76:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_st_ref_take(x_3, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_51, 1);
x_55 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_54);
x_56 = l_Std_PersistentArray_append___rarg(x_8, x_55);
lean_dec(x_55);
lean_ctor_set(x_51, 1, x_56);
x_57 = lean_st_ref_set(x_3, x_51, x_52);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_box(x_48);
x_60 = lean_apply_4(x_47, x_59, x_2, x_3, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_61 = lean_ctor_get(x_51, 0);
x_62 = lean_ctor_get(x_51, 1);
x_63 = lean_ctor_get(x_51, 2);
x_64 = lean_ctor_get(x_51, 3);
x_65 = lean_ctor_get(x_51, 4);
x_66 = lean_ctor_get(x_51, 5);
x_67 = lean_ctor_get(x_51, 6);
x_68 = lean_ctor_get(x_51, 7);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_51);
x_69 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_62);
x_70 = l_Std_PersistentArray_append___rarg(x_8, x_69);
lean_dec(x_69);
x_71 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_71, 0, x_61);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_63);
lean_ctor_set(x_71, 3, x_64);
lean_ctor_set(x_71, 4, x_65);
lean_ctor_set(x_71, 5, x_66);
lean_ctor_set(x_71, 6, x_67);
lean_ctor_set(x_71, 7, x_68);
x_72 = lean_st_ref_set(x_3, x_71, x_52);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_box(x_48);
x_75 = lean_apply_4(x_47, x_74, x_2, x_3, x_73);
return x_75;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_152; 
x_96 = lean_ctor_get(x_10, 0);
x_97 = lean_ctor_get(x_10, 2);
x_98 = lean_ctor_get(x_10, 3);
x_99 = lean_ctor_get(x_10, 4);
x_100 = lean_ctor_get(x_10, 5);
x_101 = lean_ctor_get(x_10, 6);
x_102 = lean_ctor_get(x_10, 7);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_10);
x_103 = l_Std_PersistentArray_empty___closed__1;
x_104 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_104, 0, x_96);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_104, 2, x_97);
lean_ctor_set(x_104, 3, x_98);
lean_ctor_set(x_104, 4, x_99);
lean_ctor_set(x_104, 5, x_100);
lean_ctor_set(x_104, 6, x_101);
lean_ctor_set(x_104, 7, x_102);
x_105 = lean_st_ref_set(x_3, x_104, x_11);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_129 = l_Lean_Elab_Command_failIfSucceeds___closed__1;
lean_inc(x_3);
lean_inc(x_2);
x_152 = lean_apply_3(x_1, x_2, x_3, x_106);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_154 = l_Lean_Elab_Command_hasNoErrorMessages___rarg(x_3, x_153);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_unbox(x_155);
lean_dec(x_155);
x_130 = x_157;
x_131 = x_156;
goto block_151;
}
else
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_152, 0);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_152, 1);
lean_inc(x_159);
lean_dec(x_152);
x_160 = l_Lean_Elab_logException___at_Lean_Elab_Command_runLinters___spec__1(x_158, x_2, x_3, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = 0;
x_130 = x_162;
x_131 = x_161;
goto block_151;
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_2);
x_163 = lean_ctor_get(x_160, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
lean_dec(x_160);
x_107 = x_163;
x_108 = x_164;
goto block_128;
}
}
else
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_dec(x_158);
x_165 = lean_ctor_get(x_152, 1);
lean_inc(x_165);
lean_dec(x_152);
x_166 = l_Lean_Elab_Command_failIfSucceeds___closed__4;
x_167 = 2;
x_168 = l_Lean_Elab_log___at_Lean_Elab_Command_runLinters___spec__3(x_166, x_167, x_2, x_3, x_165);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_170 = 0;
x_130 = x_170;
x_131 = x_169;
goto block_151;
}
}
block_128:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_109 = lean_st_ref_take(x_3, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_110, 4);
lean_inc(x_116);
x_117 = lean_ctor_get(x_110, 5);
lean_inc(x_117);
x_118 = lean_ctor_get(x_110, 6);
lean_inc(x_118);
x_119 = lean_ctor_get(x_110, 7);
lean_inc(x_119);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 lean_ctor_release(x_110, 4);
 lean_ctor_release(x_110, 5);
 lean_ctor_release(x_110, 6);
 lean_ctor_release(x_110, 7);
 x_120 = x_110;
} else {
 lean_dec_ref(x_110);
 x_120 = lean_box(0);
}
x_121 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_113);
x_122 = l_Std_PersistentArray_append___rarg(x_8, x_121);
lean_dec(x_121);
if (lean_is_scalar(x_120)) {
 x_123 = lean_alloc_ctor(0, 8, 0);
} else {
 x_123 = x_120;
}
lean_ctor_set(x_123, 0, x_112);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_123, 2, x_114);
lean_ctor_set(x_123, 3, x_115);
lean_ctor_set(x_123, 4, x_116);
lean_ctor_set(x_123, 5, x_117);
lean_ctor_set(x_123, 6, x_118);
lean_ctor_set(x_123, 7, x_119);
x_124 = lean_st_ref_set(x_3, x_123, x_111);
lean_dec(x_3);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
 lean_ctor_set_tag(x_127, 1);
}
lean_ctor_set(x_127, 0, x_107);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
block_151:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_132 = lean_st_ref_take(x_3, x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_133, 2);
lean_inc(x_137);
x_138 = lean_ctor_get(x_133, 3);
lean_inc(x_138);
x_139 = lean_ctor_get(x_133, 4);
lean_inc(x_139);
x_140 = lean_ctor_get(x_133, 5);
lean_inc(x_140);
x_141 = lean_ctor_get(x_133, 6);
lean_inc(x_141);
x_142 = lean_ctor_get(x_133, 7);
lean_inc(x_142);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 lean_ctor_release(x_133, 2);
 lean_ctor_release(x_133, 3);
 lean_ctor_release(x_133, 4);
 lean_ctor_release(x_133, 5);
 lean_ctor_release(x_133, 6);
 lean_ctor_release(x_133, 7);
 x_143 = x_133;
} else {
 lean_dec_ref(x_133);
 x_143 = lean_box(0);
}
x_144 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_136);
x_145 = l_Std_PersistentArray_append___rarg(x_8, x_144);
lean_dec(x_144);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 8, 0);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_135);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_146, 2, x_137);
lean_ctor_set(x_146, 3, x_138);
lean_ctor_set(x_146, 4, x_139);
lean_ctor_set(x_146, 5, x_140);
lean_ctor_set(x_146, 6, x_141);
lean_ctor_set(x_146, 7, x_142);
x_147 = lean_st_ref_set(x_3, x_146, x_134);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = lean_box(x_130);
x_150 = lean_apply_4(x_129, x_149, x_2, x_3, x_148);
return x_150;
}
}
}
}
lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Elab_Command_failIfSucceeds___lambda__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elabCheckFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheck___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_Command_failIfSucceeds(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheckFailure), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_check__failure___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__4___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Command_elabEvalUnsafe_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_throwKernelException___at_Lean_Elab_Command_elabEvalUnsafe___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = l_Lean_KernelException_toMessageData(x_1, x_9);
x_11 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_11;
}
}
lean_object* l_Lean_addDecl___at_Lean_Elab_Command_elabEvalUnsafe___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_add_decl(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_throwKernelException___at_Lean_Elab_Command_elabEvalUnsafe___spec__3(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__1(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_6);
lean_dec(x_2);
return x_17;
}
}
}
lean_object* l_Lean_compileDecl___at_Lean_Elab_Command_elabEvalUnsafe___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
x_14 = lean_compile_decl(x_12, x_13, x_1);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_throwKernelException___at_Lean_Elab_Command_elabEvalUnsafe___spec__3(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__1(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_6);
lean_dec(x_2);
return x_18;
}
}
}
lean_object* l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_2);
x_9 = l_Lean_addDecl___at_Lean_Elab_Command_elabEvalUnsafe___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_compileDecl___at_Lean_Elab_Command_elabEvalUnsafe___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_7, 3);
x_13 = lean_apply_1(x_2, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = 0;
x_21 = l_Lean_Elab_logAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__2(x_1, x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_io_error_to_string(x_23);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_throwError___at_Lean_Elab_Term_evalExpr___spec__7(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_21, 0, x_30);
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_io_error_to_string(x_35);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_inc(x_12);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_13, 0, x_39);
return x_13;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_13, 0);
x_41 = lean_ctor_get(x_13, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_13);
x_42 = lean_io_error_to_string(x_40);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_inc(x_12);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("runEval");
return x_1;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_mkSimpleThunk(x_4);
x_13 = 0;
x_14 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1;
x_18 = lean_name_mk_string(x_1, x_17);
x_19 = l_Lean_mkOptionalNode___closed__2;
x_20 = lean_array_push(x_19, x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Meta_mkAppM(x_18, x_20, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_get(x_10, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_22);
x_28 = l_Lean_Meta_inferType(x_22, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(0);
lean_inc(x_3);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_29);
x_33 = lean_box(0);
x_34 = 0;
x_35 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_22);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_36);
x_37 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
lean_inc(x_9);
lean_inc(x_5);
x_39 = l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
lean_dec(x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_5);
x_41 = l_Lean_evalConst___at_Lean_Elab_Term_evalExpr___spec__10___rarg(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
lean_dec(x_3);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__8(x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__1(x_2, x_42, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_41, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__8(x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_3);
x_54 = lean_ctor_get(x_39, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_39, 1);
lean_inc(x_55);
lean_dec(x_39);
x_56 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__8(x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_55);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 0, x_54);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_36);
lean_dec(x_3);
x_61 = lean_ctor_get(x_37, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_37, 1);
lean_inc(x_62);
lean_dec(x_37);
x_63 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__8(x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
lean_ctor_set_tag(x_63, 1);
lean_ctor_set(x_63, 0, x_61);
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec(x_22);
lean_dec(x_3);
x_68 = lean_ctor_get(x_28, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_28, 1);
lean_inc(x_69);
lean_dec(x_28);
x_70 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__8(x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_69);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
lean_ctor_set_tag(x_70, 1);
lean_ctor_set(x_70, 0, x_68);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_21);
if (x_75 == 0)
{
return x_21;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_21, 0);
x_77 = lean_ctor_get(x_21, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_21);
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
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_15);
if (x_79 == 0)
{
return x_15;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_15, 0);
x_81 = lean_ctor_get(x_15, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_15);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Elab_Term_resetMessageLog(x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_6);
x_15 = l_Lean_Elab_Term_addAutoBoundImplicits(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 10, 3);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___boxed), 11, 3);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_4);
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg), 9, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = 0;
x_24 = l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg(x_22, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("runMetaEval");
return x_1;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__1;
x_13 = lean_name_mk_string(x_1, x_12);
x_14 = l_Lean_Syntax_mkAntiquotNode___closed__9;
lean_inc(x_2);
x_15 = lean_array_push(x_14, x_2);
lean_inc(x_4);
x_16 = lean_array_push(x_15, x_4);
x_17 = lean_array_push(x_16, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l_Lean_Meta_mkAppM(x_13, x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Syntax_mkApp___closed__1;
x_22 = lean_array_push(x_21, x_2);
x_23 = lean_array_push(x_22, x_4);
x_24 = l_Lean_Meta_mkLambdaFVars(x_23, x_19, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("opts");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Options");
return x_1;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_12 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__3;
lean_inc(x_1);
x_13 = lean_name_mk_string(x_1, x_12);
x_14 = l_Lean_mkConst(x_13, x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___boxed), 11, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_4);
lean_closure_set(x_15, 2, x_3);
x_16 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__2;
x_17 = 0;
x_18 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(x_16, x_17, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_apply_3(x_4, x_1, x_2, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = 0;
x_23 = l_Lean_Elab_logAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__2(x_3, x_21, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_io_error_to_string(x_25);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_throwError___at_Lean_Elab_Term_evalExpr___spec__7(x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_dec(x_23);
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec(x_19);
x_32 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__8(x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_5);
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
}
else
{
uint8_t x_39; 
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_15);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_15, 0);
x_41 = lean_io_error_to_string(x_40);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_inc(x_14);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_14);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_15, 0, x_44);
return x_15;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_15, 0);
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_15);
x_47 = lean_io_error_to_string(x_45);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_inc(x_14);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_14);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_46);
return x_51;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("env");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Environment");
return x_1;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__3;
lean_inc(x_1);
x_17 = lean_name_mk_string(x_1, x_16);
x_18 = lean_box(0);
x_19 = l_Lean_mkConst(x_17, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__5), 11, 3);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_4);
x_21 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__2;
x_22 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(x_21, x_22, x_19, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_10, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_9, 0);
lean_inc(x_30);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_24);
x_31 = l_Lean_Meta_inferType(x_24, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_3);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_3);
lean_ctor_set(x_34, 1, x_18);
lean_ctor_set(x_34, 2, x_32);
x_35 = lean_box(0);
x_36 = 0;
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_24);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_38);
x_39 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_9);
lean_inc(x_5);
x_41 = l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1(x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
lean_dec(x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_5);
x_43 = l_Lean_evalConst___at_Lean_Elab_Term_evalExpr___spec__10___rarg(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_42);
lean_dec(x_3);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_29);
x_46 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__8(x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__6(x_29, x_30, x_2, x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_47);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_30);
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec(x_43);
x_51 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__8(x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_30);
lean_dec(x_3);
x_56 = lean_ctor_get(x_41, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
lean_dec(x_41);
x_58 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__8(x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
lean_ctor_set_tag(x_58, 1);
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_38);
lean_dec(x_30);
lean_dec(x_3);
x_63 = lean_ctor_get(x_39, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_39, 1);
lean_inc(x_64);
lean_dec(x_39);
x_65 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__8(x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_64);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set_tag(x_65, 1);
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_3);
x_70 = lean_ctor_get(x_31, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_31, 1);
lean_inc(x_71);
lean_dec(x_31);
x_72 = l_Lean_setEnv___at_Lean_Elab_Term_evalExpr___spec__8(x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_71);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 0, x_70);
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_23);
if (x_77 == 0)
{
return x_23;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_23, 0);
x_79 = lean_ctor_get(x_23, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_23);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_14);
if (x_81 == 0)
{
return x_14;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_14, 0);
x_83 = lean_ctor_get(x_14, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_14);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_Elab_Term_resetMessageLog(x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_6);
x_15 = l_Lean_Elab_Term_addAutoBoundImplicits(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 10, 3);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___boxed), 11, 3);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_4);
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg), 9, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = 0;
x_24 = l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg(x_22, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_eval");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEvalUnsafe___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("MetaEval");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Parser_Command_eval___elambda__1___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_st_ref_get(x_3, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Command_elabEvalUnsafe___closed__5;
x_17 = l_Lean_Environment_contains(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_st_ref_get(x_3, x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_19);
lean_dec(x_19);
x_22 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_23 = l_Lean_Elab_Command_elabEvalUnsafe___closed__2;
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___boxed), 12, 4);
lean_closure_set(x_24, 0, x_11);
lean_closure_set(x_24, 1, x_22);
lean_closure_set(x_24, 2, x_9);
lean_closure_set(x_24, 3, x_23);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 10, 3);
lean_closure_set(x_27, 0, x_21);
lean_closure_set(x_27, 1, x_24);
lean_closure_set(x_27, 2, x_26);
x_28 = lean_box(x_25);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg___boxed), 9, 2);
lean_closure_set(x_29, 0, x_27);
lean_closure_set(x_29, 1, x_28);
x_30 = l_Lean_Elab_Command_elabEvalUnsafe___closed__3;
x_31 = l_Lean_Elab_Command_liftTermElabM___rarg(x_30, x_29, x_2, x_3, x_20);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_32 = lean_st_ref_get(x_3, x_14);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_33);
lean_dec(x_33);
x_36 = l_Lean_Parser_Syntax_addPrec___closed__2;
x_37 = l_Lean_Elab_Command_elabEvalUnsafe___closed__2;
x_38 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___boxed), 12, 4);
lean_closure_set(x_38, 0, x_11);
lean_closure_set(x_38, 1, x_36);
lean_closure_set(x_38, 2, x_9);
lean_closure_set(x_38, 3, x_37);
x_39 = 1;
x_40 = lean_box(x_39);
x_41 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 10, 3);
lean_closure_set(x_41, 0, x_35);
lean_closure_set(x_41, 1, x_38);
lean_closure_set(x_41, 2, x_40);
x_42 = lean_box(x_39);
x_43 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg___boxed), 9, 2);
lean_closure_set(x_43, 0, x_41);
lean_closure_set(x_43, 1, x_42);
x_44 = l_Lean_Elab_Command_elabEvalUnsafe___closed__3;
x_45 = l_Lean_Elab_Command_liftTermElabM___rarg(x_44, x_43, x_2, x_3, x_34);
return x_45;
}
}
}
}
lean_object* l_Lean_throwKernelException___at_Lean_Elab_Command_elabEvalUnsafe___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwKernelException___at_Lean_Elab_Command_elabEvalUnsafe___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_addDecl___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addDecl___at_Lean_Elab_Command_elabEvalUnsafe___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_compileDecl___at_Lean_Elab_Command_elabEvalUnsafe___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_compileDecl___at_Lean_Elab_Command_elabEvalUnsafe___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Lean_Elab_Command_elabEvalUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabEvalUnsafe(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabEval___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedException___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabEval(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEval___rarg), 1, 0);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabEval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabEval(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEval___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabEval(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_eval___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabEval___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabSynth___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Meta_instantiateMVars(x_2, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Meta_synthInstance(x_15, x_1, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = 0;
x_22 = l_Lean_Elab_log___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__3(x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_11);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
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
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_12);
if (x_35 == 0)
{
return x_12;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_12, 0);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_12);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSynth___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSynth___lambda__1), 9, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabSynth___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Elab_Term_resetMessageLog(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_3);
x_12 = l_Lean_Elab_Term_addAutoBoundImplicits(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = 1;
x_16 = lean_box(x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 10, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_16);
x_18 = l_Lean_Elab_Command_elabSynth___lambda__2___closed__1;
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg), 9, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = 0;
x_21 = l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg(x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSynth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_synth_cmd");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSynth___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabSynth___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSynth___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSynth___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabSynth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_st_ref_get(x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_3, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_12);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSynth___lambda__2___boxed), 9, 1);
lean_closure_set(x_15, 0, x_6);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 10, 3);
lean_closure_set(x_18, 0, x_14);
lean_closure_set(x_18, 1, x_15);
lean_closure_set(x_18, 2, x_17);
x_19 = lean_box(x_16);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicitLocal___rarg___boxed), 9, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Command_elabSynth___closed__3;
lean_inc(x_2);
x_22 = l_Lean_Elab_Command_liftTermElabM___rarg(x_21, x_20, x_2, x_3, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_10, x_2, x_3, x_24);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_10, x_2, x_3, x_31);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabSynth___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabSynth___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Elab_Command_elabSynth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabSynth(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSynth___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_synth___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_setOption_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; size_t x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_usize(x_1, 2);
x_8 = l_Lean_getMaxRecDepth___closed__1;
x_9 = lean_string_dec_eq(x_6, x_8);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_4, x_1, x_2);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_1);
lean_dec(x_4);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_box_usize(x_7);
x_16 = lean_apply_2(x_3, x_14, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_8);
x_17 = lean_apply_2(x_4, x_1, x_2);
return x_17;
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_box_usize(x_7);
x_20 = lean_apply_2(x_3, x_18, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_21 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_8);
lean_ctor_set_usize(x_21, 2, x_7);
x_22 = lean_apply_2(x_4, x_21, x_2);
return x_22;
}
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_5);
lean_dec(x_3);
x_23 = lean_apply_2(x_4, x_1, x_2);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_3);
x_24 = lean_apply_2(x_4, x_1, x_2);
return x_24;
}
}
}
lean_object* l_Lean_Elab_Command_setOption_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_setOption_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_st_ref_take(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_7, 2);
lean_dec(x_11);
x_12 = lean_box(0);
x_13 = l_Lean_Elab_Command_modifyScope___closed__3;
x_14 = lean_panic_fn(x_12, x_13);
lean_ctor_set(x_7, 2, x_14);
x_15 = lean_st_ref_set(x_4, x_7, x_9);
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
x_24 = lean_ctor_get(x_7, 3);
x_25 = lean_ctor_get(x_7, 4);
x_26 = lean_ctor_get(x_7, 5);
x_27 = lean_ctor_get(x_7, 6);
x_28 = lean_ctor_get(x_7, 7);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_29 = lean_box(0);
x_30 = l_Lean_Elab_Command_modifyScope___closed__3;
x_31 = lean_panic_fn(x_29, x_30);
x_32 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_32, 3, x_24);
lean_ctor_set(x_32, 4, x_25);
lean_ctor_set(x_32, 5, x_26);
lean_ctor_set(x_32, 6, x_27);
lean_ctor_set(x_32, 7, x_28);
x_33 = lean_st_ref_set(x_4, x_32, x_9);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_8, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_dec(x_6);
x_40 = !lean_is_exclusive(x_7);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_7, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_8, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_38, 1);
x_46 = l_Lean_KVMap_insertCore(x_45, x_1, x_2);
lean_ctor_set(x_38, 1, x_46);
x_47 = lean_st_ref_set(x_4, x_7, x_39);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_54 = lean_ctor_get(x_38, 0);
x_55 = lean_ctor_get(x_38, 1);
x_56 = lean_ctor_get(x_38, 2);
x_57 = lean_ctor_get(x_38, 3);
x_58 = lean_ctor_get(x_38, 4);
x_59 = lean_ctor_get(x_38, 5);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_38);
x_60 = l_Lean_KVMap_insertCore(x_55, x_1, x_2);
x_61 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_61, 0, x_54);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_56);
lean_ctor_set(x_61, 3, x_57);
lean_ctor_set(x_61, 4, x_58);
lean_ctor_set(x_61, 5, x_59);
lean_ctor_set(x_8, 0, x_61);
x_62 = lean_st_ref_set(x_4, x_7, x_39);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_67 = lean_ctor_get(x_8, 1);
lean_inc(x_67);
lean_dec(x_8);
x_68 = lean_ctor_get(x_38, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_38, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_38, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_38, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_38, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_38, 5);
lean_inc(x_73);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 x_74 = x_38;
} else {
 lean_dec_ref(x_38);
 x_74 = lean_box(0);
}
x_75 = l_Lean_KVMap_insertCore(x_69, x_1, x_2);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 6, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_68);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_76, 2, x_70);
lean_ctor_set(x_76, 3, x_71);
lean_ctor_set(x_76, 4, x_72);
lean_ctor_set(x_76, 5, x_73);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_67);
lean_ctor_set(x_7, 2, x_77);
x_78 = lean_st_ref_set(x_4, x_7, x_39);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = lean_box(0);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_83 = lean_ctor_get(x_7, 0);
x_84 = lean_ctor_get(x_7, 1);
x_85 = lean_ctor_get(x_7, 3);
x_86 = lean_ctor_get(x_7, 4);
x_87 = lean_ctor_get(x_7, 5);
x_88 = lean_ctor_get(x_7, 6);
x_89 = lean_ctor_get(x_7, 7);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_7);
x_90 = lean_ctor_get(x_8, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_91 = x_8;
} else {
 lean_dec_ref(x_8);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_38, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_38, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_38, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_38, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_38, 4);
lean_inc(x_96);
x_97 = lean_ctor_get(x_38, 5);
lean_inc(x_97);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 x_98 = x_38;
} else {
 lean_dec_ref(x_38);
 x_98 = lean_box(0);
}
x_99 = l_Lean_KVMap_insertCore(x_93, x_1, x_2);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 6, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_92);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_100, 2, x_94);
lean_ctor_set(x_100, 3, x_95);
lean_ctor_set(x_100, 4, x_96);
lean_ctor_set(x_100, 5, x_97);
if (lean_is_scalar(x_91)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_91;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_90);
x_102 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_102, 0, x_83);
lean_ctor_set(x_102, 1, x_84);
lean_ctor_set(x_102, 2, x_101);
lean_ctor_set(x_102, 3, x_85);
lean_ctor_set(x_102, 4, x_86);
lean_ctor_set(x_102, 5, x_87);
lean_ctor_set(x_102, 6, x_88);
lean_ctor_set(x_102, 7, x_89);
x_103 = lean_st_ref_set(x_4, x_102, x_39);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_box(0);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
}
}
}
lean_object* l_Lean_Elab_Command_setOption___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1(x_1, x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_getMaxRecDepth___closed__1;
x_14 = lean_string_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_box(0);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_free_object(x_7);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_st_ref_take(x_5, x_10);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 4);
lean_dec(x_21);
lean_ctor_set(x_18, 4, x_16);
x_22 = lean_st_ref_set(x_5, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
x_31 = lean_ctor_get(x_18, 2);
x_32 = lean_ctor_get(x_18, 3);
x_33 = lean_ctor_get(x_18, 5);
x_34 = lean_ctor_get(x_18, 6);
x_35 = lean_ctor_get(x_18, 7);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_36 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_31);
lean_ctor_set(x_36, 3, x_32);
lean_ctor_set(x_36, 4, x_16);
lean_ctor_set(x_36, 5, x_33);
lean_ctor_set(x_36, 6, x_34);
lean_ctor_set(x_36, 7, x_35);
x_37 = lean_st_ref_set(x_5, x_36, x_19);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec(x_2);
x_42 = lean_box(0);
lean_ctor_set(x_7, 0, x_42);
return x_7;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_7, 1);
lean_inc(x_43);
lean_dec(x_7);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
lean_dec(x_1);
x_45 = l_Lean_getMaxRecDepth___closed__1;
x_46 = lean_string_dec_eq(x_44, x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
else
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
lean_dec(x_2);
x_50 = lean_st_ref_take(x_5, x_43);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_51, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_51, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_51, 5);
lean_inc(x_57);
x_58 = lean_ctor_get(x_51, 6);
lean_inc(x_58);
x_59 = lean_ctor_get(x_51, 7);
lean_inc(x_59);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 lean_ctor_release(x_51, 4);
 lean_ctor_release(x_51, 5);
 lean_ctor_release(x_51, 6);
 lean_ctor_release(x_51, 7);
 x_60 = x_51;
} else {
 lean_dec_ref(x_51);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 8, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_54);
lean_ctor_set(x_61, 2, x_55);
lean_ctor_set(x_61, 3, x_56);
lean_ctor_set(x_61, 4, x_49);
lean_ctor_set(x_61, 5, x_57);
lean_ctor_set(x_61, 6, x_58);
lean_ctor_set(x_61, 7, x_59);
x_62 = lean_st_ref_set(x_5, x_61, x_52);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_2);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_43);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_7);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_7, 0);
lean_dec(x_70);
x_71 = lean_box(0);
lean_ctor_set(x_7, 0, x_71);
return x_7;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_7, 1);
lean_inc(x_72);
lean_dec(x_7);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_7);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_7, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_7, 0, x_77);
return x_7;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_7, 1);
lean_inc(x_78);
lean_dec(x_7);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_setOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type mismatch at set_option");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_setOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_setOption___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_setOption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_setOption___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_setOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l_Lean_getOptionDecl(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_DataValue_sameCtor(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Elab_Command_setOption___closed__3;
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__5(x_11, x_3, x_4, x_8);
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
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Command_setOption___lambda__1(x_1, x_2, x_17, x_3, x_4, x_8);
lean_dec(x_3);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_3, 6);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_io_error_to_string(x_20);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_6, 0, x_25);
return x_6;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_28 = lean_ctor_get(x_3, 6);
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_io_error_to_string(x_26);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_setOption___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_setOption___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Command_setOption___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_setOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_setOption(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_elabSetOption_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_instReprBool___closed__3;
x_8 = lean_string_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_2);
x_9 = l_instReprBool___closed__1;
x_10 = lean_string_dec_eq(x_6, x_9);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_11 = lean_apply_1(x_4, x_1);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_apply_1(x_3, x_5);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_apply_1(x_2, x_5);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_1(x_4, x_1);
return x_14;
}
}
}
lean_object* l_Lean_Elab_Command_elabSetOption_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSetOption_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabSetOption_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_elabSetOption_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSetOption_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabSetOption_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_elabSetOption_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSetOption_match__3___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSetOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected set_option value ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSetOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSetOption___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabSetOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getId(x_6);
lean_dec(x_6);
x_8 = lean_erase_macro_scopes(x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_isStrLit_x3f(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_numLitKind;
x_13 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_12, x_10);
if (lean_obj_tag(x_13) == 0)
{
if (lean_obj_tag(x_10) == 2)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
x_15 = l_instReprBool___closed__3;
x_16 = lean_string_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_instReprBool___closed__1;
x_18 = lean_string_dec_eq(x_14, x_17);
lean_dec(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
lean_dec(x_8);
lean_inc(x_10);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_10);
x_20 = l_Lean_Elab_Command_elabSetOption___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_KernelException_toMessageData___closed__15;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = 2;
x_25 = l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2(x_10, x_23, x_24, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
x_26 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__3;
x_27 = l_Lean_Elab_Command_setOption(x_8, x_26, x_2, x_3, x_4);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_14);
lean_dec(x_10);
x_28 = l_Lean_initFn____x40_Lean_Data_Options___hyg_528____closed__3;
x_29 = l_Lean_Elab_Command_setOption(x_8, x_28, x_2, x_3, x_4);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
lean_dec(x_8);
lean_inc(x_10);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_10);
x_31 = l_Lean_Elab_Command_elabSetOption___closed__2;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_KernelException_toMessageData___closed__15;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = 2;
x_36 = l_Lean_Elab_logAt___at_Lean_Elab_Command_withLogging___spec__2(x_10, x_34, x_35, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_10);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_10);
x_37 = lean_ctor_get(x_13, 0);
lean_inc(x_37);
lean_dec(x_13);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_Elab_Command_setOption(x_8, x_38, x_2, x_3, x_4);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_10);
x_40 = lean_ctor_get(x_11, 0);
lean_inc(x_40);
lean_dec(x_11);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Lean_Elab_Command_setOption(x_8, x_41, x_2, x_3, x_4);
return x_42;
}
}
}
lean_object* l_Lean_Elab_Command_elabSetOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabSetOption(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSetOption___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_set__option___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_expandInCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Parser_Command_section___elambda__1___closed__1;
lean_inc(x_10);
x_12 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Array_empty___closed__1;
x_14 = lean_array_push(x_13, x_12);
x_15 = l_myMacro____x40_Init_Notation___hyg_13781____closed__10;
x_16 = lean_array_push(x_14, x_15);
x_17 = l_Lean_Parser_Command_section___elambda__1___closed__2;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_array_push(x_13, x_18);
x_20 = lean_array_push(x_19, x_5);
x_21 = lean_array_push(x_20, x_7);
x_22 = l_Lean_Parser_Command_end___elambda__1___closed__1;
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_array_push(x_13, x_23);
x_25 = lean_array_push(x_24, x_15);
x_26 = l_Lean_Parser_Command_end___elambda__1___closed__2;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_array_push(x_21, x_27);
x_29 = l_Lean_nullKind___closed__2;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_8, 0, x_30);
return x_8;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = l_Lean_Parser_Command_section___elambda__1___closed__1;
lean_inc(x_31);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Array_empty___closed__1;
x_36 = lean_array_push(x_35, x_34);
x_37 = l_myMacro____x40_Init_Notation___hyg_13781____closed__10;
x_38 = lean_array_push(x_36, x_37);
x_39 = l_Lean_Parser_Command_section___elambda__1___closed__2;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_array_push(x_35, x_40);
x_42 = lean_array_push(x_41, x_5);
x_43 = lean_array_push(x_42, x_7);
x_44 = l_Lean_Parser_Command_end___elambda__1___closed__1;
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_31);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_array_push(x_35, x_45);
x_47 = lean_array_push(x_46, x_37);
x_48 = l_Lean_Parser_Command_end___elambda__1___closed__2;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_array_push(x_43, x_49);
x_51 = l_Lean_nullKind___closed__2;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_32);
return x_53;
}
}
}
lean_object* l_Lean_Elab_Command_expandInCmd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_expandInCmd(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandInCmd___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Lean_Parser_Command_in___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Environment_contains(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_10);
x_15 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_18, x_4, x_5, x_6);
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
lean_inc(x_2);
x_7 = l_Lean_mkPrivateName(x_2, x_1);
lean_inc(x_2);
x_8 = l_Lean_Environment_contains(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__1(x_1, x_2, x_9, x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(x_15, x_4, x_5, x_6);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_8);
x_9 = l_Lean_Environment_contains(x_8, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__2(x_1, x_8, x_10, x_2, x_3, x_7);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_8);
lean_inc(x_1);
x_12 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = l_Lean_KernelException_toMessageData___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(x_17, x_2, x_3, x_7);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(x_28, x_2, x_3, x_7);
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
}
}
lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
case 1:
{
lean_object* x_15; 
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_4, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_protectedExt;
lean_inc(x_2);
x_22 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_21, x_20, x_2);
x_23 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_22, x_3, x_4, x_19);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_2);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
default: 
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_st_ref_get(x_4, x_5);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkPrivateName(x_35, x_2);
lean_inc(x_36);
x_37 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4(x_36, x_3, x_4, x_34);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_36);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
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
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
lean_inc(x_2);
x_8 = l_Lean_Name_append(x_1, x_2);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
lean_inc(x_5);
x_10 = l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__3(x_9, x_8, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_box(x_9);
if (lean_obj_tag(x_11) == 1)
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_name_mk_string(x_15, x_14);
x_17 = l_Lean_Name_append(x_16, x_2);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_name_mk_string(x_22, x_21);
x_24 = l_Lean_Name_append(x_23, x_2);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
x_28 = l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__3;
x_29 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__5(x_28, x_5, x_6, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_2);
lean_ctor_set(x_10, 0, x_32);
return x_10;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_10);
if (x_37 == 0)
{
return x_10;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_10, 0);
x_39 = lean_ctor_get(x_10, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_10);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_3);
x_7 = l_Lean_extractMacroScopes(x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Name_isAtomic(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Elab_isFreshInstanceName(x_8);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_3);
x_12 = l_Lean_Elab_mkDeclName___rarg___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_KernelException_toMessageData___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(x_15, x_4, x_5, x_6);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1(x_1, x_3, x_2, x_21, x_4, x_5, x_6);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1(x_1, x_3, x_2, x_23, x_4, x_5, x_6);
return x_24;
}
}
}
lean_object* l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_take(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Lean_docStringExt;
x_12 = l_Lean_MapDeclarationExtension_insert___rarg(x_11, x_10, x_1, x_2);
lean_ctor_set(x_7, 0, x_12);
x_13 = lean_st_ref_set(x_4, x_7, x_8);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_ctor_get(x_7, 2);
x_23 = lean_ctor_get(x_7, 3);
x_24 = lean_ctor_get(x_7, 4);
x_25 = lean_ctor_get(x_7, 5);
x_26 = lean_ctor_get(x_7, 6);
x_27 = lean_ctor_get(x_7, 7);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_28 = l_Lean_docStringExt;
x_29 = l_Lean_MapDeclarationExtension_insert___rarg(x_28, x_20, x_1, x_2);
x_30 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set(x_30, 4, x_24);
lean_ctor_set(x_30, 5, x_25);
lean_ctor_set(x_30, 6, x_26);
lean_ctor_set(x_30, 7, x_27);
x_31 = lean_st_ref_set(x_4, x_30, x_8);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
lean_object* l_Lean_addDocString_x27___at_Lean_Elab_Command_expandDeclId___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__7(x_1, x_8, x_3, x_4, x_5);
return x_9;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__2;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__9(x_9, x_2, x_3, x_4);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandDeclId___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_2 == x_3;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_uget(x_1, x_2);
x_10 = l_Lean_Syntax_getId(x_9);
x_11 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_10, x_4);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_4);
x_13 = 1;
x_14 = x_2 + x_13;
x_2 = x_14;
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_4);
x_16 = l_Lean_Elab_Command_getRef(x_5, x_6, x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_replaceRef(x_9, x_17);
lean_dec(x_17);
lean_dec(x_9);
x_20 = !lean_is_exclusive(x_5);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_5, 6);
lean_dec(x_21);
lean_ctor_set(x_5, 6, x_19);
x_22 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__8(x_10, x_5, x_6, x_18);
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_ctor_get(x_5, 1);
x_29 = lean_ctor_get(x_5, 2);
x_30 = lean_ctor_get(x_5, 3);
x_31 = lean_ctor_get(x_5, 4);
x_32 = lean_ctor_get(x_5, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_5);
x_33 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_31);
lean_ctor_set(x_33, 5, x_32);
lean_ctor_set(x_33, 6, x_19);
x_34 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__8(x_10, x_33, x_6, x_18);
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
else
{
lean_object* x_39; 
lean_dec(x_5);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_7);
return x_39;
}
}
}
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = l_Lean_Elab_Command_getRef(x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_replaceRef(x_1, x_10);
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
x_17 = lean_ctor_get(x_6, 4);
x_18 = lean_ctor_get(x_6, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_19 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_18);
lean_ctor_set(x_19, 6, x_12);
x_20 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2(x_2, x_3, x_4, x_19, x_7, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
lean_dec(x_3);
lean_inc(x_23);
x_26 = l_Lean_addDocString_x27___at_Lean_Elab_Command_expandDeclId___spec__6(x_23, x_25, x_6, x_7, x_22);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_29, 2, x_5);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_5);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_5);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Elab_expandDeclIdCore(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Syntax_isNone(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_10, x_12);
lean_dec(x_10);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
lean_object* x_35; 
lean_dec(x_15);
lean_dec(x_14);
x_35 = l_Array_empty___closed__1;
x_18 = x_35;
goto block_34;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_15, x_15);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_15);
lean_dec(x_14);
x_37 = l_Array_empty___closed__1;
x_18 = x_37;
goto block_34;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_40 = l_Array_getEvenElems___rarg___closed__1;
x_41 = l_Array_foldlMUnsafe_fold___at_Lean_Syntax_SepArray_getElems___spec__1(x_14, x_38, x_39, x_40);
lean_dec(x_14);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_18 = x_42;
goto block_34;
}
}
block_34:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_array_get_size(x_18);
x_20 = lean_nat_dec_lt(x_16, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
x_21 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(x_3, x_1, x_4, x_9, x_2, x_5, x_6, x_7);
lean_dec(x_5);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_19, x_19);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_18);
x_23 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(x_3, x_1, x_4, x_9, x_2, x_5, x_6, x_7);
lean_dec(x_5);
return x_23;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_19);
lean_dec(x_19);
lean_inc(x_5);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandDeclId___spec__10(x_18, x_24, x_25, x_2, x_5, x_6, x_7);
lean_dec(x_18);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(x_3, x_1, x_4, x_9, x_27, x_5, x_6, x_28);
lean_dec(x_5);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_10);
x_43 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(x_3, x_1, x_4, x_9, x_2, x_5, x_6, x_7);
lean_dec(x_5);
return x_43;
}
}
}
lean_object* l_Lean_Elab_Command_expandDeclId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Elab_Command_getScope___rarg(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_getLevelNames___rarg(x_4, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1(x_9, x_11, x_1, x_2, x_3, x_4, x_12);
return x_13;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_checkNotAlreadyDeclared___at_Lean_Elab_Command_expandDeclId___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__3(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_mkDeclName___at_Lean_Elab_Command_expandDeclId___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_addDocString_x27___at_Lean_Elab_Command_expandDeclId___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addDocString_x27___at_Lean_Elab_Command_expandDeclId___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at_Lean_Elab_Command_expandDeclId___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandDeclId___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_expandDeclId___spec__10(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_expandDeclId___at_Lean_Elab_Command_expandDeclId___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_expandDeclId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_expandDeclId(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Command(lean_object*);
lean_object* initialize_Lean_ResolveName(lean_object*);
lean_object* initialize_Lean_Meta_Reduce(lean_object*);
lean_object* initialize_Lean_Elab_Log(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object*);
lean_object* initialize_Lean_Elab_DeclModifiers(lean_object*);
lean_object* initialize_Lean_Elab_InfoTree(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Command(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ResolveName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Reduce(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Log(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclModifiers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_Scope_opts___default = _init_l_Lean_Elab_Command_Scope_opts___default();
lean_mark_persistent(l_Lean_Elab_Command_Scope_opts___default);
l_Lean_Elab_Command_Scope_currNamespace___default = _init_l_Lean_Elab_Command_Scope_currNamespace___default();
lean_mark_persistent(l_Lean_Elab_Command_Scope_currNamespace___default);
l_Lean_Elab_Command_Scope_openDecls___default = _init_l_Lean_Elab_Command_Scope_openDecls___default();
lean_mark_persistent(l_Lean_Elab_Command_Scope_openDecls___default);
l_Lean_Elab_Command_Scope_levelNames___default = _init_l_Lean_Elab_Command_Scope_levelNames___default();
lean_mark_persistent(l_Lean_Elab_Command_Scope_levelNames___default);
l_Lean_Elab_Command_Scope_varDecls___default = _init_l_Lean_Elab_Command_Scope_varDecls___default();
lean_mark_persistent(l_Lean_Elab_Command_Scope_varDecls___default);
l_Lean_Elab_Command_instInhabitedScope___closed__1 = _init_l_Lean_Elab_Command_instInhabitedScope___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedScope___closed__1);
l_Lean_Elab_Command_instInhabitedScope = _init_l_Lean_Elab_Command_instInhabitedScope();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedScope);
l_Lean_Elab_Command_State_messages___default = _init_l_Lean_Elab_Command_State_messages___default();
lean_mark_persistent(l_Lean_Elab_Command_State_messages___default);
l_Lean_Elab_Command_State_scopes___default___closed__1 = _init_l_Lean_Elab_Command_State_scopes___default___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_State_scopes___default___closed__1);
l_Lean_Elab_Command_State_scopes___default = _init_l_Lean_Elab_Command_State_scopes___default();
lean_mark_persistent(l_Lean_Elab_Command_State_scopes___default);
l_Lean_Elab_Command_State_nextMacroScope___default = _init_l_Lean_Elab_Command_State_nextMacroScope___default();
lean_mark_persistent(l_Lean_Elab_Command_State_nextMacroScope___default);
l_Lean_Elab_Command_State_nextInstIdx___default = _init_l_Lean_Elab_Command_State_nextInstIdx___default();
lean_mark_persistent(l_Lean_Elab_Command_State_nextInstIdx___default);
l_Lean_Elab_Command_State_ngen___default = _init_l_Lean_Elab_Command_State_ngen___default();
lean_mark_persistent(l_Lean_Elab_Command_State_ngen___default);
l_Lean_Elab_Command_State_infoState___default = _init_l_Lean_Elab_Command_State_infoState___default();
lean_mark_persistent(l_Lean_Elab_Command_State_infoState___default);
l_Lean_Elab_Command_instInhabitedState___closed__1 = _init_l_Lean_Elab_Command_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedState___closed__1);
l_Lean_Elab_Command_instInhabitedState = _init_l_Lean_Elab_Command_instInhabitedState();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedState);
l_Lean_Elab_Command_Context_currRecDepth___default = _init_l_Lean_Elab_Command_Context_currRecDepth___default();
lean_mark_persistent(l_Lean_Elab_Command_Context_currRecDepth___default);
l_Lean_Elab_Command_Context_cmdPos___default = _init_l_Lean_Elab_Command_Context_cmdPos___default();
lean_mark_persistent(l_Lean_Elab_Command_Context_cmdPos___default);
l_Lean_Elab_Command_Context_macroStack___default = _init_l_Lean_Elab_Command_Context_macroStack___default();
lean_mark_persistent(l_Lean_Elab_Command_Context_macroStack___default);
l_Lean_Elab_Command_Context_currMacroScope___default = _init_l_Lean_Elab_Command_Context_currMacroScope___default();
lean_mark_persistent(l_Lean_Elab_Command_Context_currMacroScope___default);
l_Lean_Elab_Command_Context_ref___default = _init_l_Lean_Elab_Command_Context_ref___default();
lean_mark_persistent(l_Lean_Elab_Command_Context_ref___default);
res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_155_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Command_lintersRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Command_lintersRef);
lean_dec_ref(res);
l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__4 = _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_instMonadInfoTreeCommandElabM___closed__4);
l_Lean_Elab_Command_instMonadInfoTreeCommandElabM = _init_l_Lean_Elab_Command_instMonadInfoTreeCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadInfoTreeCommandElabM);
l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__4 = _init_l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_instMonadEnvCommandElabM___closed__4);
l_Lean_Elab_Command_instMonadEnvCommandElabM = _init_l_Lean_Elab_Command_instMonadEnvCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadEnvCommandElabM);
l_Lean_Elab_Command_instMonadOptionsCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadOptionsCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadOptionsCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadOptionsCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadOptionsCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadOptionsCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadOptionsCommandElabM = _init_l_Lean_Elab_Command_instMonadOptionsCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadOptionsCommandElabM);
l_Lean_Elab_Command_instAddMessageContextCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instAddMessageContextCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instAddMessageContextCommandElabM___closed__1);
l_Lean_Elab_Command_instAddMessageContextCommandElabM = _init_l_Lean_Elab_Command_instAddMessageContextCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instAddMessageContextCommandElabM);
l_Lean_Elab_Command_instMonadRefCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadRefCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRefCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadRefCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadRefCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRefCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadRefCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadRefCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRefCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadRefCommandElabM = _init_l_Lean_Elab_Command_instMonadRefCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRefCommandElabM);
l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__4 = _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__4);
l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__5 = _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__5);
l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__6 = _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_instMonadResolveNameCommandElabM___closed__6);
l_Lean_Elab_Command_instMonadResolveNameCommandElabM = _init_l_Lean_Elab_Command_instMonadResolveNameCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadResolveNameCommandElabM);
l_Lean_Elab_Command_instMonadLogCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadLogCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadLogCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadLogCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadLogCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadLogCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadLogCommandElabM___closed__4 = _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_instMonadLogCommandElabM___closed__4);
l_Lean_Elab_Command_instMonadLogCommandElabM___closed__5 = _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_instMonadLogCommandElabM___closed__5);
l_Lean_Elab_Command_instMonadLogCommandElabM___closed__6 = _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_instMonadLogCommandElabM___closed__6);
l_Lean_Elab_Command_instMonadLogCommandElabM___closed__7 = _init_l_Lean_Elab_Command_instMonadLogCommandElabM___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_instMonadLogCommandElabM___closed__7);
l_Lean_Elab_Command_instMonadLogCommandElabM = _init_l_Lean_Elab_Command_instMonadLogCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadLogCommandElabM);
l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__4 = _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_instMonadQuotationCommandElabM___closed__4);
l_Lean_Elab_Command_instMonadQuotationCommandElabM = _init_l_Lean_Elab_Command_instMonadQuotationCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadQuotationCommandElabM);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__1);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__2 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__2);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__3 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__3);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__4 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__4);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__5 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__5);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__6 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__6);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__7 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__7);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__8 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__8);
l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__9 = _init_l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_mkCommandElabAttributeUnsafe___closed__9);
res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1050_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Command_commandElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Command_commandElabAttribute);
lean_dec_ref(res);
l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__4 = _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM___closed__4);
l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM = _init_l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadMacroAdapterCommandElabM);
l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__1);
l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__2 = _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__2);
l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__3 = _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__3);
l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__4 = _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__4);
l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__5 = _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__5);
l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__6 = _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRecDepthCommandElabM___closed__6);
l_Lean_Elab_Command_instMonadRecDepthCommandElabM = _init_l_Lean_Elab_Command_instMonadRecDepthCommandElabM();
lean_mark_persistent(l_Lean_Elab_Command_instMonadRecDepthCommandElabM);
l_Lean_Elab_Command_withLogging___closed__1 = _init_l_Lean_Elab_Command_withLogging___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_withLogging___closed__1);
l_Lean_Elab_Command_withLogging___closed__2 = _init_l_Lean_Elab_Command_withLogging___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_withLogging___closed__2);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1345____closed__1 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1345____closed__1();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1345____closed__1);
res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Command___hyg_1345_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_instInhabitedCommandElabM___closed__1 = _init_l_Lean_Elab_Command_instInhabitedCommandElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedCommandElabM___closed__1);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__1);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext___closed__2);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_mkMetaContext);
l_Lean_Elab_Command_liftTermElabM___rarg___closed__1 = _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_liftTermElabM___rarg___closed__1);
l_Lean_Elab_Command_liftTermElabM___rarg___closed__2 = _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_liftTermElabM___rarg___closed__2);
l_Lean_Elab_Command_liftTermElabM___rarg___closed__3 = _init_l_Lean_Elab_Command_liftTermElabM___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_liftTermElabM___rarg___closed__3);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__1 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__1);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__2 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__2);
l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__3 = _init_l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Command_0__Lean_Elab_Command_addScopes___closed__3);
l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabNamespace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabSection___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSection___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSection___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabSection(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabEnd___lambda__1___closed__1 = _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___lambda__1___closed__1);
l_Lean_Elab_Command_elabEnd___lambda__1___closed__2 = _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___lambda__1___closed__2);
l_Lean_Elab_Command_elabEnd___lambda__1___closed__3 = _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___lambda__1___closed__3);
l_Lean_Elab_Command_elabEnd___lambda__1___closed__4 = _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___lambda__1___closed__4);
l_Lean_Elab_Command_elabEnd___lambda__1___closed__5 = _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___lambda__1___closed__5);
l_Lean_Elab_Command_elabEnd___lambda__1___closed__6 = _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___lambda__1___closed__6);
l_Lean_Elab_Command_elabEnd___closed__1 = _init_l_Lean_Elab_Command_elabEnd___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__1);
l_Lean_Elab_Command_elabEnd___closed__2 = _init_l_Lean_Elab_Command_elabEnd___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__2);
l_Lean_Elab_Command_elabEnd___closed__3 = _init_l_Lean_Elab_Command_elabEnd___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__3);
l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabEnd(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_modifyScope___closed__1 = _init_l_Lean_Elab_Command_modifyScope___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_modifyScope___closed__1);
l_Lean_Elab_Command_modifyScope___closed__2 = _init_l_Lean_Elab_Command_modifyScope___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_modifyScope___closed__2);
l_Lean_Elab_Command_modifyScope___closed__3 = _init_l_Lean_Elab_Command_modifyScope___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_modifyScope___closed__3);
l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elbChoice___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elbChoice(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabUniverse(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverses___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabUniverses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabInitQuot(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_logUnknownDecl___closed__1 = _init_l_Lean_Elab_Command_logUnknownDecl___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_logUnknownDecl___closed__1);
l_Lean_Elab_Command_elabExport___closed__1 = _init_l_Lean_Elab_Command_elabExport___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabExport___closed__1);
l_Lean_Elab_Command_elabExport___closed__2 = _init_l_Lean_Elab_Command_elabExport___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabExport___closed__2);
l_Lean_Elab_Command_elabExport___closed__3 = _init_l_Lean_Elab_Command_elabExport___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabExport___closed__3);
l___regBuiltin_Lean_Elab_Command_elabExport___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabExport(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabOpen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabVariable___lambda__2___closed__1 = _init_l_Lean_Elab_Command_elabVariable___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabVariable___lambda__2___closed__1);
l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabVariable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariables___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabVariables(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabCheck___closed__1 = _init_l_Lean_Elab_Command_elabCheck___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabCheck___closed__1);
l_Lean_Elab_Command_elabCheck___closed__2 = _init_l_Lean_Elab_Command_elabCheck___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabCheck___closed__2);
l_Lean_Elab_Command_elabCheck___closed__3 = _init_l_Lean_Elab_Command_elabCheck___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabCheck___closed__3);
l_Lean_Elab_Command_elabCheck___closed__4 = _init_l_Lean_Elab_Command_elabCheck___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabCheck___closed__4);
l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabCheck(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabReduce___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabReduce___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabReduce___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabReduce(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1 = _init_l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1);
l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2 = _init_l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2);
l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__3 = _init_l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__3);
l_Lean_Elab_Command_failIfSucceeds___closed__1 = _init_l_Lean_Elab_Command_failIfSucceeds___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___closed__1);
l_Lean_Elab_Command_failIfSucceeds___closed__2 = _init_l_Lean_Elab_Command_failIfSucceeds___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___closed__2);
l_Lean_Elab_Command_failIfSucceeds___closed__3 = _init_l_Lean_Elab_Command_failIfSucceeds___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___closed__3);
l_Lean_Elab_Command_failIfSucceeds___closed__4 = _init_l_Lean_Elab_Command_failIfSucceeds___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___closed__4);
l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabCheckFailure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__2 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__2);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__3 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___closed__3);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__2 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__2);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__3 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___closed__3);
l_Lean_Elab_Command_elabEvalUnsafe___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___closed__2 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__2);
l_Lean_Elab_Command_elabEvalUnsafe___closed__3 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__3);
l_Lean_Elab_Command_elabEvalUnsafe___closed__4 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__4);
l_Lean_Elab_Command_elabEvalUnsafe___closed__5 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__5);
l___regBuiltin_Lean_Elab_Command_elabEval___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabEval___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEval___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabEval(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabSynth___lambda__2___closed__1 = _init_l_Lean_Elab_Command_elabSynth___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSynth___lambda__2___closed__1);
l_Lean_Elab_Command_elabSynth___closed__1 = _init_l_Lean_Elab_Command_elabSynth___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSynth___closed__1);
l_Lean_Elab_Command_elabSynth___closed__2 = _init_l_Lean_Elab_Command_elabSynth___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSynth___closed__2);
l_Lean_Elab_Command_elabSynth___closed__3 = _init_l_Lean_Elab_Command_elabSynth___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSynth___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabSynth(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_setOption___closed__1 = _init_l_Lean_Elab_Command_setOption___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_setOption___closed__1);
l_Lean_Elab_Command_setOption___closed__2 = _init_l_Lean_Elab_Command_setOption___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_setOption___closed__2);
l_Lean_Elab_Command_setOption___closed__3 = _init_l_Lean_Elab_Command_setOption___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_setOption___closed__3);
l_Lean_Elab_Command_elabSetOption___closed__1 = _init_l_Lean_Elab_Command_elabSetOption___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSetOption___closed__1);
l_Lean_Elab_Command_elabSetOption___closed__2 = _init_l_Lean_Elab_Command_elabSetOption___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSetOption___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabSetOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1);
res = l___regBuiltin_Lean_Elab_Command_expandInCmd(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
