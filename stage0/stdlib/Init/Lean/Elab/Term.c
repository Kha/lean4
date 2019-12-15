// Lean compiler output
// Module: Init.Lean.Elab.Term
// Imports: Init.Lean.Util.Sorry Init.Lean.Structure Init.Lean.Meta Init.Lean.Hygiene Init.Lean.Elab.Log Init.Lean.Elab.Alias Init.Lean.Elab.ResolveName
#include "runtime/lean.h"
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
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_1__mkMessageAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders(lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__5;
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_9__matchBinder___closed__1;
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_app___elambda__1___closed__1;
uint8_t l_Lean_MessageData_hasSyntheticSorry___main(lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_30__expandApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_13__resolveLocalName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Term_withNode___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__5;
lean_object* l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_23__elabAppFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_31__regTraceClasses(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__3;
extern lean_object* l_Lean_Parser_Term_explicit___elambda__1___closed__2;
extern lean_object* l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
lean_object* l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_exceptionToSorry___closed__3;
lean_object* l_Lean_Elab_Term_elabDepArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__2;
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__8;
lean_object* l_Lean_Elab_Term_State_inhabited;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__9;
lean_object* l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__1;
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__3;
lean_object* l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName(lean_object*);
lean_object* l_Lean_Elab_Term_tracer___closed__5;
lean_object* l_Lean_Elab_Term_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameToExprAux___main___closed__1;
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__1;
extern lean_object* l_Lean_nullKind;
lean_object* l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg___closed__1;
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__8;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__12;
lean_object* l_Lean_Elab_Term_TermElabM_MonadQuotation;
lean_object* l_Lean_Elab_Term_elabDepArrow(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__2;
lean_object* l_Lean_Elab_Term_elabArrow___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_PersistentHashMap_containsAtAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tracer___closed__3;
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_assignExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_hasSorry___main___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__2;
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_27__mergeFailures___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_20__resolveFieldLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType___closed__2;
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen(lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
extern lean_object* l_Lean_List_format___rarg___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_28__elabAppAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__3;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__3;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshId(lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_Elab_Term_elabTerm___closed__7;
lean_object* l_Lean_Elab_Term_elabArrow___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParen(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinder___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_nameToExprAux___main___closed__4;
lean_object* l_List_head_x21___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__2___boxed(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2;
lean_object* l_Lean_Elab_Term_getLocalInsts___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__2(lean_object*);
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__2;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tracingAtPos(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_24__elabAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_28__elabAppAux___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_27__mergeFailures___spec__2(lean_object*);
lean_object* l_Lean_Elab_Term_tracingAt(lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__6;
lean_object* l___private_Init_Lean_Elab_Term_17__elabAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg___closed__1;
lean_object* l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_stxInh;
lean_object* l_Lean_Meta_Exception_toMessageData(lean_object*);
extern lean_object* l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
size_t l_USize_sub(size_t, size_t);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__3;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_11__elabBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__8;
lean_object* l_Lean_Elab_Term_elabSort___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__3;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeInstMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__15;
lean_object* l_Lean_Elab_Term_elabTypeStx___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__5;
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_30__expandApp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getEnv___boxed(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_Elab_Term_elabTerm___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow___closed__3;
lean_object* l_Lean_Elab_Term_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__15(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__4;
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__5;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__6;
lean_object* l_Array_reverseAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabHole(lean_object*);
lean_object* l_Lean_Elab_Term_withoutPostponing(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabForall(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_30__expandApp___closed__1;
lean_object* l_HashMapImp_find___at_Lean_Elab_Term_elabTerm___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParen___closed__3;
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__2;
extern lean_object* l_Lean_Elab_mkElabAttribute___rarg___closed__1;
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__3;
lean_object* l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__1;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_hasToString(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_mkTermElabAttribute___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Term_20__resolveFieldLoop___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache(lean_object*);
lean_object* l_Lean_Elab_Term_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerAttribute(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18;
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabListLit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__4;
lean_object* l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__2;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_27__mergeFailures___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__3;
lean_object* l___private_Init_Lean_Elab_Term_8__expandOptIdent(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__14;
lean_object* l_Lean_Elab_Term_elabSort___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMCtx(lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__6;
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__5;
lean_object* l___private_Init_Lean_Elab_Term_17__elabAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__6;
lean_object* l_Lean_Elab_Term_elabTypeStx___rarg(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__1(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__1;
extern lean_object* l_Lean_Parser_Term_cons___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__2;
lean_object* l_Lean_Elab_Term_dbgTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_22__elabAppFieldsAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__14;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__2;
extern lean_object* l_Lean_Meta_MetaHasEval___rarg___closed__4;
lean_object* l_Lean_Elab_Term_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_Elab_Term_elabTerm___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__1;
lean_object* l_Lean_Elab_Term_NamedArg_inhabited;
lean_object* l_Lean_Elab_Term_Field_hasToString(lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_Lean_Elab_Term_resolveName___closed__5;
lean_object* l_Lean_Elab_Term_mkFreshExprMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabResult_inhabited___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_termElabAttribute___closed__2;
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__11(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getTraceState(lean_object*);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__4;
lean_object* l___private_Init_Lean_Elab_Term_26__toMessageData___closed__2;
lean_object* l_Lean_Elab_Term_elabParen___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_whnf(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_28__elabAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_prop___elambda__1___rarg___closed__2;
lean_object* l_Lean_Elab_Term_elabParen___closed__1;
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__6(lean_object*);
lean_object* l_Lean_Elab_Term_elabListLit___closed__1;
lean_object* l_Lean_Elab_Term_liftMetaM(lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_12__resolveLocalNameAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_7__expandBinderIdent(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_proj___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabListLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_Elab_Term_elabTerm___spec__3___boxed(lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__7;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_tracingAt___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_withNode___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabListLit___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__16;
lean_object* l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_9__matchBinder___closed__3;
lean_object* l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__2;
extern lean_object* l_Lean_Meta_dbgTrace___rarg___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_2__fromMetaException(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_2__fromMetaException___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__16(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_26__toMessageData___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_15__mkConsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_26__toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__10;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__3;
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_14__mkFreshLevelMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_24__elabAppFn___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_appendIndexAfter___closed__1;
lean_object* l_Lean_Elab_Term_addContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__2;
lean_object* l_Lean_Elab_Term_observing(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getTraceState___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_State_inhabited___closed__1;
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_Lean_Elab_Term_dbgTrace(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1;
extern lean_object* l_Lean_Parser_Term_id___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabTerm___closed__6;
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__3(lean_object*, lean_object*);
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLevel(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_10__elabBinderViews___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrNamespace(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__3;
extern lean_object* l_Lean_choiceKind___closed__2;
extern lean_object* l_Lean_Expr_isSyntheticSorry___closed__1;
extern lean_object* l_Lean_MessageData_Inhabited;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshId___boxed(lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__7;
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__10;
lean_object* l_Lean_Elab_Term_isExprMVarAssigned___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabProp___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_consumeDefaultParams___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkHole___closed__1;
lean_object* l_PersistentHashMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__3;
lean_object* l_Lean_Elab_Term_elabId(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_termElabAttribute___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__20;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__12;
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_27__mergeFailures___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__3;
lean_object* l_Lean_Elab_Term_mkHole___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_9__matchBinder___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentHashMap_containsAtAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabParen(lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_15__mkConsts___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_inhabited(lean_object*);
lean_object* l_Lean_Elab_Term_elabForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__6;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__1;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__3;
lean_object* l_Lean_Elab_mkElabAttribute___rarg___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_6__expandBinderType___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__1;
lean_object* l_Lean_Elab_Term_setTraceState___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_21__resolveField___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__7;
lean_object* l_Lean_Elab_Term_mkTermId___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__13;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tracingAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__3;
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_1__mkMessageAux(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Term_withNode___rarg___closed__1;
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUniv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTypeStx(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_exceptionToSorry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__7;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21;
lean_object* l_Lean_Elab_Term_termElabAttribute___closed__3;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Elab_Term_State_inhabited___closed__2;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__5;
lean_object* l_Lean_Elab_Term_withNode___rarg___closed__2;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__3;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_26__toMessageData(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Term_20__resolveFieldLoop___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__3;
lean_object* l_Lean_Elab_Term_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_24__elabAppFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabListLit___closed__4;
extern lean_object* l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_whnfForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Lean_Elab_Term_trySynthInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx(lean_object*);
lean_object* l_Lean_Elab_Term_isClass___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__3;
lean_object* l_Lean_SMap_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tracingAt___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__5;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow(lean_object*);
lean_object* l_Lean_Elab_Term_elabTypeStx___rarg___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshId___rarg(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_27__mergeFailures___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabParen___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
extern lean_object* l_PersistentArray_empty___closed__3;
lean_object* l_Lean_Elab_Term_mkBuiltinTermElabTable(lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabProp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_9__matchBinder___closed__2;
lean_object* lean_metavar_ctx_assign_expr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_consumeDefaultParams___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_13__resolveLocalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyResult___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_mkTermParserAttribute___closed__4;
lean_object* l_Lean_Elab_Term_mkTermElabAttribute(lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__4;
uint8_t l_PersistentHashMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__4(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__7;
lean_object* l_Lean_Elab_Term_TermElabM_MonadQuotation___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_tracingAtPos___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_addBuiltinTermElab___closed__2;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabApp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSort(lean_object*);
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5(lean_object*, size_t, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
extern lean_object* l___private_Init_Lean_Environment_5__envExtensionsRef;
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__5(lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_11__elabBindersAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_29__expandAppAux___main(lean_object*, lean_object*);
extern lean_object* l_List_head_x21___rarg___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__3;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_elabProp(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_arrow___elambda__1___closed__2;
lean_object* l_HashMapImp_expand___at_Lean_Elab_Term_addBuiltinTermElab___spec__13(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__8;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_elabChoice(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find___at_Lean_Elab_Term_elabTerm___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_10__elabBinderViews(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_MonadQuotation___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_22__elabAppFieldsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_15__mkConsts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addBuiltinTermElab___closed__1;
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_whnfCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrNamespace___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_9__matchBinder(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_15__mkConsts___spec__1___closed__1;
lean_object* l___private_Init_Lean_Util_Trace_4__checkTraceOption___at_Lean_Elab_Term_elabTerm___spec__10___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__1;
lean_object* l_Lean_Elab_Term_ensureHasType___closed__1;
lean_object* l_Lean_Elab_Term_addBuiltinTermElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLocalInsts(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProp(lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__7;
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__2;
lean_object* l_Lean_Elab_Term_isClass(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabResult_inhabited;
lean_object* l___private_Init_Lean_Elab_Term_21__resolveField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__11;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__2(lean_object*);
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__1;
lean_object* l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_Term_26__toMessageData___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_6__expandBinderType(lean_object*);
lean_object* l_Lean_Name_replacePrefix___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__9;
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__6;
lean_object* l_Lean_Elab_Term_elabListLit___closed__5;
lean_object* l_Lean_Elab_Term_TermElabM_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__4;
lean_object* l___private_Init_Lean_Elab_Term_27__mergeFailures(lean_object*);
lean_object* l_Lean_Elab_Term_withNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_8__expandOptIdent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabProj(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_setParam___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofArray(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__3;
lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_fix1___rarg___lambda__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toStr___closed__7;
lean_object* l___private_Init_Lean_Elab_Term_11__elabBindersAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUniv___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__2;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__6;
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_tracingAtPos___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLCtx(lean_object*);
lean_object* l_Lean_Elab_Term_withNode(lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Lean_Elab_Term_elabTerm___closed__4;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_20__resolveFieldLoop___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutPostponing___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_4__checkTraceOption___at_Lean_Elab_Term_elabTerm___spec__10(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1;
extern lean_object* l_Lean_Meta_Exception_mkAppTypeMismatchMessage___closed__8;
lean_object* l_Lean_Elab_Term_elabHole(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__1;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId(lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__2;
lean_object* l_Lean_Elab_Term_synthesizeInstMVars(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_tracingAtPos___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4;
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_18__throwFieldError___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_18__throwFieldError___spec__1(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__7;
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l___private_Init_Lean_Elab_Term_14__mkFreshLevelMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__3;
extern lean_object* l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__2;
lean_object* l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTerm___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_tracingAt___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__5;
lean_object* l_AssocList_find___main___at_Lean_Elab_Term_elabTerm___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType___closed__3;
lean_object* l___private_Init_Lean_Elab_Term_18__throwFieldError(lean_object*);
lean_object* l_Lean_registerTagAttribute___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkHole;
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTerm___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logInfoAt___at_Lean_Elab_Term_tracingAtPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkInitAttr___lambda__1___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_tracingAt___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_addNamedArg___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_20__resolveFieldLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_asNode___closed__1;
lean_object* l_Lean_nameToExprAux___main(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__3;
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__19;
uint8_t l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__2;
lean_object* l_Lean_Elab_Term_ensureType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_30__expandApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
extern lean_object* l_Bool_HasRepr___closed__2;
lean_object* l_Lean_Elab_Term_ensureType___closed__2;
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2;
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerSyntheticMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Term_tracer___closed__4;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr(lean_object*);
lean_object* l_Lean_registerTagAttribute___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_tracingAt___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___closed__1;
extern lean_object* l_Lean_Parser_Term_paren___elambda__1___closed__1;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChoice(lean_object*);
lean_object* l_Lean_Elab_Term_ensureType___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__11;
extern lean_object* l_Lean_Parser_Term_app___elambda__1___closed__2;
extern lean_object* l_Lean_EnvExtension_setState___closed__1;
lean_object* l_PersistentHashMap_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__8(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
lean_object* l_Array_filterAux___main___at___private_Init_Lean_Elab_Term_25__getSuccess___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Elab_Term_elabTerm___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_3__fromMetaState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1;
lean_object* l_Lean_Elab_Term_isExprMVarAssigned(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___closed__2;
lean_object* l_Lean_Elab_Term_whnf___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabHole___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_consumeDefaultParams(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_unfoldDefinition_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSort(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkHole___closed__3;
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_Term_elabListLit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_10__elabBinderViews___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__4;
lean_object* l___private_Init_Lean_Elab_Term_20__resolveFieldLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName(lean_object*);
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_30__expandApp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVar___closed__2;
lean_object* l_Lean_Elab_Term_elabTerm___closed__5;
lean_object* l_Lean_Elab_Term_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__1;
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Term_withNode___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVar___closed__1;
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_addNamedArg___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkTermId(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1;
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_namedArgument___elambda__1___rarg___closed__2;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getEnv(lean_object*);
lean_object* l_Lean_Elab_Term_getOpenDecls(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__8;
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_14__mkFreshLevelMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabListLit(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_11__elabBindersAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__4;
lean_object* l_Lean_Elab_Term_tracer___closed__2;
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_withNode___spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__1;
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__1;
extern lean_object* l_Lean_KernelException_toMessageData___closed__12;
lean_object* l_Lean_Syntax_formatStx___main(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_29__expandAppAux(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm___closed__3;
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addBuiltinTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__6;
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__17;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2;
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tracer___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__3;
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOpenDecls___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getTraceState___boxed(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__2;
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tracer___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__4;
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__2;
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__2;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabListLit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVar___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1;
lean_object* l_Lean_Elab_Term_isDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_getLCtx___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__9;
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Util_Trace_3__checkTraceOptionAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_setTraceState(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_tracingAtPos___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Message_Inhabited___closed__2;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__2;
uint8_t l_Lean_Position_DecidableEq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_MonadQuotation___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_withNode___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
uint8_t l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_23__elabAppFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_3__fromMetaState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTerm___spec__4(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__2;
lean_object* l_Lean_Elab_Term_elabListLit___closed__3;
lean_object* l_Lean_Elab_Term_addContext(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_listLit___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_withNode___rarg___closed__3;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__4;
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_withNode___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProj(lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tracer;
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___boxed(lean_object*);
extern lean_object* l_Nat_Inhabited;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__13;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_builtinTermElabTable;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_mkTermElabAttribute___closed__2;
lean_object* l_Lean_Elab_logInfoAt___at_Lean_Elab_Term_tracingAtPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMCtx___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_applyResult(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_14__mkFreshLevelMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__1;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1;
lean_object* l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_Term_26__toMessageData___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrow(lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTerm___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Elab_Term_elabTerm___spec__7___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
lean_object* l___private_Init_Lean_Elab_Term_31__regTraceClasses___closed__1;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__5;
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
extern lean_object* l_HashMap_Inhabited___closed__1;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__5;
extern lean_object* l_Lean_Parser_Term_simpleBinder___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_forall___elambda__1___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__3;
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__1;
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_24__elabAppFn___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_mkTermElabAttribute___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkExplicitBinder___closed__6;
lean_object* l_Lean_SMap_find___at_Lean_Elab_Term_elabTerm___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName___closed__1;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__2;
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCache(lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__12(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__8;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerSyntheticMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_18__throwFieldError___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findField_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_exceptionToSorry___closed__1;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
extern lean_object* l_Lean_initAttr;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_7__expandBinderIdent___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_exceptionToSorry___closed__2;
lean_object* l_Lean_Elab_Term_getOptions___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tracer___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_exceptionToSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_12__resolveLocalNameAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMCtx___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___closed__4;
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__14(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_liftMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__4;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeInstMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkTermElabAttribute___closed__1;
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_10__elabBinderViews___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_type___elambda__1___rarg___closed__2;
lean_object* l___private_Init_Lean_Elab_Term_15__mkConsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_consumeDefaultParams___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Term_25__getSuccess(lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__2;
extern lean_object* l_Lean_Parser_Term_sort___elambda__1___rarg___closed__2;
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Elab_Term_elabTerm___spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinder(lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tracingAtPos___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Lean_Elab_Term_State_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_EnvExtension_setState___closed__1;
x_2 = l_Lean_MetavarContext_Inhabited___closed__1;
x_3 = l_Lean_Meta_MetaHasEval___rarg___closed__4;
x_4 = l_Lean_NameGenerator_Inhabited___closed__3;
x_5 = l_Lean_TraceState_Inhabited___closed__1;
x_6 = l_PersistentArray_empty___closed__3;
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
lean_object* _init_l_Lean_Elab_Term_State_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_State_inhabited___closed__1;
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 4, x_3);
lean_ctor_set(x_4, 5, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_State_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_State_inhabited___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Message_Inhabited___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_SynthInstance_SynthM_inhabited___lambda__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_TermElabM_inhabited___closed__1;
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabResult_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_Inhabited___closed__1;
x_2 = l_Lean_Elab_Term_State_inhabited___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabResult_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_TermElabResult_inhabited___closed__1;
return x_1;
}
}
lean_object* l_ReaderT_read___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_List_head_x21___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Nat_Inhabited;
x_3 = l_List_head_x21___rarg___closed__2;
x_4 = lean_panic_fn(x_3);
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
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__3___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_MonadQuotation___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 8);
x_5 = l_List_head_x21___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__2(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_MonadQuotation___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_6, x_7);
lean_ctor_set(x_4, 5, x_8);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 8);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_3, 8, x_11);
x_12 = lean_apply_2(x_2, x_3, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 6);
x_20 = lean_ctor_get(x_3, 7);
x_21 = lean_ctor_get(x_3, 8);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_15);
lean_ctor_set(x_24, 3, x_16);
lean_ctor_set(x_24, 4, x_17);
lean_ctor_set(x_24, 5, x_18);
lean_ctor_set(x_24, 6, x_19);
lean_ctor_set(x_24, 7, x_20);
lean_ctor_set(x_24, 8, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*9, x_22);
x_25 = lean_apply_2(x_2, x_24, x_4);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
x_28 = lean_ctor_get(x_4, 2);
x_29 = lean_ctor_get(x_4, 3);
x_30 = lean_ctor_get(x_4, 4);
x_31 = lean_ctor_get(x_4, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_31, x_32);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 4, x_30);
lean_ctor_set(x_34, 5, x_33);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_3, 4);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 5);
lean_inc(x_40);
x_41 = lean_ctor_get(x_3, 6);
lean_inc(x_41);
x_42 = lean_ctor_get(x_3, 7);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 8);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 x_45 = x_3;
} else {
 lean_dec_ref(x_3);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_31);
lean_ctor_set(x_46, 1, x_43);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 9, 1);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 3, x_38);
lean_ctor_set(x_47, 4, x_39);
lean_ctor_set(x_47, 5, x_40);
lean_ctor_set(x_47, 6, x_41);
lean_ctor_set(x_47, 7, x_42);
lean_ctor_set(x_47, 8, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*9, x_44);
x_48 = lean_apply_2(x_2, x_47, x_34);
return x_48;
}
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_TermElabM_MonadQuotation___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__1;
x_2 = l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__3___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_TermElabM_MonadQuotation___lambda__2), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__3;
x_2 = l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_MonadQuotation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__5;
return x_1;
}
}
lean_object* l_List_head_x21___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x21___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_MonadQuotation___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_TermElabM_MonadQuotation___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_Field_hasToString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Nat_repr(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
return x_4;
}
}
}
lean_object* l_Lean_Elab_Term_observing(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_3);
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_applyResult(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* l_Lean_Elab_Term_applyResult___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_applyResult(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_3, 2, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
x_14 = lean_ctor_get(x_3, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_13);
lean_ctor_set(x_16, 5, x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_TermElabM_monadLog___lambda__2___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__1;
x_2 = l_Lean_Elab_Term_TermElabM_monadLog___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__3___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_TermElabM_monadLog___lambda__3___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__1;
x_2 = l_Lean_Elab_Term_TermElabM_monadLog___closed__3;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__3___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_TermElabM_monadLog___lambda__4___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__1;
x_2 = l_Lean_Elab_Term_TermElabM_monadLog___closed__5;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_TermElabM_MonadQuotation___spec__3___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_TermElabM_monadLog___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_TermElabM_monadLog___closed__7;
x_2 = l_Lean_Elab_Term_TermElabM_monadLog___closed__2;
x_3 = l_Lean_Elab_Term_TermElabM_monadLog___closed__4;
x_4 = l_Lean_Elab_Term_TermElabM_monadLog___closed__6;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_TermElabM_monadLog() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_TermElabM_monadLog___closed__8;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_TermElabM_monadLog___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_TermElabM_monadLog___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_TermElabM_monadLog___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_monadLog___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_TermElabM_monadLog___lambda__4(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_mkHashMap___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_PersistentHashMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__1;
x_3 = l_PersistentHashMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__2;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_mkBuiltinTermElabTable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
uint8_t l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3(lean_object* x_1, lean_object* x_2) {
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
uint8_t l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_PersistentHashMap_containsAtAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = lean_name_eq(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_2 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = 1;
return x_12;
}
}
}
}
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = x_2 >> x_5;
x_15 = l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5(x_13, x_14, x_3);
lean_dec(x_13);
return x_15;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_PersistentHashMap_containsAtAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__6(x_17, x_18, x_3);
return x_19;
}
}
}
uint8_t l_PersistentHashMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5(x_3, x_4, x_2);
return x_5;
}
}
uint8_t l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2(x_4, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_PersistentHashMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__4(x_5, x_2);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2(x_9, x_2);
return x_10;
}
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__11(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
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
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
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
x_22 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_29 = l_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
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
x_38 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(x_35, x_36, x_37, x_4, x_5);
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
x_43 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
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
x_64 = l_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
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
x_75 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(x_71, x_73, x_74, x_4, x_5);
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
lean_object* x_82; lean_object* x_83; size_t x_84; uint8_t x_85; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__10(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_iterateMAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__11(x_3, x_89, x_90, x_89, x_82, x_91);
lean_dec(x_90);
lean_dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
lean_object* l_PersistentHashMap_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(x_5, x_7, x_8, x_2, x_3);
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
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(x_12, x_14, x_15, x_2, x_3);
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
lean_object* l_AssocList_foldlM___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__15(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__15(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_Elab_Term_addBuiltinTermElab___spec__13(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__14(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__16(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__16(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3(x_2, x_10);
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
x_17 = l_HashMapImp_expand___at_Lean_Elab_Term_addBuiltinTermElab___spec__13(x_13, x_15);
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
x_18 = l_AssocList_replace___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__16(x_2, x_3, x_10);
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
x_26 = l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3(x_2, x_25);
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
x_32 = l_HashMapImp_expand___at_Lean_Elab_Term_addBuiltinTermElab___spec__13(x_28, x_30);
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
x_34 = l_AssocList_replace___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__16(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_SMap_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_PersistentHashMap_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__8(x_6, x_2, x_3);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_PersistentHashMap_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__8(x_9, x_2, x_3);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_4);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_HashMapImp_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__12(x_13, x_2, x_3);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = l_HashMapImp_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__12(x_15, x_2, x_3);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_4);
return x_18;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_addBuiltinTermElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid builtin term elaborator, elaborator for '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_addBuiltinTermElab___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already been defined");
return x_1;
}
}
lean_object* l_Lean_Elab_Term_addBuiltinTermElab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Term_builtinTermElabTable;
x_6 = lean_io_ref_get(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1(x_8, x_1);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_6);
x_11 = lean_io_ref_get(x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_io_ref_reset(x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_SMap_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__7(x_12, x_1, x_3);
x_17 = lean_io_ref_set(x_5, x_16, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_3);
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
uint8_t x_22; 
lean_dec(x_3);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_1);
x_28 = l_Lean_Elab_Term_addBuiltinTermElab___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_addBuiltinTermElab___closed__2;
x_31 = lean_string_append(x_29, x_30);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_31);
return x_6;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_6);
x_34 = l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1(x_32, x_1);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_io_ref_get(x_5, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_io_ref_reset(x_5, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_SMap_insert___at_Lean_Elab_Term_addBuiltinTermElab___spec__7(x_36, x_1, x_3);
x_41 = lean_io_ref_set(x_5, x_40, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_36);
lean_dec(x_3);
lean_dec(x_1);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_44 = x_38;
} else {
 lean_dec_ref(x_38);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
lean_dec(x_1);
x_46 = lean_ctor_get(x_35, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_48 = x_35;
} else {
 lean_dec_ref(x_35);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_3);
x_50 = l_Lean_Name_toString___closed__1;
x_51 = l_Lean_Name_toStringWithSep___main(x_50, x_1);
x_52 = l_Lean_Elab_Term_addBuiltinTermElab___closed__1;
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_54 = l_Lean_Elab_Term_addBuiltinTermElab___closed__2;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_33);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_3);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_6);
if (x_57 == 0)
{
return x_6;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_6, 0);
x_59 = lean_ctor_get(x_6, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_6);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_containsAtAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_PersistentHashMap_containsAtAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__5(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_PersistentHashMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentHashMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_SMap_contains___at_Lean_Elab_Term_addBuiltinTermElab___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__11(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_Elab_Term_addBuiltinTermElab___spec__9(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_addBuiltinTermElab___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_regBuiltinTermElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addBuiltinTermElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__6;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to emit registration code for builtin term elaborator '");
return x_1;
}
}
lean_object* l_Lean_Elab_Term_declareBuiltinTermElab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_5 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__2;
lean_inc(x_3);
x_6 = l_Lean_Name_append___main(x_5, x_3);
x_7 = lean_box(0);
x_8 = l_Lean_nameToExprAux___main(x_2);
lean_inc(x_3);
x_9 = l_Lean_nameToExprAux___main(x_3);
lean_inc(x_3);
x_10 = l_Lean_mkConst(x_3, x_7);
x_11 = l_Lean_Parser_declareBuiltinParser___closed__8;
x_12 = lean_array_push(x_11, x_8);
x_13 = lean_array_push(x_12, x_9);
x_14 = lean_array_push(x_13, x_10);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__7;
x_17 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_14, x_14, x_15, x_16);
lean_dec(x_14);
x_18 = l_Lean_Parser_declareBuiltinParser___closed__7;
lean_inc(x_6);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_7);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_box(0);
x_21 = 0;
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Options_empty;
x_25 = l_Lean_Environment_addAndCompile(x_1, x_24, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_6);
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_3);
x_28 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__8;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Char_HasRepr___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_3);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_34 = l_Lean_initAttr;
x_35 = lean_box(0);
x_36 = l_Lean_ParametricAttribute_setParam___rarg(x_34, x_33, x_6, x_35);
x_37 = l_IO_ofExcept___at_Lean_Parser_declareBuiltinParser___spec__1(x_36, x_4);
lean_dec(x_36);
return x_37;
}
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid attribute 'builtinTermElab', must be persistent");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected term elaborator type at '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' `TermElab` expected");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TermElab");
return x_1;
}
}
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
if (x_4 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_inc(x_1);
x_9 = l_Lean_Elab_syntaxNodeKindOfAttrParam(x_1, x_8, x_3, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_22; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_1);
x_22 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l_Lean_mkInitAttr___lambda__1___closed__1;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Lean_ConstantInfo_type(x_25);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 4)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = l_Lean_nameToExprAux___main___closed__1;
x_37 = lean_string_dec_eq(x_35, x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_10);
lean_dec(x_1);
x_38 = lean_box(0);
x_13 = x_38;
goto block_21;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__1;
x_40 = lean_string_dec_eq(x_34, x_39);
lean_dec(x_34);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_10);
lean_dec(x_1);
x_41 = lean_box(0);
x_13 = x_41;
goto block_21;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__1;
x_43 = lean_string_dec_eq(x_33, x_42);
lean_dec(x_33);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_32);
lean_dec(x_10);
lean_dec(x_1);
x_44 = lean_box(0);
x_13 = x_44;
goto block_21;
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4;
x_46 = lean_string_dec_eq(x_32, x_45);
lean_dec(x_32);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_10);
lean_dec(x_1);
x_47 = lean_box(0);
x_13 = x_47;
goto block_21;
}
else
{
lean_object* x_48; 
lean_dec(x_12);
x_48 = l_Lean_Elab_Term_declareBuiltinTermElab(x_1, x_10, x_2, x_11);
return x_48;
}
}
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_49 = lean_box(0);
x_13 = x_49;
goto block_21;
}
}
else
{
lean_object* x_50; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_50 = lean_box(0);
x_13 = x_50;
goto block_21;
}
}
else
{
lean_object* x_51; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_51 = lean_box(0);
x_13 = x_51;
goto block_21;
}
}
else
{
lean_object* x_52; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_52 = lean_box(0);
x_13 = x_52;
goto block_21;
}
}
else
{
lean_object* x_53; 
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_1);
x_53 = lean_box(0);
x_13 = x_53;
goto block_21;
}
}
else
{
lean_object* x_54; 
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_1);
x_54 = lean_box(0);
x_13 = x_54;
goto block_21;
}
}
block_21:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_14 = l_Lean_Name_toString___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_2);
x_16 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3;
x_19 = lean_string_append(x_17, x_18);
if (lean_is_scalar(x_12)) {
 x_20 = lean_alloc_ctor(1, 2, 0);
} else {
 x_20 = x_12;
 lean_ctor_set_tag(x_20, 1);
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
}
else
{
uint8_t x_55; 
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_9);
if (x_55 == 0)
{
return x_9;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_9, 0);
x_57 = lean_ctor_get(x_9, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_9);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinTermElab");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Builtin term elaborator");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_1 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2;
x_2 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__5;
x_3 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__6;
x_4 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__3;
x_5 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__4;
x_6 = l_Lean_AttributeImpl_inhabited___closed__4;
x_7 = l_Lean_AttributeImpl_inhabited___closed__5;
x_8 = 1;
x_9 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_5);
lean_ctor_set(x_9, 5, x_6);
lean_ctor_set(x_9, 6, x_7);
lean_ctor_set(x_9, 7, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*8, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__7;
x_3 = l_Lean_registerAttribute(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_3);
return x_7;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_mkTermElabAttribute___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_5);
return x_11;
}
}
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_HashMap_Inhabited___closed__1;
x_3 = l_PersistentHashMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_14 = lean_io_ref_get(x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_15);
lean_dec(x_15);
x_18 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__2;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_io_ref_get(x_13, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_io_ref_reset(x_13, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_19);
x_26 = x_19;
x_27 = lean_array_push(x_21, x_26);
x_28 = lean_io_ref_set(x_13, x_27, x_24);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_19);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_19);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_21);
lean_dec(x_19);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
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
lean_dec(x_19);
x_41 = !lean_is_exclusive(x_20);
if (x_41 == 0)
{
return x_20;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_20, 0);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_20);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_14);
if (x_45 == 0)
{
return x_14;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_14, 0);
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_14);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_3);
if (x_49 == 0)
{
return x_3;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_3, 0);
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_3);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_mkTermElabAttribute___spec__3(x_1, x_6, x_6, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_4);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = l_Array_empty___closed__1;
lean_inc(x_11);
x_13 = lean_apply_1(x_11, x_12);
x_14 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_15 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4(x_15, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 4);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_11);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_22);
x_24 = lean_io_ref_get(x_3, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_io_ref_reset(x_3, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_23);
x_30 = x_23;
x_31 = lean_array_push(x_25, x_30);
x_32 = lean_io_ref_set(x_3, x_31, x_28);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_23);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_23);
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
lean_dec(x_25);
lean_dec(x_23);
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
uint8_t x_45; 
lean_dec(x_23);
x_45 = !lean_is_exclusive(x_24);
if (x_45 == 0)
{
return x_24;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_24, 0);
x_47 = lean_ctor_get(x_24, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_24);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_11);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_16);
if (x_49 == 0)
{
return x_16;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_16, 0);
x_51 = lean_ctor_get(x_16, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_16);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
lean_dec(x_1);
x_54 = l_Lean_Name_toString___closed__1;
x_55 = l_Lean_Name_toStringWithSep___main(x_54, x_53);
x_56 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_59 = lean_string_append(x_57, x_58);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_59);
return x_4;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_4, 0);
x_61 = lean_ctor_get(x_4, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_4);
x_62 = lean_array_get_size(x_60);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_mkTermElabAttribute___spec__3(x_1, x_60, x_60, x_62, x_63);
lean_dec(x_62);
lean_dec(x_60);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
x_66 = l_Array_empty___closed__1;
lean_inc(x_65);
x_67 = lean_apply_1(x_65, x_66);
x_68 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_69 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_69, 0, x_67);
lean_closure_set(x_69, 1, x_68);
x_70 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4(x_69, x_61);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_1, 4);
lean_inc(x_76);
lean_dec(x_1);
x_77 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_65);
lean_ctor_set(x_77, 3, x_74);
lean_ctor_set(x_77, 4, x_75);
lean_ctor_set(x_77, 5, x_76);
x_78 = lean_io_ref_get(x_3, x_72);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_io_ref_reset(x_3, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_77);
x_84 = x_77;
x_85 = lean_array_push(x_79, x_84);
x_86 = lean_io_ref_set(x_3, x_85, x_82);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_77);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_77);
x_90 = lean_ctor_get(x_86, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_92 = x_86;
} else {
 lean_dec_ref(x_86);
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
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_79);
lean_dec(x_77);
x_94 = lean_ctor_get(x_81, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_81, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_96 = x_81;
} else {
 lean_dec_ref(x_81);
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
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_77);
x_98 = lean_ctor_get(x_78, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_78, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_100 = x_78;
} else {
 lean_dec_ref(x_78);
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
lean_dec(x_65);
lean_dec(x_1);
x_102 = lean_ctor_get(x_70, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_70, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_104 = x_70;
} else {
 lean_dec_ref(x_70);
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
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_ctor_get(x_1, 0);
lean_inc(x_106);
lean_dec(x_1);
x_107 = l_Lean_Name_toString___closed__1;
x_108 = l_Lean_Name_toStringWithSep___main(x_107, x_106);
x_109 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_110 = lean_string_append(x_109, x_108);
lean_dec(x_108);
x_111 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_112 = lean_string_append(x_110, x_111);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_61);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_4);
if (x_114 == 0)
{
return x_4;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_4, 0);
x_116 = lean_ctor_get(x_4, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_4);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
lean_object* _init_l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_fix1___rarg___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_3);
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_mkElabAttribute___rarg___lambda__2___boxed), 2, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1;
x_8 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set(x_9, 4, x_6);
x_10 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__2(x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Elab_mkElabAttribute___rarg___closed__1;
lean_inc(x_2);
x_14 = lean_string_append(x_2, x_13);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = l_Lean_AttributeImpl_inhabited___closed__1;
x_18 = l_Lean_AttributeImpl_inhabited___closed__4;
x_19 = l_Lean_AttributeImpl_inhabited___closed__5;
x_20 = 0;
x_21 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_15);
lean_ctor_set(x_21, 4, x_16);
lean_ctor_set(x_21, 5, x_18);
lean_ctor_set(x_21, 6, x_19);
lean_ctor_set(x_21, 7, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*8, x_20);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_2);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = l_Lean_Elab_mkElabAttribute___rarg___closed__1;
lean_inc(x_2);
x_26 = lean_string_append(x_2, x_25);
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__5___boxed), 5, 1);
lean_closure_set(x_27, 0, x_1);
lean_inc(x_1);
x_28 = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lambda__6___boxed), 5, 1);
lean_closure_set(x_28, 0, x_1);
x_29 = l_Lean_AttributeImpl_inhabited___closed__1;
x_30 = l_Lean_AttributeImpl_inhabited___closed__4;
x_31 = l_Lean_AttributeImpl_inhabited___closed__5;
x_32 = 0;
x_33 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set(x_33, 3, x_27);
lean_ctor_set(x_33, 4, x_28);
lean_ctor_set(x_33, 5, x_30);
lean_ctor_set(x_33, 6, x_31);
lean_ctor_set(x_33, 7, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*8, x_32);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_34, 2, x_2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_10);
if (x_36 == 0)
{
return x_10;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_10, 0);
x_38 = lean_ctor_get(x_10, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_10);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabTerm");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_mkTermElabAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_mkTermElabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_mkTermElabAttribute___closed__2;
x_3 = l_Lean_Parser_mkTermParserAttribute___closed__4;
x_4 = l_Lean_Elab_Term_builtinTermElabTable;
x_5 = l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_mkTermElabAttribute___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_mkTermElabAttribute___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Term_termElabAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_termElabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Term_termElabAttribute___closed__1;
x_2 = lean_box(0);
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_4 = l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1;
x_5 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_6 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
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
lean_object* _init_l_Lean_Elab_Term_termElabAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_AttributeImpl_inhabited___closed__6;
x_2 = l_Lean_Elab_Term_termElabAttribute___closed__2;
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getEnv___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_getEnv___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_getEnv(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_getMCtx___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getMCtx___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_getMCtx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_getMCtx(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_getCurrNamespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getCurrNamespace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_getCurrNamespace(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_getOpenDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 6);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getOpenDecls___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_getOpenDecls(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_getLCtx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_getLCtx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_getLCtx(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_getLocalInsts(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_getLocalInsts___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_getLocalInsts(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_getOptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_getOptions___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_getOptions(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_getTraceState___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getTraceState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getTraceState___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_getTraceState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_getTraceState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_setTraceState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 4);
lean_dec(x_7);
lean_ctor_set(x_5, 4, x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_5, 2);
x_13 = lean_ctor_get(x_5, 3);
x_14 = lean_ctor_get(x_5, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_13);
lean_ctor_set(x_15, 4, x_1);
lean_ctor_set(x_15, 5, x_14);
lean_ctor_set(x_3, 0, x_15);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
x_23 = lean_ctor_get(x_3, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_18, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 5);
lean_inc(x_28);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 lean_ctor_release(x_18, 5);
 x_29 = x_18;
} else {
 lean_dec_ref(x_18);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 6, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_30, 3, x_27);
lean_ctor_set(x_30, 4, x_1);
lean_ctor_set(x_30, 5, x_28);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_19);
lean_ctor_set(x_31, 2, x_20);
lean_ctor_set(x_31, 3, x_21);
lean_ctor_set(x_31, 4, x_22);
lean_ctor_set(x_31, 5, x_23);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
lean_object* l_Lean_Elab_Term_setTraceState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_setTraceState(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_isExprMVarAssigned(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_getMCtx___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_metavar_ctx_is_expr_assigned(x_6, x_1);
x_8 = lean_box(x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_metavar_ctx_is_expr_assigned(x_9, x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
lean_object* l_Lean_Elab_Term_isExprMVarAssigned___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_isExprMVarAssigned(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_getMCtx___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_MetavarContext_getDecl(x_6, x_1);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_Lean_MetavarContext_getDecl(x_8, x_1);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Elab_Term_getMVarDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_getMVarDecl(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_assignExprMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_metavar_ctx_assign_expr(x_8, x_1, x_2);
lean_ctor_set(x_6, 1, x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 2);
x_15 = lean_ctor_get(x_6, 3);
x_16 = lean_ctor_get(x_6, 4);
x_17 = lean_ctor_get(x_6, 5);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_18 = lean_metavar_ctx_assign_expr(x_13, x_1, x_2);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_16);
lean_ctor_set(x_19, 5, x_17);
lean_ctor_set(x_4, 0, x_19);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 2);
x_25 = lean_ctor_get(x_4, 3);
x_26 = lean_ctor_get(x_4, 4);
x_27 = lean_ctor_get(x_4, 5);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_22, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_22, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_22, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_22, 5);
lean_inc(x_33);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 lean_ctor_release(x_22, 4);
 lean_ctor_release(x_22, 5);
 x_34 = x_22;
} else {
 lean_dec_ref(x_22);
 x_34 = lean_box(0);
}
x_35 = lean_metavar_ctx_assign_expr(x_29, x_1, x_2);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 6, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_32);
lean_ctor_set(x_36, 5, x_33);
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 2, x_24);
lean_ctor_set(x_37, 3, x_25);
lean_ctor_set(x_37, 4, x_26);
lean_ctor_set(x_37, 5, x_27);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
lean_object* l_Lean_Elab_Term_assignExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_assignExprMVar(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_addContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_alloc_ctor(5, 4, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_addContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_addContext(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_tracer___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_apply_1(x_1, x_7);
lean_ctor_set(x_5, 4, x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
x_16 = lean_ctor_get(x_5, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_17 = lean_apply_1(x_1, x_15);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_17);
lean_ctor_set(x_18, 5, x_16);
lean_ctor_set(x_3, 0, x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
x_26 = lean_ctor_get(x_3, 5);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_21, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_21, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_21, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_21, 5);
lean_inc(x_32);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 lean_ctor_release(x_21, 5);
 x_33 = x_21;
} else {
 lean_dec_ref(x_21);
 x_33 = lean_box(0);
}
x_34 = lean_apply_1(x_1, x_31);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 6, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_24);
lean_ctor_set(x_36, 4, x_25);
lean_ctor_set(x_36, 5, x_26);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
lean_object* _init_l_Lean_Elab_Term_tracer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getOptions___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_tracer___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_tracer___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_tracer___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_getTraceState___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_tracer___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_addContext___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_tracer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_tracer___closed__1;
x_2 = l_Lean_Elab_Term_tracer___closed__2;
x_3 = l_Lean_Elab_Term_tracer___closed__3;
x_4 = l_Lean_Elab_Term_tracer___closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_tracer() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_tracer___closed__5;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_tracer___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_tracer___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_dbgTrace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_apply_1(x_1, x_2);
x_6 = l_Lean_Meta_dbgTrace___rarg___closed__1;
x_7 = lean_dbg_trace(x_5, x_6);
x_8 = lean_apply_2(x_7, x_3, x_4);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_dbgTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_dbgTrace___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_1__mkMessageAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = l_Lean_Syntax_getPos(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Elab_mkMessageCore(x_5, x_6, x_3, x_4, x_8);
lean_dec(x_8);
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
lean_dec(x_10);
lean_dec(x_6);
return x_11;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_1__mkMessageAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l___private_Init_Lean_Elab_Term_1__mkMessageAux(x_1, x_2, x_3, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Term_2__fromMetaException(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = l_Lean_Meta_Exception_toMessageData(x_3);
x_5 = 2;
x_6 = l___private_Init_Lean_Elab_Term_1__mkMessageAux(x_1, x_2, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Term_2__fromMetaException___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = 0;
lean_inc(x_2);
x_11 = l___private_Init_Lean_Elab_Term_1__mkMessageAux(x_2, x_1, x_9, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_5 = x_14;
x_6 = x_12;
goto _start;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_3__fromMetaState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 5);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 0);
lean_dec(x_15);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__1(x_1, x_2, x_4, x_12, x_16, x_14);
lean_dec(x_12);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_4, 5);
lean_dec(x_19);
x_20 = lean_ctor_get(x_4, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_4, 3);
lean_dec(x_21);
x_22 = lean_ctor_get(x_4, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
lean_ctor_set(x_4, 4, x_5);
lean_ctor_set(x_3, 2, x_17);
lean_ctor_set(x_3, 0, x_4);
return x_3;
}
else
{
lean_object* x_25; 
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_7);
lean_ctor_set(x_25, 2, x_8);
lean_ctor_set(x_25, 3, x_9);
lean_ctor_set(x_25, 4, x_5);
lean_ctor_set(x_25, 5, x_11);
lean_ctor_set(x_3, 2, x_17);
lean_ctor_set(x_3, 0, x_25);
return x_3;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_3, 1);
x_27 = lean_ctor_get(x_3, 2);
x_28 = lean_ctor_get(x_3, 3);
x_29 = lean_ctor_get(x_3, 4);
x_30 = lean_ctor_get(x_3, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_3);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__1(x_1, x_2, x_4, x_12, x_31, x_27);
lean_dec(x_12);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_33 = x_4;
} else {
 lean_dec_ref(x_4);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 6, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_7);
lean_ctor_set(x_34, 2, x_8);
lean_ctor_set(x_34, 3, x_9);
lean_ctor_set(x_34, 4, x_5);
lean_ctor_set(x_34, 5, x_11);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_28);
lean_ctor_set(x_35, 4, x_29);
lean_ctor_set(x_35, 5, x_30);
return x_35;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_3__fromMetaState___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_Term_3__fromMetaState___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_liftMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = lean_apply_2(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_3);
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
lean_inc(x_3);
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = l_Lean_TraceState_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_33);
x_37 = lean_apply_2(x_2, x_34, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
lean_inc(x_3);
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_liftMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_liftMetaM___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_liftMetaM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_liftMetaM___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_isDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_6, 4, x_10);
x_11 = l_Lean_Meta_isExprDefEq(x_2, x_3, x_9, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_13, x_8);
lean_ctor_set(x_11, 1, x_14);
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
x_17 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_16, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_4);
x_22 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_20);
x_23 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_21, x_8);
lean_ctor_set(x_11, 1, x_23);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
lean_inc(x_4);
x_26 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_24);
x_27 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_25, x_8);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_ctor_get(x_6, 1);
x_31 = lean_ctor_get(x_6, 2);
x_32 = lean_ctor_get(x_6, 3);
x_33 = lean_ctor_get(x_6, 4);
x_34 = lean_ctor_get(x_6, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_6);
x_35 = lean_ctor_get(x_4, 0);
lean_inc(x_35);
x_36 = l_Lean_TraceState_Inhabited___closed__1;
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_34);
x_38 = l_Lean_Meta_isExprDefEq(x_2, x_3, x_35, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_40, x_33);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_46 = x_38;
} else {
 lean_dec_ref(x_38);
 x_46 = lean_box(0);
}
lean_inc(x_4);
x_47 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_44);
x_48 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_45, x_33);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l_Lean_Elab_Term_isDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_isDefEq(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_Meta_inferType(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_3);
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
lean_inc(x_3);
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = l_Lean_TraceState_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_33);
x_37 = l_Lean_Meta_inferType(x_2, x_34, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
lean_inc(x_3);
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_inferType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_inferType(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_whnf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_Meta_whnf(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_3);
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
lean_inc(x_3);
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = l_Lean_TraceState_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_33);
x_37 = l_Lean_Meta_whnf(x_2, x_34, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
lean_inc(x_3);
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_whnf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_whnf(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_whnfForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_Meta_whnfForall(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_3);
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
lean_inc(x_3);
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = l_Lean_TraceState_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_33);
x_37 = l_Lean_Meta_whnfForall(x_2, x_34, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
lean_inc(x_3);
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_whnfForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_whnfForall(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_whnfCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_3);
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
lean_inc(x_3);
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = l_Lean_TraceState_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_33);
x_37 = l_Lean_WHNF_whnfCore___main___at_Lean_Meta_whnfCore___spec__1(x_2, x_34, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
lean_inc(x_3);
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_whnfCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_whnfCore(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_unfoldDefinition_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_3);
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
lean_inc(x_3);
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = l_Lean_TraceState_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_33);
x_37 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_2, x_34, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
lean_inc(x_3);
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_unfoldDefinition_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_unfoldDefinition_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_Meta_instantiateMVars(x_2, x_8, x_5);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_5, 2);
x_21 = lean_ctor_get(x_5, 3);
x_22 = lean_ctor_get(x_5, 4);
x_23 = lean_ctor_get(x_5, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
x_25 = l_Lean_TraceState_Inhabited___closed__1;
x_26 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_19);
lean_ctor_set(x_26, 2, x_20);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set(x_26, 5, x_23);
x_27 = l_Lean_Meta_instantiateMVars(x_2, x_24, x_26);
lean_dec(x_24);
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
x_31 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_29, x_22);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
lean_object* l_Lean_Elab_Term_instantiateMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_instantiateMVars(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_isClass(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_Meta_isClass(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_3);
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
lean_inc(x_3);
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = l_Lean_TraceState_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_33);
x_37 = l_Lean_Meta_isClass(x_2, x_34, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
lean_inc(x_3);
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_isClass___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_isClass(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 4);
x_7 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_4, 4, x_7);
x_8 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_2, x_3, x_10, x_6);
lean_ctor_set(x_8, 1, x_11);
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
x_14 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_2, x_3, x_13, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 2);
x_19 = lean_ctor_get(x_4, 3);
x_20 = lean_ctor_get(x_4, 4);
x_21 = lean_ctor_get(x_4, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_22 = l_Lean_TraceState_Inhabited___closed__1;
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set(x_23, 5, x_21);
x_24 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_2, x_3, x_26, x_20);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_mkFreshLevelMVar(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_mkFreshExprMVar(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_7, 4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_7, 4, x_11);
x_12 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_mkSort(x_13);
x_16 = l_Lean_Meta_mkFreshExprMVar(x_15, x_4, x_3, x_10, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_5, x_6, x_18, x_9);
lean_ctor_set(x_16, 1, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_5, x_6, x_21, x_9);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
x_26 = lean_ctor_get(x_7, 2);
x_27 = lean_ctor_get(x_7, 3);
x_28 = lean_ctor_get(x_7, 4);
x_29 = lean_ctor_get(x_7, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_30 = lean_ctor_get(x_5, 0);
lean_inc(x_30);
x_31 = l_Lean_TraceState_Inhabited___closed__1;
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_25);
lean_ctor_set(x_32, 2, x_26);
lean_ctor_set(x_32, 3, x_27);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_29);
x_33 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_mkSort(x_34);
x_37 = l_Lean_Meta_mkFreshExprMVar(x_36, x_4, x_3, x_30, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_5, x_6, x_39, x_28);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_6, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_43, 4);
x_47 = lean_ctor_get(x_5, 0);
lean_inc(x_47);
x_48 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_43, 4, x_48);
x_49 = l_Lean_Meta_mkFreshExprMVar(x_44, x_4, x_3, x_47, x_43);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 1);
x_52 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_5, x_6, x_51, x_46);
lean_ctor_set(x_49, 1, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_5, x_6, x_54, x_46);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_57 = lean_ctor_get(x_43, 0);
x_58 = lean_ctor_get(x_43, 1);
x_59 = lean_ctor_get(x_43, 2);
x_60 = lean_ctor_get(x_43, 3);
x_61 = lean_ctor_get(x_43, 4);
x_62 = lean_ctor_get(x_43, 5);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_43);
x_63 = lean_ctor_get(x_5, 0);
lean_inc(x_63);
x_64 = l_Lean_TraceState_Inhabited___closed__1;
x_65 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_65, 0, x_57);
lean_ctor_set(x_65, 1, x_58);
lean_ctor_set(x_65, 2, x_59);
lean_ctor_set(x_65, 3, x_60);
lean_ctor_set(x_65, 4, x_64);
lean_ctor_set(x_65, 5, x_62);
x_66 = l_Lean_Meta_mkFreshExprMVar(x_44, x_4, x_3, x_63, x_65);
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
x_70 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_5, x_6, x_68, x_61);
if (lean_is_scalar(x_69)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_69;
}
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshExprMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_getLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Lean_Meta_getLevel(x_2, x_8, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_12, x_7);
lean_ctor_set(x_10, 1, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_15, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_3);
x_21 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_19);
x_22 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_20, x_7);
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
lean_inc(x_3);
x_25 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_23);
x_26 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_24, x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_5, 2);
x_31 = lean_ctor_get(x_5, 3);
x_32 = lean_ctor_get(x_5, 4);
x_33 = lean_ctor_get(x_5, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = l_Lean_TraceState_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_33);
x_37 = l_Lean_Meta_getLevel(x_2, x_34, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_39, x_32);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
lean_inc(x_3);
x_46 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_43);
x_47 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_44, x_32);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_getLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_getLevel(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_mkForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_6, 4, x_10);
x_11 = l_Lean_Meta_mkForall(x_2, x_3, x_9, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_13, x_8);
lean_ctor_set(x_11, 1, x_14);
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
x_17 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_16, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_4);
x_22 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_20);
x_23 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_21, x_8);
lean_ctor_set(x_11, 1, x_23);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
lean_inc(x_4);
x_26 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_24);
x_27 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_25, x_8);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_ctor_get(x_6, 1);
x_31 = lean_ctor_get(x_6, 2);
x_32 = lean_ctor_get(x_6, 3);
x_33 = lean_ctor_get(x_6, 4);
x_34 = lean_ctor_get(x_6, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_6);
x_35 = lean_ctor_get(x_4, 0);
lean_inc(x_35);
x_36 = l_Lean_TraceState_Inhabited___closed__1;
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_34);
x_38 = l_Lean_Meta_mkForall(x_2, x_3, x_35, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_40, x_33);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_46 = x_38;
} else {
 lean_dec_ref(x_38);
 x_46 = lean_box(0);
}
lean_inc(x_4);
x_47 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_4, x_1, x_44);
x_48 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_4, x_5, x_45, x_33);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l_Lean_Elab_Term_mkForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_mkForall(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_trySynthInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = lean_unsigned_to_nat(10000u);
x_11 = l_Lean_Meta_trySynthInstance(x_2, x_10, x_8, x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_13, x_7);
lean_ctor_set(x_11, 1, x_14);
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
x_17 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_16, x_7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_3);
x_22 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_20);
x_23 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_21, x_7);
lean_ctor_set(x_11, 1, x_23);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
lean_inc(x_3);
x_26 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_24);
x_27 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_25, x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 2);
x_32 = lean_ctor_get(x_5, 3);
x_33 = lean_ctor_get(x_5, 4);
x_34 = lean_ctor_get(x_5, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = l_Lean_TraceState_Inhabited___closed__1;
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_34);
x_38 = lean_unsigned_to_nat(10000u);
x_39 = l_Lean_Meta_trySynthInstance(x_2, x_38, x_35, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_41, x_33);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_47 = x_39;
} else {
 lean_dec_ref(x_39);
 x_47 = lean_box(0);
}
lean_inc(x_3);
x_48 = l___private_Init_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_45);
x_49 = l___private_Init_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_46, x_33);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
lean_object* l_Lean_Elab_Term_trySynthInstance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_trySynthInstance(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_registerSyntheticMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_3);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_5, 1, x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
x_16 = lean_ctor_get(x_5, 4);
x_17 = lean_ctor_get(x_5, 5);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_3);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set(x_20, 3, x_15);
lean_ctor_set(x_20, 4, x_16);
lean_ctor_set(x_20, 5, x_17);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_Elab_Term_registerSyntheticMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_registerSyntheticMVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_withoutPostponing___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
lean_ctor_set_uint8(x_2, sizeof(void*)*9, x_5);
x_6 = lean_apply_2(x_1, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_16 = 0;
x_17 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
lean_ctor_set(x_17, 2, x_9);
lean_ctor_set(x_17, 3, x_10);
lean_ctor_set(x_17, 4, x_11);
lean_ctor_set(x_17, 5, x_12);
lean_ctor_set(x_17, 6, x_13);
lean_ctor_set(x_17, 7, x_14);
lean_ctor_set(x_17, 8, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*9, x_16);
x_18 = lean_apply_2(x_1, x_17, x_3);
return x_18;
}
}
}
lean_object* l_Lean_Elab_Term_withoutPostponing(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutPostponing___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_withNode___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getPos(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
}
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_withNode___spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_box(0);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_FileMap_toPosition(x_6, x_8);
x_11 = l_String_splitAux___main___closed__1;
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set(x_12, 4, x_1);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = l_Lean_FileMap_toPosition(x_6, x_14);
x_16 = l_String_splitAux___main___closed__1;
lean_inc(x_7);
x_17 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_9);
lean_ctor_set(x_17, 3, x_16);
lean_ctor_set(x_17, 4, x_1);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
}
}
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Term_withNode___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Elab_getPos___at_Lean_Elab_Term_withNode___spec__3(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_withNode___spec__4(x_1, x_2, x_9, x_4, x_8);
lean_dec(x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 2;
x_6 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_withNode___spec__2(x_2, x_5, x_1, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 2;
x_6 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_withNode___spec__2(x_2, x_5, x_1, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__5___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 2;
x_6 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_withNode___spec__2(x_2, x_5, x_1, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__6___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_withNode___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("term elaborator failed, unexpected syntax");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_withNode___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_withNode___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_withNode___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_withNode___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_withNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = l_Lean_Elab_Term_withNode___rarg___closed__3;
x_6 = l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__1___rarg(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
case 1:
{
lean_object* x_7; 
x_7 = lean_apply_3(x_2, x_1, x_3, x_4);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = l_Lean_Elab_Term_withNode___rarg___closed__3;
x_9 = l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__5___rarg(x_1, x_8, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = l_Lean_Elab_Term_withNode___rarg___closed__3;
x_11 = l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__6___rarg(x_1, x_10, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
}
}
lean_object* l_Lean_Elab_Term_withNode(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withNode___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_withNode___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getPos___at_Lean_Elab_Term_withNode___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_withNode___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_withNode___spec__4(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Term_withNode___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_withNode___spec__2(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__5___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwError___at_Lean_Elab_Term_withNode___spec__6___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_Elab_mkMessageAt___at_Lean_Elab_Term_withNode___spec__4(x_3, x_2, x_6, x_4, x_5);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_9, 2);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_9, 2, x_13);
x_14 = lean_box(0);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_18);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set(x_23, 5, x_21);
x_24 = lean_box(0);
lean_ctor_set(x_7, 1, x_23);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_7, 1);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_inc(x_26);
lean_dec(x_7);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 5);
lean_inc(x_32);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 lean_ctor_release(x_25, 5);
 x_33 = x_25;
} else {
 lean_dec_ref(x_25);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_29);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 6, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_30);
lean_ctor_set(x_35, 4, x_31);
lean_ctor_set(x_35, 5, x_32);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
lean_object* l_Lean_Elab_logInfoAt___at_Lean_Elab_Term_tracingAtPos___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_tracingAtPos___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = 0;
lean_inc(x_1);
x_14 = l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(x_1, x_13, x_10, x_4, x_5);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_3 = x_12;
x_5 = x_15;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_tracingAtPos___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = 0;
lean_inc(x_1);
x_14 = l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(x_1, x_13, x_10, x_4, x_5);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_3 = x_12;
x_5 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Term_tracingAtPos___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_26; 
x_5 = l_Lean_Elab_Term_getTraceState___rarg(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_TraceState_Inhabited___closed__1;
x_9 = l_Lean_Elab_Term_setTraceState(x_8, x_3, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_3);
x_26 = lean_apply_2(x_2, x_3, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_Term_getTraceState___rarg(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Array_forMAux___main___at_Lean_Elab_Term_tracingAtPos___spec__4(x_1, x_32, x_33, x_3, x_31);
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Elab_Term_setTraceState(x_6, x_3, x_35);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_27);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_26, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_dec(x_26);
x_11 = x_41;
x_12 = x_42;
goto block_25;
}
block_25:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = l_Lean_Elab_Term_getTraceState___rarg(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_forMAux___main___at_Lean_Elab_Term_tracingAtPos___spec__3(x_1, x_16, x_17, x_3, x_15);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Elab_Term_setTraceState(x_6, x_3, x_19);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Elab_Term_tracingAtPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_tracingAtPos___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_Elab_logInfoAt___at_Lean_Elab_Term_tracingAtPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_logInfoAt___at_Lean_Elab_Term_tracingAtPos___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_tracingAtPos___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Term_tracingAtPos___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_tracingAtPos___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Term_tracingAtPos___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_tracingAt___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = 0;
lean_inc(x_1);
x_14 = l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(x_1, x_13, x_10, x_4, x_5);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_3 = x_12;
x_5 = x_15;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_tracingAt___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = 0;
lean_inc(x_1);
x_14 = l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(x_1, x_13, x_10, x_4, x_5);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_3 = x_12;
x_5 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Term_tracingAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_Syntax_getPos(x_1);
x_6 = l_Lean_Elab_Term_getTraceState___rarg(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_6, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_6, 1);
lean_inc(x_47);
lean_dec(x_6);
x_48 = lean_ctor_get(x_3, 3);
lean_inc(x_48);
x_7 = x_48;
x_8 = x_46;
x_9 = x_47;
goto block_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_5, 0);
lean_inc(x_49);
lean_dec(x_5);
x_50 = lean_ctor_get(x_6, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_6, 1);
lean_inc(x_51);
lean_dec(x_6);
x_7 = x_49;
x_8 = x_50;
x_9 = x_51;
goto block_45;
}
block_45:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_28; 
x_10 = l_Lean_TraceState_Inhabited___closed__1;
x_11 = l_Lean_Elab_Term_setTraceState(x_10, x_3, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_3);
x_28 = lean_apply_2(x_2, x_3, x_12);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Term_getTraceState___rarg(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Array_forMAux___main___at_Lean_Elab_Term_tracingAt___spec__2(x_7, x_34, x_35, x_3, x_33);
lean_dec(x_34);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_Elab_Term_setTraceState(x_8, x_3, x_37);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_29);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_28, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_dec(x_28);
x_13 = x_43;
x_14 = x_44;
goto block_27;
}
block_27:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = l_Lean_Elab_Term_getTraceState___rarg(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_forMAux___main___at_Lean_Elab_Term_tracingAt___spec__1(x_7, x_18, x_19, x_3, x_17);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Elab_Term_setTraceState(x_8, x_3, x_21);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_13);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_tracingAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_tracingAt___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_tracingAt___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Term_tracingAt___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_tracingAt___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Term_tracingAt___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_tracingAt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_tracingAt___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_exceptionToSorry___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_isSyntheticSorry___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_exceptionToSorry___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_exceptionToSorry___closed__1;
x_2 = l_Bool_HasRepr___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_exceptionToSorry___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_exceptionToSorry___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_exceptionToSorry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = 0;
x_58 = lean_box(0);
lean_inc(x_4);
x_59 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_3, x_57, x_58, x_4, x_5);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_6 = x_60;
x_7 = x_61;
goto block_56;
}
else
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_3, 0);
lean_inc(x_62);
lean_dec(x_3);
x_6 = x_62;
x_7 = x_5;
goto block_56;
}
block_56:
{
lean_object* x_8; 
lean_inc(x_6);
x_8 = l_Lean_Elab_Term_getLevel(x_1, x_6, x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Expr_hasSorry___main___closed__1;
x_15 = l_Lean_mkConst(x_14, x_13);
x_16 = l_Lean_Elab_Term_exceptionToSorry___closed__3;
x_17 = l_Lean_mkAppB(x_15, x_6, x_16);
x_18 = lean_ctor_get(x_2, 4);
lean_inc(x_18);
x_19 = l_Lean_MessageData_hasSyntheticSorry___main(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 2);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_11, 2, x_22);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get(x_11, 4);
x_28 = lean_ctor_get(x_11, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_25);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_27);
lean_ctor_set(x_30, 5, x_28);
lean_ctor_set(x_8, 1, x_30);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
}
else
{
lean_dec(x_2);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Expr_hasSorry___main___closed__1;
x_36 = l_Lean_mkConst(x_35, x_34);
x_37 = l_Lean_Elab_Term_exceptionToSorry___closed__3;
x_38 = l_Lean_mkAppB(x_36, x_6, x_37);
x_39 = lean_ctor_get(x_2, 4);
lean_inc(x_39);
x_40 = l_Lean_MessageData_hasSyntheticSorry___main(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_32, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_32, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_32, 4);
lean_inc(x_45);
x_46 = lean_ctor_get(x_32, 5);
lean_inc(x_46);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 lean_ctor_release(x_32, 5);
 x_47 = x_32;
} else {
 lean_dec_ref(x_32);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_2);
lean_ctor_set(x_48, 1, x_43);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 6, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_44);
lean_ctor_set(x_49, 4, x_45);
lean_ctor_set(x_49, 5, x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_38);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_38);
lean_ctor_set(x_51, 1, x_32);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_6);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_8);
if (x_52 == 0)
{
return x_8;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_8, 0);
x_54 = lean_ctor_get(x_8, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_8);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_exceptionToSorry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_exceptionToSorry(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 2;
x_6 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_withNode___spec__2(x_2, x_5, x_1, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTerm___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTerm___spec__4(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
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
lean_object* x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_18 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTerm___spec__4(x_16, x_17, x_3);
lean_dec(x_16);
return x_18;
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
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTerm___spec__5(x_20, x_21, lean_box(0), x_22, x_3);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find___at_Lean_Elab_Term_elabTerm___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTerm___spec__4(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_Term_elabTerm___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find___at_Lean_Elab_Term_elabTerm___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_Elab_Term_elabTerm___spec__7(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find___at_Lean_Elab_Term_elabTerm___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_PersistentHashMap_find___at_Lean_Elab_Term_elabTerm___spec__3(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_HashMapImp_find___at_Lean_Elab_Term_elabTerm___spec__6(x_4, x_2);
return x_7;
}
else
{
return x_6;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_HashMapImp_find___at_Lean_Elab_Term_elabTerm___spec__6(x_8, x_2);
return x_9;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = 0;
lean_inc(x_1);
x_14 = l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(x_1, x_13, x_10, x_4, x_5);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_3 = x_12;
x_5 = x_15;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = 0;
lean_inc(x_1);
x_14 = l_Lean_Elab_logAt___at_Lean_Elab_Term_tracingAtPos___spec__2(x_1, x_13, x_10, x_4, x_5);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_3 = x_12;
x_5 = x_15;
goto _start;
}
}
}
lean_object* l___private_Init_Lean_Util_Trace_4__checkTraceOption___at_Lean_Elab_Term_elabTerm___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_getOptions(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_List_isEmpty___rarg(x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = l___private_Init_Lean_Util_Trace_3__checkTraceOptionAux___main(x_6, x_1);
lean_dec(x_6);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
uint8_t x_10; lean_object* x_11; 
lean_dec(x_6);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = l_List_isEmpty___rarg(x_12);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l___private_Init_Lean_Util_Trace_3__checkTraceOptionAux___main(x_12, x_1);
lean_dec(x_12);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Elab_Term_elabTerm___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Lean_Elab_Term_addContext(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_6, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_7, 4);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_10);
x_19 = lean_array_push(x_17, x_18);
lean_ctor_set(x_8, 0, x_19);
x_20 = lean_box(0);
lean_ctor_set(x_5, 0, x_20);
return x_5;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_10);
x_24 = lean_array_push(x_22, x_23);
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_21);
lean_ctor_set(x_7, 4, x_25);
x_26 = lean_box(0);
lean_ctor_set(x_5, 0, x_26);
return x_5;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
x_29 = lean_ctor_get(x_7, 2);
x_30 = lean_ctor_get(x_7, 3);
x_31 = lean_ctor_get(x_7, 5);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_32 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_33 = lean_ctor_get(x_8, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_34 = x_8;
} else {
 lean_dec_ref(x_8);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_10);
x_36 = lean_array_push(x_33, x_35);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(0, 1, 1);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_32);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_28);
lean_ctor_set(x_38, 2, x_29);
lean_ctor_set(x_38, 3, x_30);
lean_ctor_set(x_38, 4, x_37);
lean_ctor_set(x_38, 5, x_31);
lean_ctor_set(x_6, 0, x_38);
x_39 = lean_box(0);
lean_ctor_set(x_5, 0, x_39);
return x_5;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_40 = lean_ctor_get(x_6, 1);
x_41 = lean_ctor_get(x_6, 2);
x_42 = lean_ctor_get(x_6, 3);
x_43 = lean_ctor_get(x_6, 4);
x_44 = lean_ctor_get(x_6, 5);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_6);
x_45 = lean_ctor_get(x_7, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_7, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_7, 5);
lean_inc(x_49);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 x_50 = x_7;
} else {
 lean_dec_ref(x_7);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_52 = lean_ctor_get(x_8, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_53 = x_8;
} else {
 lean_dec_ref(x_8);
 x_53 = lean_box(0);
}
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_10);
x_55 = lean_array_push(x_52, x_54);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 1, 1);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_51);
if (lean_is_scalar(x_50)) {
 x_57 = lean_alloc_ctor(0, 6, 0);
} else {
 x_57 = x_50;
}
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_46);
lean_ctor_set(x_57, 2, x_47);
lean_ctor_set(x_57, 3, x_48);
lean_ctor_set(x_57, 4, x_56);
lean_ctor_set(x_57, 5, x_49);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_40);
lean_ctor_set(x_58, 2, x_41);
lean_ctor_set(x_58, 3, x_42);
lean_ctor_set(x_58, 4, x_43);
lean_ctor_set(x_58, 5, x_44);
x_59 = lean_box(0);
lean_ctor_set(x_5, 1, x_58);
lean_ctor_set(x_5, 0, x_59);
return x_5;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_60 = lean_ctor_get(x_5, 0);
lean_inc(x_60);
lean_dec(x_5);
x_61 = lean_ctor_get(x_6, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_6, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_6, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_6, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_6, 5);
lean_inc(x_65);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 x_66 = x_6;
} else {
 lean_dec_ref(x_6);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get(x_7, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_7, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_7, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_7, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_7, 5);
lean_inc(x_71);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 x_72 = x_7;
} else {
 lean_dec_ref(x_7);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_74 = lean_ctor_get(x_8, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_75 = x_8;
} else {
 lean_dec_ref(x_8);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_60);
x_77 = lean_array_push(x_74, x_76);
if (lean_is_scalar(x_75)) {
 x_78 = lean_alloc_ctor(0, 1, 1);
} else {
 x_78 = x_75;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_73);
if (lean_is_scalar(x_72)) {
 x_79 = lean_alloc_ctor(0, 6, 0);
} else {
 x_79 = x_72;
}
lean_ctor_set(x_79, 0, x_67);
lean_ctor_set(x_79, 1, x_68);
lean_ctor_set(x_79, 2, x_69);
lean_ctor_set(x_79, 3, x_70);
lean_ctor_set(x_79, 4, x_78);
lean_ctor_set(x_79, 5, x_71);
if (lean_is_scalar(x_66)) {
 x_80 = lean_alloc_ctor(0, 6, 0);
} else {
 x_80 = x_66;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_61);
lean_ctor_set(x_80, 2, x_62);
lean_ctor_set(x_80, 3, x_63);
lean_ctor_set(x_80, 4, x_64);
lean_ctor_set(x_80, 5, x_65);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
lean_object* _init_l_Lean_Elab_Term_elabTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elaboration function for '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabTerm___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTerm___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabTerm___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTerm___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has not been implemented");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTerm___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabTerm___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTerm___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabTerm___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTerm___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__4;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_6, x_7);
lean_ctor_set(x_4, 5, x_8);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 3);
x_11 = lean_ctor_get(x_3, 8);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
lean_inc(x_10);
lean_ctor_set(x_3, 8, x_12);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_76 = l_Lean_Elab_Term_getTraceState___rarg(x_4);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get_uint8(x_77, sizeof(void*)*1);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_14 = x_79;
goto block_75;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
x_81 = l_Lean_Elab_Term_elabTerm___closed__7;
x_82 = l___private_Init_Lean_Util_Trace_4__checkTraceOption___at_Lean_Elab_Term_elabTerm___spec__10(x_81, x_3, x_80);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_14 = x_85;
goto block_75;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
lean_inc(x_1);
x_87 = l_Lean_Syntax_formatStx___main(x_1);
x_88 = l_Lean_Options_empty;
x_89 = l_Lean_Format_pretty(x_87, x_88);
x_90 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__4;
x_93 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Elab_Term_elabTerm___spec__11(x_92, x_91, x_3, x_86);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_14 = x_94;
goto block_75;
}
}
block_75:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = l_Lean_Elab_Term_termElabAttribute;
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_PersistentEnvExtension_getState___rarg(x_16, x_18);
lean_dec(x_18);
x_20 = l_Lean_SMap_find___at_Lean_Elab_Term_elabTerm___spec__2(x_19, x_13);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
lean_dec(x_2);
x_21 = l_Lean_Name_toString___closed__1;
x_22 = l_Lean_Name_toStringWithSep___main(x_21, x_13);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Elab_Term_elabTerm___closed__3;
x_26 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Elab_Term_elabTerm___closed__6;
x_28 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(x_1, x_28, x_3, x_14);
lean_dec(x_3);
lean_dec(x_1);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_69; 
lean_dec(x_13);
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = l_Lean_Syntax_getPos(x_1);
x_69 = l_Lean_Elab_Term_getTraceState___rarg(x_14);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_32 = x_10;
x_33 = x_70;
x_34 = x_71;
goto block_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_10);
x_72 = lean_ctor_get(x_31, 0);
lean_inc(x_72);
lean_dec(x_31);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
x_32 = x_72;
x_33 = x_73;
x_34 = x_74;
goto block_68;
}
block_68:
{
lean_object* x_35; lean_object* x_36; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = l_Lean_TraceState_Inhabited___closed__1;
x_49 = l_Lean_Elab_Term_setTraceState(x_48, x_3, x_34);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_51 = lean_apply_4(x_30, x_1, x_2, x_3, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Elab_Term_getTraceState___rarg(x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__9(x_32, x_57, x_58, x_3, x_56);
lean_dec(x_57);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Elab_Term_setTraceState(x_33, x_3, x_60);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set(x_61, 0, x_52);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_52);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_51, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_51, 1);
lean_inc(x_67);
lean_dec(x_51);
x_35 = x_66;
x_36 = x_67;
goto block_47;
}
block_47:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = l_Lean_Elab_Term_getTraceState___rarg(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__8(x_32, x_40, x_41, x_3, x_39);
lean_dec(x_40);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Elab_Term_setTraceState(x_33, x_3, x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_Elab_Term_exceptionToSorry(x_1, x_35, x_2, x_3, x_45);
lean_dec(x_1);
return x_46;
}
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_10);
lean_dec(x_2);
x_95 = l_Lean_Elab_Term_withNode___rarg___closed__3;
x_96 = l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(x_1, x_95, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_97 = lean_ctor_get(x_3, 0);
x_98 = lean_ctor_get(x_3, 1);
x_99 = lean_ctor_get(x_3, 2);
x_100 = lean_ctor_get(x_3, 3);
x_101 = lean_ctor_get(x_3, 4);
x_102 = lean_ctor_get(x_3, 5);
x_103 = lean_ctor_get(x_3, 6);
x_104 = lean_ctor_get(x_3, 7);
x_105 = lean_ctor_get(x_3, 8);
x_106 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_3);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_6);
lean_ctor_set(x_107, 1, x_105);
lean_inc(x_100);
x_108 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_108, 0, x_97);
lean_ctor_set(x_108, 1, x_98);
lean_ctor_set(x_108, 2, x_99);
lean_ctor_set(x_108, 3, x_100);
lean_ctor_set(x_108, 4, x_101);
lean_ctor_set(x_108, 5, x_102);
lean_ctor_set(x_108, 6, x_103);
lean_ctor_set(x_108, 7, x_104);
lean_ctor_set(x_108, 8, x_107);
lean_ctor_set_uint8(x_108, sizeof(void*)*9, x_106);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_109; lean_object* x_110; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_109 = lean_ctor_get(x_1, 0);
lean_inc(x_109);
x_171 = l_Lean_Elab_Term_getTraceState___rarg(x_4);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get_uint8(x_172, sizeof(void*)*1);
lean_dec(x_172);
if (x_173 == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_110 = x_174;
goto block_170;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_175 = lean_ctor_get(x_171, 1);
lean_inc(x_175);
lean_dec(x_171);
x_176 = l_Lean_Elab_Term_elabTerm___closed__7;
x_177 = l___private_Init_Lean_Util_Trace_4__checkTraceOption___at_Lean_Elab_Term_elabTerm___spec__10(x_176, x_108, x_175);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_unbox(x_178);
lean_dec(x_178);
if (x_179 == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_dec(x_177);
x_110 = x_180;
goto block_170;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
lean_dec(x_177);
lean_inc(x_1);
x_182 = l_Lean_Syntax_formatStx___main(x_1);
x_183 = l_Lean_Options_empty;
x_184 = l_Lean_Format_pretty(x_182, x_183);
x_185 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_185);
x_187 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__4;
x_188 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Elab_Term_elabTerm___spec__11(x_187, x_186, x_108, x_181);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_110 = x_189;
goto block_170;
}
}
block_170:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = l_Lean_Elab_Term_termElabAttribute;
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec(x_113);
x_115 = l_Lean_PersistentEnvExtension_getState___rarg(x_112, x_114);
lean_dec(x_114);
x_116 = l_Lean_SMap_find___at_Lean_Elab_Term_elabTerm___spec__2(x_115, x_109);
lean_dec(x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_100);
lean_dec(x_2);
x_117 = l_Lean_Name_toString___closed__1;
x_118 = l_Lean_Name_toStringWithSep___main(x_117, x_109);
x_119 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = l_Lean_Elab_Term_elabTerm___closed__3;
x_122 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = l_Lean_Elab_Term_elabTerm___closed__6;
x_124 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(x_1, x_124, x_108, x_110);
lean_dec(x_108);
lean_dec(x_1);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_164; 
lean_dec(x_109);
x_126 = lean_ctor_get(x_116, 0);
lean_inc(x_126);
lean_dec(x_116);
x_127 = l_Lean_Syntax_getPos(x_1);
x_164 = l_Lean_Elab_Term_getTraceState___rarg(x_110);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_128 = x_100;
x_129 = x_165;
x_130 = x_166;
goto block_163;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_100);
x_167 = lean_ctor_get(x_127, 0);
lean_inc(x_167);
lean_dec(x_127);
x_168 = lean_ctor_get(x_164, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
lean_dec(x_164);
x_128 = x_167;
x_129 = x_168;
x_130 = x_169;
goto block_163;
}
block_163:
{
lean_object* x_131; lean_object* x_132; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = l_Lean_TraceState_Inhabited___closed__1;
x_145 = l_Lean_Elab_Term_setTraceState(x_144, x_108, x_130);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
lean_inc(x_108);
lean_inc(x_2);
lean_inc(x_1);
x_147 = lean_apply_4(x_126, x_1, x_2, x_108, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_2);
lean_dec(x_1);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lean_Elab_Term_getTraceState___rarg(x_149);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_unsigned_to_nat(0u);
x_155 = l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__9(x_128, x_153, x_154, x_108, x_152);
lean_dec(x_153);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = l_Lean_Elab_Term_setTraceState(x_129, x_108, x_156);
lean_dec(x_108);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_148);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_147, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_147, 1);
lean_inc(x_162);
lean_dec(x_147);
x_131 = x_161;
x_132 = x_162;
goto block_143;
}
block_143:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_133 = l_Lean_Elab_Term_getTraceState___rarg(x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_unsigned_to_nat(0u);
x_138 = l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__8(x_128, x_136, x_137, x_108, x_135);
lean_dec(x_136);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = l_Lean_Elab_Term_setTraceState(x_129, x_108, x_139);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = l_Lean_Elab_Term_exceptionToSorry(x_1, x_131, x_2, x_108, x_141);
lean_dec(x_1);
return x_142;
}
}
}
}
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_100);
lean_dec(x_2);
x_190 = l_Lean_Elab_Term_withNode___rarg___closed__3;
x_191 = l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(x_1, x_190, x_108, x_4);
lean_dec(x_108);
lean_dec(x_1);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_192 = lean_ctor_get(x_4, 0);
x_193 = lean_ctor_get(x_4, 1);
x_194 = lean_ctor_get(x_4, 2);
x_195 = lean_ctor_get(x_4, 3);
x_196 = lean_ctor_get(x_4, 4);
x_197 = lean_ctor_get(x_4, 5);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_4);
x_198 = lean_unsigned_to_nat(1u);
x_199 = lean_nat_add(x_197, x_198);
x_200 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_200, 0, x_192);
lean_ctor_set(x_200, 1, x_193);
lean_ctor_set(x_200, 2, x_194);
lean_ctor_set(x_200, 3, x_195);
lean_ctor_set(x_200, 4, x_196);
lean_ctor_set(x_200, 5, x_199);
x_201 = lean_ctor_get(x_3, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_3, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_3, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_3, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_3, 4);
lean_inc(x_205);
x_206 = lean_ctor_get(x_3, 5);
lean_inc(x_206);
x_207 = lean_ctor_get(x_3, 6);
lean_inc(x_207);
x_208 = lean_ctor_get(x_3, 7);
lean_inc(x_208);
x_209 = lean_ctor_get(x_3, 8);
lean_inc(x_209);
x_210 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 x_211 = x_3;
} else {
 lean_dec_ref(x_3);
 x_211 = lean_box(0);
}
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_197);
lean_ctor_set(x_212, 1, x_209);
lean_inc(x_204);
if (lean_is_scalar(x_211)) {
 x_213 = lean_alloc_ctor(0, 9, 1);
} else {
 x_213 = x_211;
}
lean_ctor_set(x_213, 0, x_201);
lean_ctor_set(x_213, 1, x_202);
lean_ctor_set(x_213, 2, x_203);
lean_ctor_set(x_213, 3, x_204);
lean_ctor_set(x_213, 4, x_205);
lean_ctor_set(x_213, 5, x_206);
lean_ctor_set(x_213, 6, x_207);
lean_ctor_set(x_213, 7, x_208);
lean_ctor_set(x_213, 8, x_212);
lean_ctor_set_uint8(x_213, sizeof(void*)*9, x_210);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_214; lean_object* x_215; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_214 = lean_ctor_get(x_1, 0);
lean_inc(x_214);
x_276 = l_Lean_Elab_Term_getTraceState___rarg(x_200);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get_uint8(x_277, sizeof(void*)*1);
lean_dec(x_277);
if (x_278 == 0)
{
lean_object* x_279; 
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_279);
lean_dec(x_276);
x_215 = x_279;
goto block_275;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_280 = lean_ctor_get(x_276, 1);
lean_inc(x_280);
lean_dec(x_276);
x_281 = l_Lean_Elab_Term_elabTerm___closed__7;
x_282 = l___private_Init_Lean_Util_Trace_4__checkTraceOption___at_Lean_Elab_Term_elabTerm___spec__10(x_281, x_213, x_280);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_unbox(x_283);
lean_dec(x_283);
if (x_284 == 0)
{
lean_object* x_285; 
x_285 = lean_ctor_get(x_282, 1);
lean_inc(x_285);
lean_dec(x_282);
x_215 = x_285;
goto block_275;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_286 = lean_ctor_get(x_282, 1);
lean_inc(x_286);
lean_dec(x_282);
lean_inc(x_1);
x_287 = l_Lean_Syntax_formatStx___main(x_1);
x_288 = l_Lean_Options_empty;
x_289 = l_Lean_Format_pretty(x_287, x_288);
x_290 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_290, 0, x_289);
x_291 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_291, 0, x_290);
x_292 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__4;
x_293 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Elab_Term_elabTerm___spec__11(x_292, x_291, x_213, x_286);
x_294 = lean_ctor_get(x_293, 1);
lean_inc(x_294);
lean_dec(x_293);
x_215 = x_294;
goto block_275;
}
}
block_275:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_216 = l_Lean_Elab_Term_termElabAttribute;
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_215, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec(x_218);
x_220 = l_Lean_PersistentEnvExtension_getState___rarg(x_217, x_219);
lean_dec(x_219);
x_221 = l_Lean_SMap_find___at_Lean_Elab_Term_elabTerm___spec__2(x_220, x_214);
lean_dec(x_220);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_204);
lean_dec(x_2);
x_222 = l_Lean_Name_toString___closed__1;
x_223 = l_Lean_Name_toStringWithSep___main(x_222, x_214);
x_224 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_224, 0, x_223);
x_225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_225, 0, x_224);
x_226 = l_Lean_Elab_Term_elabTerm___closed__3;
x_227 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_225);
x_228 = l_Lean_Elab_Term_elabTerm___closed__6;
x_229 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(x_1, x_229, x_213, x_215);
lean_dec(x_213);
lean_dec(x_1);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_269; 
lean_dec(x_214);
x_231 = lean_ctor_get(x_221, 0);
lean_inc(x_231);
lean_dec(x_221);
x_232 = l_Lean_Syntax_getPos(x_1);
x_269 = l_Lean_Elab_Term_getTraceState___rarg(x_215);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_233 = x_204;
x_234 = x_270;
x_235 = x_271;
goto block_268;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_204);
x_272 = lean_ctor_get(x_232, 0);
lean_inc(x_272);
lean_dec(x_232);
x_273 = lean_ctor_get(x_269, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_269, 1);
lean_inc(x_274);
lean_dec(x_269);
x_233 = x_272;
x_234 = x_273;
x_235 = x_274;
goto block_268;
}
block_268:
{
lean_object* x_236; lean_object* x_237; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = l_Lean_TraceState_Inhabited___closed__1;
x_250 = l_Lean_Elab_Term_setTraceState(x_249, x_213, x_235);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
lean_dec(x_250);
lean_inc(x_213);
lean_inc(x_2);
lean_inc(x_1);
x_252 = lean_apply_4(x_231, x_1, x_2, x_213, x_251);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_2);
lean_dec(x_1);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = l_Lean_Elab_Term_getTraceState___rarg(x_254);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_unsigned_to_nat(0u);
x_260 = l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__9(x_233, x_258, x_259, x_213, x_257);
lean_dec(x_258);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
lean_dec(x_260);
x_262 = l_Lean_Elab_Term_setTraceState(x_234, x_213, x_261);
lean_dec(x_213);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_264 = x_262;
} else {
 lean_dec_ref(x_262);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_253);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_252, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_252, 1);
lean_inc(x_267);
lean_dec(x_252);
x_236 = x_266;
x_237 = x_267;
goto block_248;
}
block_248:
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_238 = l_Lean_Elab_Term_getTraceState___rarg(x_237);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_ctor_get(x_239, 0);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_unsigned_to_nat(0u);
x_243 = l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__8(x_233, x_241, x_242, x_213, x_240);
lean_dec(x_241);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_245 = l_Lean_Elab_Term_setTraceState(x_234, x_213, x_244);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
lean_dec(x_245);
x_247 = l_Lean_Elab_Term_exceptionToSorry(x_1, x_236, x_2, x_213, x_246);
lean_dec(x_1);
return x_247;
}
}
}
}
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_204);
lean_dec(x_2);
x_295 = l_Lean_Elab_Term_withNode___rarg___closed__3;
x_296 = l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(x_1, x_295, x_213, x_200);
lean_dec(x_213);
lean_dec(x_1);
return x_296;
}
}
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTerm___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Term_elabTerm___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTerm___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Term_elabTerm___spec__4(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_find___at_Lean_Elab_Term_elabTerm___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find___at_Lean_Elab_Term_elabTerm___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_Term_elabTerm___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Elab_Term_elabTerm___spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at_Lean_Elab_Term_elabTerm___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at_Lean_Elab_Term_elabTerm___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find___at_Lean_Elab_Term_elabTerm___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find___at_Lean_Elab_Term_elabTerm___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Term_elabTerm___spec__9(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Util_Trace_4__checkTraceOption___at_Lean_Elab_Term_elabTerm___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Util_Trace_4__checkTraceOption___at_Lean_Elab_Term_elabTerm___spec__10(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Elab_Term_elabTerm___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Elab_Term_elabTerm___spec__11(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_ensureType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toStr___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_ensureType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_ensureType___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ensureType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Elab_Term_inferType(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
x_8 = l_Lean_Elab_Term_whnf(x_1, x_6, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Expr_isSort(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_free_object(x_8);
lean_inc(x_3);
x_13 = l_Lean_Elab_Term_mkFreshLevelMVar(x_1, x_3, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_mkSort(x_14);
lean_inc(x_3);
x_17 = l_Lean_Elab_Term_isDefEq(x_1, x_10, x_16, x_3, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_Elab_Term_ensureType___closed__2;
x_22 = l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(x_1, x_21, x_3, x_20);
lean_dec(x_3);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_17, 0);
lean_dec(x_24);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_10);
lean_dec(x_3);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = l_Lean_Expr_isSort(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc(x_3);
x_34 = l_Lean_Elab_Term_mkFreshLevelMVar(x_1, x_3, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_mkSort(x_35);
lean_inc(x_3);
x_38 = l_Lean_Elab_Term_isDefEq(x_1, x_31, x_37, x_3, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Elab_Term_ensureType___closed__2;
x_43 = l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(x_1, x_42, x_3, x_41);
lean_dec(x_3);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_45 = x_38;
} else {
 lean_dec_ref(x_38);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_ctor_get(x_38, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_49 = x_38;
} else {
 lean_dec_ref(x_38);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; 
lean_dec(x_31);
lean_dec(x_3);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_32);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_8);
if (x_52 == 0)
{
return x_8;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_8, 0);
x_54 = lean_ctor_get(x_8, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_8);
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
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_5);
if (x_56 == 0)
{
return x_5;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_5, 0);
x_58 = lean_ctor_get(x_5, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_5);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
lean_object* l_Lean_Elab_Term_ensureType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_ensureType(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Term_mkFreshLevelMVar(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_mkSort(x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_Elab_Term_elabTerm(x_1, x_8, x_2, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Term_ensureType(x_1, x_10, x_2, x_11);
lean_dec(x_1);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Term_elabProp___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_getAppArgs___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabProp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabProp___rarg), 1, 0);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabProp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_elabProp(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabProp");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabProp___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_prop___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabSort___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_getAppArgs___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabSort(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSort___rarg), 1, 0);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabSort___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_elabSort(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabSort");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSort___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSort(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_sort___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_elabTypeStx___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelOne;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabTypeStx___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_elabTypeStx___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabTypeStx(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTypeStx___rarg), 1, 0);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabTypeStx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_elabTypeStx(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabTypeStx");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTypeStx___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_type___elambda__1___rarg___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabHole(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 0;
x_6 = lean_box(0);
x_7 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabHole___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabHole(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabHole");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabHole___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabHole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_a");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 4);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_ctor_set(x_1, 4, x_5);
x_6 = l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg___closed__2;
x_7 = l_Lean_Name_appendIndexAfter(x_6, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_1, 4);
x_14 = lean_ctor_get(x_1, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_13, x_15);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_12);
lean_ctor_set(x_17, 4, x_16);
lean_ctor_set(x_17, 5, x_14);
x_18 = l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg___closed__2;
x_19 = l_Lean_Name_appendIndexAfter(x_18, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_inst");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_ctor_set(x_1, 3, x_5);
x_6 = l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg___closed__2;
x_7 = l_Lean_Name_appendIndexAfter(x_6, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_1, 4);
x_14 = lean_ctor_get(x_1, 5);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_12, x_15);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_11);
lean_ctor_set(x_17, 3, x_16);
lean_ctor_set(x_17, 4, x_13);
lean_ctor_set(x_17, 5, x_14);
x_18 = l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg___closed__2;
x_19 = l_Lean_Name_appendIndexAfter(x_18, x_12);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkHole___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Name_appendIndexAfter___closed__1;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkHole___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__1;
x_2 = l_Lean_Elab_Term_mkHole___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_mkHole___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1;
x_2 = l_Lean_Elab_Term_mkHole___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_mkHole() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_mkHole___closed__3;
return x_1;
}
}
lean_object* l___private_Init_Lean_Elab_Term_6__expandBinderType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Syntax_getNumArgs(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_mkHole;
return x_7;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_6__expandBinderType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Term_6__expandBinderType(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_7__expandBinderIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Syntax_getKind(x_1);
x_5 = l_Lean_Parser_Term_hole___elambda__1___rarg___closed__1;
x_6 = lean_name_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg(x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_mkIdentFrom(x_1, x_10);
lean_dec(x_1);
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
x_14 = l_Lean_mkIdentFrom(x_1, x_12);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_7__expandBinderIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_7__expandBinderIdent(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Term_8__expandOptIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Syntax_getNumArgs(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Syntax_getArg(x_1, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg(x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_mkIdentFrom(x_1, x_11);
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
x_15 = l_Lean_mkIdentFrom(x_1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_8__expandOptIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_8__expandOptIdent(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 2;
x_6 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_withNode___spec__2(x_2, x_5, x_1, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = x_3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_array_fget(x_3, x_2);
x_12 = lean_box(0);
lean_inc(x_11);
x_13 = x_12;
x_14 = lean_array_fset(x_3, x_2, x_13);
lean_inc(x_11);
x_15 = l___private_Init_Lean_Elab_Term_7__expandBinderIdent(x_11, x_4, x_5);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = x_19;
x_23 = lean_array_fset(x_14, x_2, x_22);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_23;
x_5 = x_17;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = x_3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_array_fget(x_3, x_2);
x_12 = lean_box(0);
lean_inc(x_11);
x_13 = x_12;
x_14 = lean_array_fset(x_3, x_2, x_13);
lean_inc(x_11);
x_15 = l___private_Init_Lean_Elab_Term_7__expandBinderIdent(x_11, x_4, x_5);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 0;
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = x_19;
x_23 = lean_array_fset(x_14, x_2, x_22);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_23;
x_5 = x_17;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_7 = l_Array_empty___closed__1;
x_8 = x_2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = lean_array_fget(x_2, x_1);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = x_11;
x_13 = lean_array_fset(x_2, x_1, x_12);
lean_inc(x_10);
x_14 = l___private_Init_Lean_Elab_Term_7__expandBinderIdent(x_10, x_3, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Term_mkHole;
x_18 = 0;
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_1, x_20);
x_22 = x_19;
x_23 = lean_array_fset(x_13, x_1, x_22);
lean_dec(x_1);
x_1 = x_21;
x_2 = x_23;
x_4 = x_16;
goto _start;
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_9__matchBinder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("term elaborator failed, unexpected binder syntax");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_9__matchBinder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_9__matchBinder___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_9__matchBinder___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_9__matchBinder___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_9__matchBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Parser_Term_simpleBinder___elambda__1___closed__2;
x_7 = lean_name_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_9 = lean_name_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
x_11 = lean_name_eq(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Parser_Term_instBinder___elambda__1___rarg___closed__2;
x_13 = lean_name_eq(x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l___private_Init_Lean_Elab_Term_9__matchBinder___closed__3;
x_15 = l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__1(x_1, x_14, x_2, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = l_Lean_stxInh;
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_array_get(x_16, x_5, x_17);
x_19 = l___private_Init_Lean_Elab_Term_8__expandOptIdent(x_18, x_2, x_3);
lean_dec(x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_unsigned_to_nat(2u);
x_23 = lean_array_get(x_16, x_5, x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
x_26 = l_Lean_mkOptionalNode___closed__1;
x_27 = lean_array_push(x_26, x_25);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_array_get(x_16, x_5, x_30);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_32);
x_34 = l_Lean_mkOptionalNode___closed__1;
x_35 = lean_array_push(x_34, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = l_Lean_stxInh;
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_array_get(x_37, x_5, x_38);
x_40 = l_Lean_Syntax_getArgs(x_39);
lean_dec(x_39);
x_41 = lean_unsigned_to_nat(2u);
x_42 = lean_array_get(x_37, x_5, x_41);
x_43 = l___private_Init_Lean_Elab_Term_6__expandBinderType(x_42);
lean_dec(x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__2(x_43, x_44, x_40, x_2, x_3);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = l_Lean_stxInh;
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_array_get(x_46, x_5, x_47);
x_49 = l_Lean_Syntax_getArgs(x_48);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(2u);
x_51 = lean_array_get(x_46, x_5, x_50);
x_52 = l___private_Init_Lean_Elab_Term_6__expandBinderType(x_51);
lean_dec(x_51);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__3(x_52, x_53, x_49, x_2, x_3);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = l_Lean_stxInh;
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_array_get(x_55, x_5, x_56);
x_58 = l_Lean_Syntax_getArgs(x_57);
lean_dec(x_57);
x_59 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__4(x_56, x_58, x_2, x_3);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Elab_Term_withNode___rarg___closed__3;
x_61 = l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__1(x_1, x_60, x_2, x_3);
return x_61;
}
}
}
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_9__matchBinder___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_Term_9__matchBinder___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_9__matchBinder(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_withLCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set(x_7, 1, x_1);
x_11 = lean_apply_2(x_3, x_4, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_2);
lean_ctor_set(x_4, 0, x_13);
x_14 = lean_apply_2(x_3, x_4, x_5);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_ctor_get(x_4, 3);
x_19 = lean_ctor_get(x_4, 4);
x_20 = lean_ctor_get(x_4, 5);
x_21 = lean_ctor_get(x_4, 6);
x_22 = lean_ctor_get(x_4, 7);
x_23 = lean_ctor_get(x_4, 8);
x_24 = lean_ctor_get_uint8(x_4, sizeof(void*)*9);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_26 = x_15;
} else {
 lean_dec_ref(x_15);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 3, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_1);
lean_ctor_set(x_27, 2, x_2);
x_28 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_16);
lean_ctor_set(x_28, 2, x_17);
lean_ctor_set(x_28, 3, x_18);
lean_ctor_set(x_28, 4, x_19);
lean_ctor_set(x_28, 5, x_20);
lean_ctor_set(x_28, 6, x_21);
lean_ctor_set(x_28, 7, x_22);
lean_ctor_set(x_28, 8, x_23);
lean_ctor_set_uint8(x_28, sizeof(void*)*9, x_24);
x_29 = lean_apply_2(x_3, x_28, x_5);
return x_29;
}
}
}
lean_object* l_Lean_Elab_Term_withLCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withLCtx___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_dec(x_5);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 2);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 2);
lean_dec(x_9);
x_10 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_3, 2, x_10);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_2, 2, x_16);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_1);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 3);
x_22 = lean_ctor_get(x_2, 4);
x_23 = lean_ctor_get(x_2, 5);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_2);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_26 = x_3;
} else {
 lean_dec_ref(x_3);
 x_26 = lean_box(0);
}
x_27 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 3, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_20);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_21);
lean_ctor_set(x_29, 4, x_22);
lean_ctor_set(x_29, 5, x_23);
lean_ctor_set(x_1, 0, x_29);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_1);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_32 = lean_ctor_get(x_1, 1);
x_33 = lean_ctor_get(x_1, 2);
x_34 = lean_ctor_get(x_1, 3);
x_35 = lean_ctor_get(x_1, 4);
x_36 = lean_ctor_get(x_1, 5);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 5);
lean_inc(x_41);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_42 = x_2;
} else {
 lean_dec_ref(x_2);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_45 = x_3;
} else {
 lean_dec_ref(x_3);
 x_45 = lean_box(0);
}
x_46 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 3, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_46);
if (lean_is_scalar(x_42)) {
 x_48 = lean_alloc_ctor(0, 6, 0);
} else {
 x_48 = x_42;
}
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set(x_48, 1, x_38);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_39);
lean_ctor_set(x_48, 4, x_40);
lean_ctor_set(x_48, 5, x_41);
x_49 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_32);
lean_ctor_set(x_49, 2, x_33);
lean_ctor_set(x_49, 3, x_34);
lean_ctor_set(x_49, 4, x_35);
lean_ctor_set(x_49, 5, x_36);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_resetSynthInstanceCache___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_resetSynthInstanceCache(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_1, x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_9, 1);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_11, 2);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_12, 2);
lean_dec(x_20);
lean_ctor_set(x_12, 2, x_6);
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_6);
lean_ctor_set(x_11, 2, x_23);
return x_9;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get(x_11, 4);
x_28 = lean_ctor_get(x_11, 5);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_29 = lean_ctor_get(x_12, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_31 = x_12;
} else {
 lean_dec_ref(x_12);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 3, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_6);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_24);
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_26);
lean_ctor_set(x_33, 4, x_27);
lean_ctor_set(x_33, 5, x_28);
lean_ctor_set(x_10, 0, x_33);
return x_9;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_34 = lean_ctor_get(x_10, 1);
x_35 = lean_ctor_get(x_10, 2);
x_36 = lean_ctor_get(x_10, 3);
x_37 = lean_ctor_get(x_10, 4);
x_38 = lean_ctor_get(x_10, 5);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_10);
x_39 = lean_ctor_get(x_11, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_11, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_11, 4);
lean_inc(x_42);
x_43 = lean_ctor_get(x_11, 5);
lean_inc(x_43);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_44 = x_11;
} else {
 lean_dec_ref(x_11);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_12, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_47 = x_12;
} else {
 lean_dec_ref(x_12);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 3, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_6);
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(0, 6, 0);
} else {
 x_49 = x_44;
}
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_40);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_41);
lean_ctor_set(x_49, 4, x_42);
lean_ctor_set(x_49, 5, x_43);
x_50 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_34);
lean_ctor_set(x_50, 2, x_35);
lean_ctor_set(x_50, 3, x_36);
lean_ctor_set(x_50, 4, x_37);
lean_ctor_set(x_50, 5, x_38);
lean_ctor_set(x_9, 1, x_50);
return x_9;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_51 = lean_ctor_get(x_9, 0);
lean_inc(x_51);
lean_dec(x_9);
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_10, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_10, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_10, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_10, 5);
lean_inc(x_56);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 lean_ctor_release(x_10, 5);
 x_57 = x_10;
} else {
 lean_dec_ref(x_10);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_11, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_11, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_11, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_11, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_11, 5);
lean_inc(x_62);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 lean_ctor_release(x_11, 5);
 x_63 = x_11;
} else {
 lean_dec_ref(x_11);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_12, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_12, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 x_66 = x_12;
} else {
 lean_dec_ref(x_12);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 3, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_67, 2, x_6);
if (lean_is_scalar(x_63)) {
 x_68 = lean_alloc_ctor(0, 6, 0);
} else {
 x_68 = x_63;
}
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_59);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_68, 3, x_60);
lean_ctor_set(x_68, 4, x_61);
lean_ctor_set(x_68, 5, x_62);
if (lean_is_scalar(x_57)) {
 x_69 = lean_alloc_ctor(0, 6, 0);
} else {
 x_69 = x_57;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_52);
lean_ctor_set(x_69, 2, x_53);
lean_ctor_set(x_69, 3, x_54);
lean_ctor_set(x_69, 4, x_55);
lean_ctor_set(x_69, 5, x_56);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_51);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_9, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 2);
lean_inc(x_73);
x_74 = !lean_is_exclusive(x_9);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_9, 1);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_71);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_71, 0);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_72);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_72, 2);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_73);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_73, 2);
lean_dec(x_81);
lean_ctor_set(x_73, 2, x_6);
return x_9;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_73, 0);
x_83 = lean_ctor_get(x_73, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_73);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_6);
lean_ctor_set(x_72, 2, x_84);
return x_9;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_85 = lean_ctor_get(x_72, 0);
x_86 = lean_ctor_get(x_72, 1);
x_87 = lean_ctor_get(x_72, 3);
x_88 = lean_ctor_get(x_72, 4);
x_89 = lean_ctor_get(x_72, 5);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_72);
x_90 = lean_ctor_get(x_73, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_73, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_92 = x_73;
} else {
 lean_dec_ref(x_73);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 3, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_6);
x_94 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_94, 0, x_85);
lean_ctor_set(x_94, 1, x_86);
lean_ctor_set(x_94, 2, x_93);
lean_ctor_set(x_94, 3, x_87);
lean_ctor_set(x_94, 4, x_88);
lean_ctor_set(x_94, 5, x_89);
lean_ctor_set(x_71, 0, x_94);
return x_9;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_95 = lean_ctor_get(x_71, 1);
x_96 = lean_ctor_get(x_71, 2);
x_97 = lean_ctor_get(x_71, 3);
x_98 = lean_ctor_get(x_71, 4);
x_99 = lean_ctor_get(x_71, 5);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_71);
x_100 = lean_ctor_get(x_72, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_72, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_72, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_72, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_72, 5);
lean_inc(x_104);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 lean_ctor_release(x_72, 5);
 x_105 = x_72;
} else {
 lean_dec_ref(x_72);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_73, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_73, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_108 = x_73;
} else {
 lean_dec_ref(x_73);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 3, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set(x_109, 2, x_6);
if (lean_is_scalar(x_105)) {
 x_110 = lean_alloc_ctor(0, 6, 0);
} else {
 x_110 = x_105;
}
lean_ctor_set(x_110, 0, x_100);
lean_ctor_set(x_110, 1, x_101);
lean_ctor_set(x_110, 2, x_109);
lean_ctor_set(x_110, 3, x_102);
lean_ctor_set(x_110, 4, x_103);
lean_ctor_set(x_110, 5, x_104);
x_111 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_95);
lean_ctor_set(x_111, 2, x_96);
lean_ctor_set(x_111, 3, x_97);
lean_ctor_set(x_111, 4, x_98);
lean_ctor_set(x_111, 5, x_99);
lean_ctor_set(x_9, 1, x_111);
return x_9;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_112 = lean_ctor_get(x_9, 0);
lean_inc(x_112);
lean_dec(x_9);
x_113 = lean_ctor_get(x_71, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_71, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_71, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_71, 4);
lean_inc(x_116);
x_117 = lean_ctor_get(x_71, 5);
lean_inc(x_117);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 lean_ctor_release(x_71, 5);
 x_118 = x_71;
} else {
 lean_dec_ref(x_71);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_72, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_72, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_72, 3);
lean_inc(x_121);
x_122 = lean_ctor_get(x_72, 4);
lean_inc(x_122);
x_123 = lean_ctor_get(x_72, 5);
lean_inc(x_123);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 lean_ctor_release(x_72, 5);
 x_124 = x_72;
} else {
 lean_dec_ref(x_72);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_73, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_73, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_127 = x_73;
} else {
 lean_dec_ref(x_73);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 3, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
lean_ctor_set(x_128, 2, x_6);
if (lean_is_scalar(x_124)) {
 x_129 = lean_alloc_ctor(0, 6, 0);
} else {
 x_129 = x_124;
}
lean_ctor_set(x_129, 0, x_119);
lean_ctor_set(x_129, 1, x_120);
lean_ctor_set(x_129, 2, x_128);
lean_ctor_set(x_129, 3, x_121);
lean_ctor_set(x_129, 4, x_122);
lean_ctor_set(x_129, 5, x_123);
if (lean_is_scalar(x_118)) {
 x_130 = lean_alloc_ctor(0, 6, 0);
} else {
 x_130 = x_118;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_113);
lean_ctor_set(x_130, 2, x_114);
lean_ctor_set(x_130, 3, x_115);
lean_ctor_set(x_130, 4, x_116);
lean_ctor_set(x_130, 5, x_117);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_112);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_resettingSynthInstanceCache___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
lean_object* x_5; 
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_4);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_2, x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_11, 1);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_13, 2);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_14, 2);
lean_dec(x_22);
lean_ctor_set(x_14, 2, x_8);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_8);
lean_ctor_set(x_13, 2, x_25);
return x_11;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
x_28 = lean_ctor_get(x_13, 3);
x_29 = lean_ctor_get(x_13, 4);
x_30 = lean_ctor_get(x_13, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_33 = x_14;
} else {
 lean_dec_ref(x_14);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 3, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_8);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_27);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_28);
lean_ctor_set(x_35, 4, x_29);
lean_ctor_set(x_35, 5, x_30);
lean_ctor_set(x_12, 0, x_35);
return x_11;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_36 = lean_ctor_get(x_12, 1);
x_37 = lean_ctor_get(x_12, 2);
x_38 = lean_ctor_get(x_12, 3);
x_39 = lean_ctor_get(x_12, 4);
x_40 = lean_ctor_get(x_12, 5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_12);
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_13, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_13, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_13, 5);
lean_inc(x_45);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 x_46 = x_13;
} else {
 lean_dec_ref(x_13);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_14, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_14, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_49 = x_14;
} else {
 lean_dec_ref(x_14);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 3, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_50, 2, x_8);
if (lean_is_scalar(x_46)) {
 x_51 = lean_alloc_ctor(0, 6, 0);
} else {
 x_51 = x_46;
}
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_42);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_51, 3, x_43);
lean_ctor_set(x_51, 4, x_44);
lean_ctor_set(x_51, 5, x_45);
x_52 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_36);
lean_ctor_set(x_52, 2, x_37);
lean_ctor_set(x_52, 3, x_38);
lean_ctor_set(x_52, 4, x_39);
lean_ctor_set(x_52, 5, x_40);
lean_ctor_set(x_11, 1, x_52);
return x_11;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_53 = lean_ctor_get(x_11, 0);
lean_inc(x_53);
lean_dec(x_11);
x_54 = lean_ctor_get(x_12, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_12, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_12, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_12, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_12, 5);
lean_inc(x_58);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 lean_ctor_release(x_12, 5);
 x_59 = x_12;
} else {
 lean_dec_ref(x_12);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_13, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_13, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_13, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_13, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_13, 5);
lean_inc(x_64);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 x_65 = x_13;
} else {
 lean_dec_ref(x_13);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_14, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_14, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_68 = x_14;
} else {
 lean_dec_ref(x_14);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 3, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_8);
if (lean_is_scalar(x_65)) {
 x_70 = lean_alloc_ctor(0, 6, 0);
} else {
 x_70 = x_65;
}
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_61);
lean_ctor_set(x_70, 2, x_69);
lean_ctor_set(x_70, 3, x_62);
lean_ctor_set(x_70, 4, x_63);
lean_ctor_set(x_70, 5, x_64);
if (lean_is_scalar(x_59)) {
 x_71 = lean_alloc_ctor(0, 6, 0);
} else {
 x_71 = x_59;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_54);
lean_ctor_set(x_71, 2, x_55);
lean_ctor_set(x_71, 3, x_56);
lean_ctor_set(x_71, 4, x_57);
lean_ctor_set(x_71, 5, x_58);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_53);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_11, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_74, 2);
lean_inc(x_75);
x_76 = !lean_is_exclusive(x_11);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_11, 1);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_73);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_73, 0);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_74);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_74, 2);
lean_dec(x_81);
x_82 = !lean_is_exclusive(x_75);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_75, 2);
lean_dec(x_83);
lean_ctor_set(x_75, 2, x_8);
return x_11;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_75, 0);
x_85 = lean_ctor_get(x_75, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_75);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_8);
lean_ctor_set(x_74, 2, x_86);
return x_11;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_74, 0);
x_88 = lean_ctor_get(x_74, 1);
x_89 = lean_ctor_get(x_74, 3);
x_90 = lean_ctor_get(x_74, 4);
x_91 = lean_ctor_get(x_74, 5);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_74);
x_92 = lean_ctor_get(x_75, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_75, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_94 = x_75;
} else {
 lean_dec_ref(x_75);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 3, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_8);
x_96 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_96, 0, x_87);
lean_ctor_set(x_96, 1, x_88);
lean_ctor_set(x_96, 2, x_95);
lean_ctor_set(x_96, 3, x_89);
lean_ctor_set(x_96, 4, x_90);
lean_ctor_set(x_96, 5, x_91);
lean_ctor_set(x_73, 0, x_96);
return x_11;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_97 = lean_ctor_get(x_73, 1);
x_98 = lean_ctor_get(x_73, 2);
x_99 = lean_ctor_get(x_73, 3);
x_100 = lean_ctor_get(x_73, 4);
x_101 = lean_ctor_get(x_73, 5);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_73);
x_102 = lean_ctor_get(x_74, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_74, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_74, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_74, 4);
lean_inc(x_105);
x_106 = lean_ctor_get(x_74, 5);
lean_inc(x_106);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 lean_ctor_release(x_74, 4);
 lean_ctor_release(x_74, 5);
 x_107 = x_74;
} else {
 lean_dec_ref(x_74);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_75, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_75, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_110 = x_75;
} else {
 lean_dec_ref(x_75);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 3, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
lean_ctor_set(x_111, 2, x_8);
if (lean_is_scalar(x_107)) {
 x_112 = lean_alloc_ctor(0, 6, 0);
} else {
 x_112 = x_107;
}
lean_ctor_set(x_112, 0, x_102);
lean_ctor_set(x_112, 1, x_103);
lean_ctor_set(x_112, 2, x_111);
lean_ctor_set(x_112, 3, x_104);
lean_ctor_set(x_112, 4, x_105);
lean_ctor_set(x_112, 5, x_106);
x_113 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_97);
lean_ctor_set(x_113, 2, x_98);
lean_ctor_set(x_113, 3, x_99);
lean_ctor_set(x_113, 4, x_100);
lean_ctor_set(x_113, 5, x_101);
lean_ctor_set(x_11, 1, x_113);
return x_11;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_114 = lean_ctor_get(x_11, 0);
lean_inc(x_114);
lean_dec(x_11);
x_115 = lean_ctor_get(x_73, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_73, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_73, 3);
lean_inc(x_117);
x_118 = lean_ctor_get(x_73, 4);
lean_inc(x_118);
x_119 = lean_ctor_get(x_73, 5);
lean_inc(x_119);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 lean_ctor_release(x_73, 3);
 lean_ctor_release(x_73, 4);
 lean_ctor_release(x_73, 5);
 x_120 = x_73;
} else {
 lean_dec_ref(x_73);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_74, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_74, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_74, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_74, 4);
lean_inc(x_124);
x_125 = lean_ctor_get(x_74, 5);
lean_inc(x_125);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 lean_ctor_release(x_74, 4);
 lean_ctor_release(x_74, 5);
 x_126 = x_74;
} else {
 lean_dec_ref(x_74);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_75, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_75, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_129 = x_75;
} else {
 lean_dec_ref(x_75);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(0, 3, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
lean_ctor_set(x_130, 2, x_8);
if (lean_is_scalar(x_126)) {
 x_131 = lean_alloc_ctor(0, 6, 0);
} else {
 x_131 = x_126;
}
lean_ctor_set(x_131, 0, x_121);
lean_ctor_set(x_131, 1, x_122);
lean_ctor_set(x_131, 2, x_130);
lean_ctor_set(x_131, 3, x_123);
lean_ctor_set(x_131, 4, x_124);
lean_ctor_set(x_131, 5, x_125);
if (lean_is_scalar(x_120)) {
 x_132 = lean_alloc_ctor(0, 6, 0);
} else {
 x_132 = x_120;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_115);
lean_ctor_set(x_132, 2, x_116);
lean_ctor_set(x_132, 3, x_117);
lean_ctor_set(x_132, 4, x_118);
lean_ctor_set(x_132, 5, x_119);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_114);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_resettingSynthInstanceCacheWhen___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_resettingSynthInstanceCacheWhen___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Elab_Term_resettingSynthInstanceCacheWhen___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_mkFreshId___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 3);
lean_inc(x_3);
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_dec(x_5);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 3);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
x_11 = lean_name_mk_numeral(x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_10, x_12);
lean_dec(x_10);
lean_ctor_set(x_3, 1, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_1);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
lean_inc(x_16);
lean_inc(x_15);
x_17 = lean_name_mk_numeral(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_16, x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_2, 3, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_1);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_ctor_get(x_2, 4);
x_26 = lean_ctor_get(x_2, 5);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_29 = x_3;
} else {
 lean_dec_ref(x_3);
 x_29 = lean_box(0);
}
lean_inc(x_28);
lean_inc(x_27);
x_30 = lean_name_mk_numeral(x_27, x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_28, x_31);
lean_dec(x_28);
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_34, 2, x_24);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_25);
lean_ctor_set(x_34, 5, x_26);
lean_ctor_set(x_1, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_1);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_ctor_get(x_1, 4);
x_40 = lean_ctor_get(x_1, 5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_1);
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 5);
lean_inc(x_45);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_46 = x_2;
} else {
 lean_dec_ref(x_2);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_3, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_49 = x_3;
} else {
 lean_dec_ref(x_3);
 x_49 = lean_box(0);
}
lean_inc(x_48);
lean_inc(x_47);
x_50 = lean_name_mk_numeral(x_47, x_48);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_48, x_51);
lean_dec(x_48);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
if (lean_is_scalar(x_46)) {
 x_54 = lean_alloc_ctor(0, 6, 0);
} else {
 x_54 = x_46;
}
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_42);
lean_ctor_set(x_54, 2, x_43);
lean_ctor_set(x_54, 3, x_53);
lean_ctor_set(x_54, 4, x_44);
lean_ctor_set(x_54, 5, x_45);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_36);
lean_ctor_set(x_55, 2, x_37);
lean_ctor_set(x_55, 3, x_38);
lean_ctor_set(x_55, 4, x_39);
lean_ctor_set(x_55, 5, x_40);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
lean_object* l_Lean_Elab_Term_mkFreshId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_mkFreshId___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_mkFreshId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_mkFreshId(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_10__elabBinderViews___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_fget(x_1, x_2);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_6, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_14, 1);
lean_dec(x_20);
lean_inc(x_5);
lean_inc(x_4);
lean_ctor_set(x_14, 2, x_5);
lean_ctor_set(x_14, 1, x_4);
lean_inc(x_6);
lean_inc(x_15);
x_21 = l_Lean_Elab_Term_elabType(x_15, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Term_mkFreshId___rarg(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_25);
x_27 = l_Lean_mkFVar(x_25);
lean_inc(x_27);
x_28 = lean_array_push(x_3, x_27);
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
x_30 = l_Lean_Syntax_getId(x_29);
lean_dec(x_29);
x_31 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
lean_inc(x_22);
x_32 = lean_local_ctx_mk_local_decl(x_4, x_25, x_30, x_22, x_31);
lean_inc(x_6);
x_33 = l_Lean_Elab_Term_isClass(x_15, x_22, x_6, x_26);
lean_dec(x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_27);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_2, x_36);
lean_dec(x_2);
x_2 = x_37;
x_3 = x_28;
x_4 = x_32;
x_7 = x_35;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
lean_dec(x_34);
x_41 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_39);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_27);
x_44 = lean_array_push(x_5, x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_2, x_45);
lean_dec(x_2);
x_2 = x_46;
x_3 = x_28;
x_4 = x_32;
x_5 = x_44;
x_7 = x_42;
goto _start;
}
}
else
{
uint8_t x_48; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_33);
if (x_48 == 0)
{
return x_33;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_33, 0);
x_50 = lean_ctor_get(x_33, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_33);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_6);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_21);
if (x_52 == 0)
{
return x_21;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_21, 0);
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_21);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_14, 0);
lean_inc(x_56);
lean_dec(x_14);
lean_inc(x_5);
lean_inc(x_4);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_4);
lean_ctor_set(x_57, 2, x_5);
lean_ctor_set(x_6, 0, x_57);
lean_inc(x_6);
lean_inc(x_15);
x_58 = l_Lean_Elab_Term_elabType(x_15, x_6, x_7);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Elab_Term_mkFreshId___rarg(x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_62);
x_64 = l_Lean_mkFVar(x_62);
lean_inc(x_64);
x_65 = lean_array_push(x_3, x_64);
x_66 = lean_ctor_get(x_13, 0);
lean_inc(x_66);
x_67 = l_Lean_Syntax_getId(x_66);
lean_dec(x_66);
x_68 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
lean_inc(x_59);
x_69 = lean_local_ctx_mk_local_decl(x_4, x_62, x_67, x_59, x_68);
lean_inc(x_6);
x_70 = l_Lean_Elab_Term_isClass(x_15, x_59, x_6, x_63);
lean_dec(x_15);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_add(x_2, x_73);
lean_dec(x_2);
x_2 = x_74;
x_3 = x_65;
x_4 = x_69;
x_7 = x_72;
goto _start;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
lean_dec(x_71);
x_78 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_76);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_64);
x_81 = lean_array_push(x_5, x_80);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_2, x_82);
lean_dec(x_2);
x_2 = x_83;
x_3 = x_65;
x_4 = x_69;
x_5 = x_81;
x_7 = x_79;
goto _start;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_69);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_85 = lean_ctor_get(x_70, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_70, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_87 = x_70;
} else {
 lean_dec_ref(x_70);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_6);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_89 = lean_ctor_get(x_58, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_58, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_91 = x_58;
} else {
 lean_dec_ref(x_58);
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
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_93 = lean_ctor_get(x_6, 1);
x_94 = lean_ctor_get(x_6, 2);
x_95 = lean_ctor_get(x_6, 3);
x_96 = lean_ctor_get(x_6, 4);
x_97 = lean_ctor_get(x_6, 5);
x_98 = lean_ctor_get(x_6, 6);
x_99 = lean_ctor_get(x_6, 7);
x_100 = lean_ctor_get(x_6, 8);
x_101 = lean_ctor_get_uint8(x_6, sizeof(void*)*9);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_6);
x_102 = lean_ctor_get(x_14, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_103 = x_14;
} else {
 lean_dec_ref(x_14);
 x_103 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_4);
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 3, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_4);
lean_ctor_set(x_104, 2, x_5);
x_105 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_93);
lean_ctor_set(x_105, 2, x_94);
lean_ctor_set(x_105, 3, x_95);
lean_ctor_set(x_105, 4, x_96);
lean_ctor_set(x_105, 5, x_97);
lean_ctor_set(x_105, 6, x_98);
lean_ctor_set(x_105, 7, x_99);
lean_ctor_set(x_105, 8, x_100);
lean_ctor_set_uint8(x_105, sizeof(void*)*9, x_101);
lean_inc(x_105);
lean_inc(x_15);
x_106 = l_Lean_Elab_Term_elabType(x_15, x_105, x_7);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_Elab_Term_mkFreshId___rarg(x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_110);
x_112 = l_Lean_mkFVar(x_110);
lean_inc(x_112);
x_113 = lean_array_push(x_3, x_112);
x_114 = lean_ctor_get(x_13, 0);
lean_inc(x_114);
x_115 = l_Lean_Syntax_getId(x_114);
lean_dec(x_114);
x_116 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
lean_inc(x_107);
x_117 = lean_local_ctx_mk_local_decl(x_4, x_110, x_115, x_107, x_116);
lean_inc(x_105);
x_118 = l_Lean_Elab_Term_isClass(x_15, x_107, x_105, x_111);
lean_dec(x_15);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_112);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_nat_add(x_2, x_121);
lean_dec(x_2);
x_2 = x_122;
x_3 = x_113;
x_4 = x_117;
x_6 = x_105;
x_7 = x_120;
goto _start;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_124 = lean_ctor_get(x_118, 1);
lean_inc(x_124);
lean_dec(x_118);
x_125 = lean_ctor_get(x_119, 0);
lean_inc(x_125);
lean_dec(x_119);
x_126 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_124);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_112);
x_129 = lean_array_push(x_5, x_128);
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_nat_add(x_2, x_130);
lean_dec(x_2);
x_2 = x_131;
x_3 = x_113;
x_4 = x_117;
x_5 = x_129;
x_6 = x_105;
x_7 = x_127;
goto _start;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_117);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_105);
lean_dec(x_5);
lean_dec(x_2);
x_133 = lean_ctor_get(x_118, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_118, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_135 = x_118;
} else {
 lean_dec_ref(x_118);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_105);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = lean_ctor_get(x_106, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_106, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_139 = x_106;
} else {
 lean_dec_ref(x_106);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_10__elabBinderViews___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_10__elabBinderViews___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_10__elabBinderViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_10__elabBinderViews___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_10__elabBinderViews___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_10__elabBinderViews(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_11__elabBindersAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_1, x_2);
x_14 = l___private_Init_Lean_Elab_Term_9__matchBinder(x_13, x_6, x_7);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_18 = l___private_Init_Lean_Elab_Term_10__elabBinderViews___main(x_15, x_17, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_2, x_25);
lean_dec(x_2);
x_2 = x_26;
x_3 = x_22;
x_4 = x_23;
x_5 = x_24;
x_7 = x_21;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_11__elabBindersAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_11__elabBindersAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_11__elabBindersAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_11__elabBindersAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_11__elabBindersAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_11__elabBindersAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lean_Elab_Term_getLCtx(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Term_getLocalInsts(x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_empty___closed__1;
lean_inc(x_3);
lean_inc(x_9);
x_13 = l___private_Init_Lean_Elab_Term_11__elabBindersAux___main(x_1, x_11, x_12, x_6, x_9, x_3, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_array_get_size(x_9);
lean_dec(x_9);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 2);
lean_dec(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_dec(x_27);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 1, x_18);
x_28 = lean_apply_3(x_2, x_17, x_3, x_16);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_18);
lean_ctor_set(x_30, 2, x_19);
lean_ctor_set(x_3, 0, x_30);
x_31 = lean_apply_3(x_2, x_17, x_3, x_16);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_32 = lean_ctor_get(x_3, 0);
x_33 = lean_ctor_get(x_3, 1);
x_34 = lean_ctor_get(x_3, 2);
x_35 = lean_ctor_get(x_3, 3);
x_36 = lean_ctor_get(x_3, 4);
x_37 = lean_ctor_get(x_3, 5);
x_38 = lean_ctor_get(x_3, 6);
x_39 = lean_ctor_get(x_3, 7);
x_40 = lean_ctor_get(x_3, 8);
x_41 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_3);
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 x_43 = x_32;
} else {
 lean_dec_ref(x_32);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 3, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_18);
lean_ctor_set(x_44, 2, x_19);
x_45 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_35);
lean_ctor_set(x_45, 4, x_36);
lean_ctor_set(x_45, 5, x_37);
lean_ctor_set(x_45, 6, x_38);
lean_ctor_set(x_45, 7, x_39);
lean_ctor_set(x_45, 8, x_40);
lean_ctor_set_uint8(x_45, sizeof(void*)*9, x_41);
x_46 = lean_apply_3(x_2, x_17, x_45, x_16);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_47 = lean_ctor_get(x_16, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 2);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_48, 2);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_16);
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = !lean_is_exclusive(x_3);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_3, 0);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_51, 2);
lean_dec(x_56);
x_57 = lean_ctor_get(x_51, 1);
lean_dec(x_57);
lean_ctor_set(x_51, 2, x_19);
lean_ctor_set(x_51, 1, x_18);
x_58 = lean_apply_3(x_2, x_17, x_3, x_52);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 2);
lean_inc(x_61);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_58, 1);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_59, 0);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_60);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_60, 2);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_61);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_61, 2);
lean_dec(x_69);
lean_ctor_set(x_61, 2, x_49);
return x_58;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_61, 0);
x_71 = lean_ctor_get(x_61, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_61);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_49);
lean_ctor_set(x_60, 2, x_72);
return x_58;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_73 = lean_ctor_get(x_60, 0);
x_74 = lean_ctor_get(x_60, 1);
x_75 = lean_ctor_get(x_60, 3);
x_76 = lean_ctor_get(x_60, 4);
x_77 = lean_ctor_get(x_60, 5);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_60);
x_78 = lean_ctor_get(x_61, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_61, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 x_80 = x_61;
} else {
 lean_dec_ref(x_61);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 3, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
lean_ctor_set(x_81, 2, x_49);
x_82 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_75);
lean_ctor_set(x_82, 4, x_76);
lean_ctor_set(x_82, 5, x_77);
lean_ctor_set(x_59, 0, x_82);
return x_58;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_83 = lean_ctor_get(x_59, 1);
x_84 = lean_ctor_get(x_59, 2);
x_85 = lean_ctor_get(x_59, 3);
x_86 = lean_ctor_get(x_59, 4);
x_87 = lean_ctor_get(x_59, 5);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_59);
x_88 = lean_ctor_get(x_60, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_60, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_60, 3);
lean_inc(x_90);
x_91 = lean_ctor_get(x_60, 4);
lean_inc(x_91);
x_92 = lean_ctor_get(x_60, 5);
lean_inc(x_92);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 lean_ctor_release(x_60, 3);
 lean_ctor_release(x_60, 4);
 lean_ctor_release(x_60, 5);
 x_93 = x_60;
} else {
 lean_dec_ref(x_60);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_61, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_61, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 x_96 = x_61;
} else {
 lean_dec_ref(x_61);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 3, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_97, 2, x_49);
if (lean_is_scalar(x_93)) {
 x_98 = lean_alloc_ctor(0, 6, 0);
} else {
 x_98 = x_93;
}
lean_ctor_set(x_98, 0, x_88);
lean_ctor_set(x_98, 1, x_89);
lean_ctor_set(x_98, 2, x_97);
lean_ctor_set(x_98, 3, x_90);
lean_ctor_set(x_98, 4, x_91);
lean_ctor_set(x_98, 5, x_92);
x_99 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_83);
lean_ctor_set(x_99, 2, x_84);
lean_ctor_set(x_99, 3, x_85);
lean_ctor_set(x_99, 4, x_86);
lean_ctor_set(x_99, 5, x_87);
lean_ctor_set(x_58, 1, x_99);
return x_58;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_100 = lean_ctor_get(x_58, 0);
lean_inc(x_100);
lean_dec(x_58);
x_101 = lean_ctor_get(x_59, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_59, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_59, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_59, 4);
lean_inc(x_104);
x_105 = lean_ctor_get(x_59, 5);
lean_inc(x_105);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 lean_ctor_release(x_59, 5);
 x_106 = x_59;
} else {
 lean_dec_ref(x_59);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_60, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_60, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_60, 3);
lean_inc(x_109);
x_110 = lean_ctor_get(x_60, 4);
lean_inc(x_110);
x_111 = lean_ctor_get(x_60, 5);
lean_inc(x_111);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 lean_ctor_release(x_60, 3);
 lean_ctor_release(x_60, 4);
 lean_ctor_release(x_60, 5);
 x_112 = x_60;
} else {
 lean_dec_ref(x_60);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_61, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_61, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 x_115 = x_61;
} else {
 lean_dec_ref(x_61);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 3, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
lean_ctor_set(x_116, 2, x_49);
if (lean_is_scalar(x_112)) {
 x_117 = lean_alloc_ctor(0, 6, 0);
} else {
 x_117 = x_112;
}
lean_ctor_set(x_117, 0, x_107);
lean_ctor_set(x_117, 1, x_108);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_117, 3, x_109);
lean_ctor_set(x_117, 4, x_110);
lean_ctor_set(x_117, 5, x_111);
if (lean_is_scalar(x_106)) {
 x_118 = lean_alloc_ctor(0, 6, 0);
} else {
 x_118 = x_106;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_101);
lean_ctor_set(x_118, 2, x_102);
lean_ctor_set(x_118, 3, x_103);
lean_ctor_set(x_118, 4, x_104);
lean_ctor_set(x_118, 5, x_105);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_100);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_120 = lean_ctor_get(x_58, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_121, 2);
lean_inc(x_122);
x_123 = !lean_is_exclusive(x_58);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_58, 1);
lean_dec(x_124);
x_125 = !lean_is_exclusive(x_120);
if (x_125 == 0)
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_120, 0);
lean_dec(x_126);
x_127 = !lean_is_exclusive(x_121);
if (x_127 == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_121, 2);
lean_dec(x_128);
x_129 = !lean_is_exclusive(x_122);
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_122, 2);
lean_dec(x_130);
lean_ctor_set(x_122, 2, x_49);
return x_58;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_122, 0);
x_132 = lean_ctor_get(x_122, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_122);
x_133 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_133, 2, x_49);
lean_ctor_set(x_121, 2, x_133);
return x_58;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_134 = lean_ctor_get(x_121, 0);
x_135 = lean_ctor_get(x_121, 1);
x_136 = lean_ctor_get(x_121, 3);
x_137 = lean_ctor_get(x_121, 4);
x_138 = lean_ctor_get(x_121, 5);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_121);
x_139 = lean_ctor_get(x_122, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_122, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 x_141 = x_122;
} else {
 lean_dec_ref(x_122);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(0, 3, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
lean_ctor_set(x_142, 2, x_49);
x_143 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_143, 0, x_134);
lean_ctor_set(x_143, 1, x_135);
lean_ctor_set(x_143, 2, x_142);
lean_ctor_set(x_143, 3, x_136);
lean_ctor_set(x_143, 4, x_137);
lean_ctor_set(x_143, 5, x_138);
lean_ctor_set(x_120, 0, x_143);
return x_58;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_144 = lean_ctor_get(x_120, 1);
x_145 = lean_ctor_get(x_120, 2);
x_146 = lean_ctor_get(x_120, 3);
x_147 = lean_ctor_get(x_120, 4);
x_148 = lean_ctor_get(x_120, 5);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_120);
x_149 = lean_ctor_get(x_121, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_121, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_121, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_121, 4);
lean_inc(x_152);
x_153 = lean_ctor_get(x_121, 5);
lean_inc(x_153);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 lean_ctor_release(x_121, 4);
 lean_ctor_release(x_121, 5);
 x_154 = x_121;
} else {
 lean_dec_ref(x_121);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_122, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_122, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 x_157 = x_122;
} else {
 lean_dec_ref(x_122);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 3, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
lean_ctor_set(x_158, 2, x_49);
if (lean_is_scalar(x_154)) {
 x_159 = lean_alloc_ctor(0, 6, 0);
} else {
 x_159 = x_154;
}
lean_ctor_set(x_159, 0, x_149);
lean_ctor_set(x_159, 1, x_150);
lean_ctor_set(x_159, 2, x_158);
lean_ctor_set(x_159, 3, x_151);
lean_ctor_set(x_159, 4, x_152);
lean_ctor_set(x_159, 5, x_153);
x_160 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_144);
lean_ctor_set(x_160, 2, x_145);
lean_ctor_set(x_160, 3, x_146);
lean_ctor_set(x_160, 4, x_147);
lean_ctor_set(x_160, 5, x_148);
lean_ctor_set(x_58, 1, x_160);
return x_58;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_161 = lean_ctor_get(x_58, 0);
lean_inc(x_161);
lean_dec(x_58);
x_162 = lean_ctor_get(x_120, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_120, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_120, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_120, 4);
lean_inc(x_165);
x_166 = lean_ctor_get(x_120, 5);
lean_inc(x_166);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 lean_ctor_release(x_120, 5);
 x_167 = x_120;
} else {
 lean_dec_ref(x_120);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_121, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_121, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_121, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_121, 4);
lean_inc(x_171);
x_172 = lean_ctor_get(x_121, 5);
lean_inc(x_172);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 lean_ctor_release(x_121, 4);
 lean_ctor_release(x_121, 5);
 x_173 = x_121;
} else {
 lean_dec_ref(x_121);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_122, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_122, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 x_176 = x_122;
} else {
 lean_dec_ref(x_122);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 3, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
lean_ctor_set(x_177, 2, x_49);
if (lean_is_scalar(x_173)) {
 x_178 = lean_alloc_ctor(0, 6, 0);
} else {
 x_178 = x_173;
}
lean_ctor_set(x_178, 0, x_168);
lean_ctor_set(x_178, 1, x_169);
lean_ctor_set(x_178, 2, x_177);
lean_ctor_set(x_178, 3, x_170);
lean_ctor_set(x_178, 4, x_171);
lean_ctor_set(x_178, 5, x_172);
if (lean_is_scalar(x_167)) {
 x_179 = lean_alloc_ctor(0, 6, 0);
} else {
 x_179 = x_167;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_162);
lean_ctor_set(x_179, 2, x_163);
lean_ctor_set(x_179, 3, x_164);
lean_ctor_set(x_179, 4, x_165);
lean_ctor_set(x_179, 5, x_166);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_161);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_51, 0);
lean_inc(x_181);
lean_dec(x_51);
x_182 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_18);
lean_ctor_set(x_182, 2, x_19);
lean_ctor_set(x_3, 0, x_182);
x_183 = lean_apply_3(x_2, x_17, x_3, x_52);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_185, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_183, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_188 = x_183;
} else {
 lean_dec_ref(x_183);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_184, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_184, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_184, 3);
lean_inc(x_191);
x_192 = lean_ctor_get(x_184, 4);
lean_inc(x_192);
x_193 = lean_ctor_get(x_184, 5);
lean_inc(x_193);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 lean_ctor_release(x_184, 4);
 lean_ctor_release(x_184, 5);
 x_194 = x_184;
} else {
 lean_dec_ref(x_184);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_185, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_185, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_185, 3);
lean_inc(x_197);
x_198 = lean_ctor_get(x_185, 4);
lean_inc(x_198);
x_199 = lean_ctor_get(x_185, 5);
lean_inc(x_199);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 lean_ctor_release(x_185, 4);
 lean_ctor_release(x_185, 5);
 x_200 = x_185;
} else {
 lean_dec_ref(x_185);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_186, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_186, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 x_203 = x_186;
} else {
 lean_dec_ref(x_186);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 3, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
lean_ctor_set(x_204, 2, x_49);
if (lean_is_scalar(x_200)) {
 x_205 = lean_alloc_ctor(0, 6, 0);
} else {
 x_205 = x_200;
}
lean_ctor_set(x_205, 0, x_195);
lean_ctor_set(x_205, 1, x_196);
lean_ctor_set(x_205, 2, x_204);
lean_ctor_set(x_205, 3, x_197);
lean_ctor_set(x_205, 4, x_198);
lean_ctor_set(x_205, 5, x_199);
if (lean_is_scalar(x_194)) {
 x_206 = lean_alloc_ctor(0, 6, 0);
} else {
 x_206 = x_194;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_189);
lean_ctor_set(x_206, 2, x_190);
lean_ctor_set(x_206, 3, x_191);
lean_ctor_set(x_206, 4, x_192);
lean_ctor_set(x_206, 5, x_193);
if (lean_is_scalar(x_188)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_188;
}
lean_ctor_set(x_207, 0, x_187);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_208 = lean_ctor_get(x_183, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_209, 2);
lean_inc(x_210);
x_211 = lean_ctor_get(x_183, 0);
lean_inc(x_211);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_212 = x_183;
} else {
 lean_dec_ref(x_183);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_208, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_208, 2);
lean_inc(x_214);
x_215 = lean_ctor_get(x_208, 3);
lean_inc(x_215);
x_216 = lean_ctor_get(x_208, 4);
lean_inc(x_216);
x_217 = lean_ctor_get(x_208, 5);
lean_inc(x_217);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 lean_ctor_release(x_208, 3);
 lean_ctor_release(x_208, 4);
 lean_ctor_release(x_208, 5);
 x_218 = x_208;
} else {
 lean_dec_ref(x_208);
 x_218 = lean_box(0);
}
x_219 = lean_ctor_get(x_209, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_209, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_209, 3);
lean_inc(x_221);
x_222 = lean_ctor_get(x_209, 4);
lean_inc(x_222);
x_223 = lean_ctor_get(x_209, 5);
lean_inc(x_223);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 lean_ctor_release(x_209, 2);
 lean_ctor_release(x_209, 3);
 lean_ctor_release(x_209, 4);
 lean_ctor_release(x_209, 5);
 x_224 = x_209;
} else {
 lean_dec_ref(x_209);
 x_224 = lean_box(0);
}
x_225 = lean_ctor_get(x_210, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_210, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 x_227 = x_210;
} else {
 lean_dec_ref(x_210);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(0, 3, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
lean_ctor_set(x_228, 2, x_49);
if (lean_is_scalar(x_224)) {
 x_229 = lean_alloc_ctor(0, 6, 0);
} else {
 x_229 = x_224;
}
lean_ctor_set(x_229, 0, x_219);
lean_ctor_set(x_229, 1, x_220);
lean_ctor_set(x_229, 2, x_228);
lean_ctor_set(x_229, 3, x_221);
lean_ctor_set(x_229, 4, x_222);
lean_ctor_set(x_229, 5, x_223);
if (lean_is_scalar(x_218)) {
 x_230 = lean_alloc_ctor(0, 6, 0);
} else {
 x_230 = x_218;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_213);
lean_ctor_set(x_230, 2, x_214);
lean_ctor_set(x_230, 3, x_215);
lean_ctor_set(x_230, 4, x_216);
lean_ctor_set(x_230, 5, x_217);
if (lean_is_scalar(x_212)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_212;
}
lean_ctor_set(x_231, 0, x_211);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_232 = lean_ctor_get(x_3, 1);
x_233 = lean_ctor_get(x_3, 2);
x_234 = lean_ctor_get(x_3, 3);
x_235 = lean_ctor_get(x_3, 4);
x_236 = lean_ctor_get(x_3, 5);
x_237 = lean_ctor_get(x_3, 6);
x_238 = lean_ctor_get(x_3, 7);
x_239 = lean_ctor_get(x_3, 8);
x_240 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_3);
x_241 = lean_ctor_get(x_51, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 x_242 = x_51;
} else {
 lean_dec_ref(x_51);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(0, 3, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_18);
lean_ctor_set(x_243, 2, x_19);
x_244 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_232);
lean_ctor_set(x_244, 2, x_233);
lean_ctor_set(x_244, 3, x_234);
lean_ctor_set(x_244, 4, x_235);
lean_ctor_set(x_244, 5, x_236);
lean_ctor_set(x_244, 6, x_237);
lean_ctor_set(x_244, 7, x_238);
lean_ctor_set(x_244, 8, x_239);
lean_ctor_set_uint8(x_244, sizeof(void*)*9, x_240);
x_245 = lean_apply_3(x_2, x_17, x_244, x_52);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_247, 2);
lean_inc(x_248);
x_249 = lean_ctor_get(x_245, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_250 = x_245;
} else {
 lean_dec_ref(x_245);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_246, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_246, 2);
lean_inc(x_252);
x_253 = lean_ctor_get(x_246, 3);
lean_inc(x_253);
x_254 = lean_ctor_get(x_246, 4);
lean_inc(x_254);
x_255 = lean_ctor_get(x_246, 5);
lean_inc(x_255);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 lean_ctor_release(x_246, 2);
 lean_ctor_release(x_246, 3);
 lean_ctor_release(x_246, 4);
 lean_ctor_release(x_246, 5);
 x_256 = x_246;
} else {
 lean_dec_ref(x_246);
 x_256 = lean_box(0);
}
x_257 = lean_ctor_get(x_247, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_247, 1);
lean_inc(x_258);
x_259 = lean_ctor_get(x_247, 3);
lean_inc(x_259);
x_260 = lean_ctor_get(x_247, 4);
lean_inc(x_260);
x_261 = lean_ctor_get(x_247, 5);
lean_inc(x_261);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 lean_ctor_release(x_247, 3);
 lean_ctor_release(x_247, 4);
 lean_ctor_release(x_247, 5);
 x_262 = x_247;
} else {
 lean_dec_ref(x_247);
 x_262 = lean_box(0);
}
x_263 = lean_ctor_get(x_248, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_248, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 lean_ctor_release(x_248, 2);
 x_265 = x_248;
} else {
 lean_dec_ref(x_248);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(0, 3, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
lean_ctor_set(x_266, 2, x_49);
if (lean_is_scalar(x_262)) {
 x_267 = lean_alloc_ctor(0, 6, 0);
} else {
 x_267 = x_262;
}
lean_ctor_set(x_267, 0, x_257);
lean_ctor_set(x_267, 1, x_258);
lean_ctor_set(x_267, 2, x_266);
lean_ctor_set(x_267, 3, x_259);
lean_ctor_set(x_267, 4, x_260);
lean_ctor_set(x_267, 5, x_261);
if (lean_is_scalar(x_256)) {
 x_268 = lean_alloc_ctor(0, 6, 0);
} else {
 x_268 = x_256;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_251);
lean_ctor_set(x_268, 2, x_252);
lean_ctor_set(x_268, 3, x_253);
lean_ctor_set(x_268, 4, x_254);
lean_ctor_set(x_268, 5, x_255);
if (lean_is_scalar(x_250)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_250;
}
lean_ctor_set(x_269, 0, x_249);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_270 = lean_ctor_get(x_245, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_271, 2);
lean_inc(x_272);
x_273 = lean_ctor_get(x_245, 0);
lean_inc(x_273);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_274 = x_245;
} else {
 lean_dec_ref(x_245);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_270, 1);
lean_inc(x_275);
x_276 = lean_ctor_get(x_270, 2);
lean_inc(x_276);
x_277 = lean_ctor_get(x_270, 3);
lean_inc(x_277);
x_278 = lean_ctor_get(x_270, 4);
lean_inc(x_278);
x_279 = lean_ctor_get(x_270, 5);
lean_inc(x_279);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 lean_ctor_release(x_270, 2);
 lean_ctor_release(x_270, 3);
 lean_ctor_release(x_270, 4);
 lean_ctor_release(x_270, 5);
 x_280 = x_270;
} else {
 lean_dec_ref(x_270);
 x_280 = lean_box(0);
}
x_281 = lean_ctor_get(x_271, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_271, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_271, 3);
lean_inc(x_283);
x_284 = lean_ctor_get(x_271, 4);
lean_inc(x_284);
x_285 = lean_ctor_get(x_271, 5);
lean_inc(x_285);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 lean_ctor_release(x_271, 4);
 lean_ctor_release(x_271, 5);
 x_286 = x_271;
} else {
 lean_dec_ref(x_271);
 x_286 = lean_box(0);
}
x_287 = lean_ctor_get(x_272, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_272, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 x_289 = x_272;
} else {
 lean_dec_ref(x_272);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(0, 3, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_288);
lean_ctor_set(x_290, 2, x_49);
if (lean_is_scalar(x_286)) {
 x_291 = lean_alloc_ctor(0, 6, 0);
} else {
 x_291 = x_286;
}
lean_ctor_set(x_291, 0, x_281);
lean_ctor_set(x_291, 1, x_282);
lean_ctor_set(x_291, 2, x_290);
lean_ctor_set(x_291, 3, x_283);
lean_ctor_set(x_291, 4, x_284);
lean_ctor_set(x_291, 5, x_285);
if (lean_is_scalar(x_280)) {
 x_292 = lean_alloc_ctor(0, 6, 0);
} else {
 x_292 = x_280;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_275);
lean_ctor_set(x_292, 2, x_276);
lean_ctor_set(x_292, 3, x_277);
lean_ctor_set(x_292, 4, x_278);
lean_ctor_set(x_292, 5, x_279);
if (lean_is_scalar(x_274)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_274;
}
lean_ctor_set(x_293, 0, x_273);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
}
else
{
uint8_t x_294; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_294 = !lean_is_exclusive(x_13);
if (x_294 == 0)
{
return x_13;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_13, 0);
x_296 = lean_ctor_get(x_13, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_13);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabBinders(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabBinders___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabBinder___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = l_Lean_mkOptionalNode___closed__1;
x_6 = lean_array_push(x_5, x_1);
x_7 = l_Lean_Elab_Term_getLCtx(x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Term_getLocalInsts(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_empty___closed__1;
lean_inc(x_3);
lean_inc(x_11);
x_15 = l___private_Init_Lean_Elab_Term_11__elabBindersAux___main(x_6, x_13, x_14, x_8, x_11, x_3, x_12);
lean_dec(x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_array_get_size(x_11);
lean_dec(x_11);
x_23 = lean_array_get_size(x_21);
x_24 = lean_nat_dec_lt(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_26, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_dec(x_29);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 1, x_20);
x_30 = l_Lean_Expr_Inhabited;
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_array_get(x_30, x_19, x_31);
lean_dec(x_19);
x_33 = lean_apply_3(x_2, x_32, x_3, x_18);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_20);
lean_ctor_set(x_35, 2, x_21);
lean_ctor_set(x_3, 0, x_35);
x_36 = l_Lean_Expr_Inhabited;
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_array_get(x_36, x_19, x_37);
lean_dec(x_19);
x_39 = lean_apply_3(x_2, x_38, x_3, x_18);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_3, 1);
x_42 = lean_ctor_get(x_3, 2);
x_43 = lean_ctor_get(x_3, 3);
x_44 = lean_ctor_get(x_3, 4);
x_45 = lean_ctor_get(x_3, 5);
x_46 = lean_ctor_get(x_3, 6);
x_47 = lean_ctor_get(x_3, 7);
x_48 = lean_ctor_get(x_3, 8);
x_49 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_3);
x_50 = lean_ctor_get(x_40, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 3, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_20);
lean_ctor_set(x_52, 2, x_21);
x_53 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_41);
lean_ctor_set(x_53, 2, x_42);
lean_ctor_set(x_53, 3, x_43);
lean_ctor_set(x_53, 4, x_44);
lean_ctor_set(x_53, 5, x_45);
lean_ctor_set(x_53, 6, x_46);
lean_ctor_set(x_53, 7, x_47);
lean_ctor_set(x_53, 8, x_48);
lean_ctor_set_uint8(x_53, sizeof(void*)*9, x_49);
x_54 = l_Lean_Expr_Inhabited;
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_array_get(x_54, x_19, x_55);
lean_dec(x_19);
x_57 = lean_apply_3(x_2, x_56, x_53, x_18);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_58 = lean_ctor_get(x_18, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 2);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_59, 2);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_18);
x_62 = lean_ctor_get(x_3, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = !lean_is_exclusive(x_3);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_3, 0);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_62, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_62, 1);
lean_dec(x_68);
lean_ctor_set(x_62, 2, x_21);
lean_ctor_set(x_62, 1, x_20);
x_69 = l_Lean_Expr_Inhabited;
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_array_get(x_69, x_19, x_70);
lean_dec(x_19);
x_72 = lean_apply_3(x_2, x_71, x_3, x_63);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_74, 2);
lean_inc(x_75);
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_72, 1);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_73);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_73, 0);
lean_dec(x_79);
x_80 = !lean_is_exclusive(x_74);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_74, 2);
lean_dec(x_81);
x_82 = !lean_is_exclusive(x_75);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_75, 2);
lean_dec(x_83);
lean_ctor_set(x_75, 2, x_60);
return x_72;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_75, 0);
x_85 = lean_ctor_get(x_75, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_75);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_60);
lean_ctor_set(x_74, 2, x_86);
return x_72;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_74, 0);
x_88 = lean_ctor_get(x_74, 1);
x_89 = lean_ctor_get(x_74, 3);
x_90 = lean_ctor_get(x_74, 4);
x_91 = lean_ctor_get(x_74, 5);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_74);
x_92 = lean_ctor_get(x_75, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_75, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_94 = x_75;
} else {
 lean_dec_ref(x_75);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 3, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_60);
x_96 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_96, 0, x_87);
lean_ctor_set(x_96, 1, x_88);
lean_ctor_set(x_96, 2, x_95);
lean_ctor_set(x_96, 3, x_89);
lean_ctor_set(x_96, 4, x_90);
lean_ctor_set(x_96, 5, x_91);
lean_ctor_set(x_73, 0, x_96);
return x_72;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_97 = lean_ctor_get(x_73, 1);
x_98 = lean_ctor_get(x_73, 2);
x_99 = lean_ctor_get(x_73, 3);
x_100 = lean_ctor_get(x_73, 4);
x_101 = lean_ctor_get(x_73, 5);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_73);
x_102 = lean_ctor_get(x_74, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_74, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_74, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_74, 4);
lean_inc(x_105);
x_106 = lean_ctor_get(x_74, 5);
lean_inc(x_106);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 lean_ctor_release(x_74, 4);
 lean_ctor_release(x_74, 5);
 x_107 = x_74;
} else {
 lean_dec_ref(x_74);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_75, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_75, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_110 = x_75;
} else {
 lean_dec_ref(x_75);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 3, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
lean_ctor_set(x_111, 2, x_60);
if (lean_is_scalar(x_107)) {
 x_112 = lean_alloc_ctor(0, 6, 0);
} else {
 x_112 = x_107;
}
lean_ctor_set(x_112, 0, x_102);
lean_ctor_set(x_112, 1, x_103);
lean_ctor_set(x_112, 2, x_111);
lean_ctor_set(x_112, 3, x_104);
lean_ctor_set(x_112, 4, x_105);
lean_ctor_set(x_112, 5, x_106);
x_113 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_97);
lean_ctor_set(x_113, 2, x_98);
lean_ctor_set(x_113, 3, x_99);
lean_ctor_set(x_113, 4, x_100);
lean_ctor_set(x_113, 5, x_101);
lean_ctor_set(x_72, 1, x_113);
return x_72;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_114 = lean_ctor_get(x_72, 0);
lean_inc(x_114);
lean_dec(x_72);
x_115 = lean_ctor_get(x_73, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_73, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_73, 3);
lean_inc(x_117);
x_118 = lean_ctor_get(x_73, 4);
lean_inc(x_118);
x_119 = lean_ctor_get(x_73, 5);
lean_inc(x_119);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 lean_ctor_release(x_73, 3);
 lean_ctor_release(x_73, 4);
 lean_ctor_release(x_73, 5);
 x_120 = x_73;
} else {
 lean_dec_ref(x_73);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_74, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_74, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_74, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_74, 4);
lean_inc(x_124);
x_125 = lean_ctor_get(x_74, 5);
lean_inc(x_125);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 lean_ctor_release(x_74, 4);
 lean_ctor_release(x_74, 5);
 x_126 = x_74;
} else {
 lean_dec_ref(x_74);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_75, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_75, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_129 = x_75;
} else {
 lean_dec_ref(x_75);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(0, 3, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
lean_ctor_set(x_130, 2, x_60);
if (lean_is_scalar(x_126)) {
 x_131 = lean_alloc_ctor(0, 6, 0);
} else {
 x_131 = x_126;
}
lean_ctor_set(x_131, 0, x_121);
lean_ctor_set(x_131, 1, x_122);
lean_ctor_set(x_131, 2, x_130);
lean_ctor_set(x_131, 3, x_123);
lean_ctor_set(x_131, 4, x_124);
lean_ctor_set(x_131, 5, x_125);
if (lean_is_scalar(x_120)) {
 x_132 = lean_alloc_ctor(0, 6, 0);
} else {
 x_132 = x_120;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_115);
lean_ctor_set(x_132, 2, x_116);
lean_ctor_set(x_132, 3, x_117);
lean_ctor_set(x_132, 4, x_118);
lean_ctor_set(x_132, 5, x_119);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_114);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_134 = lean_ctor_get(x_72, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_135, 2);
lean_inc(x_136);
x_137 = !lean_is_exclusive(x_72);
if (x_137 == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_72, 1);
lean_dec(x_138);
x_139 = !lean_is_exclusive(x_134);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_134, 0);
lean_dec(x_140);
x_141 = !lean_is_exclusive(x_135);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_135, 2);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_136);
if (x_143 == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_136, 2);
lean_dec(x_144);
lean_ctor_set(x_136, 2, x_60);
return x_72;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_136, 0);
x_146 = lean_ctor_get(x_136, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_136);
x_147 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_60);
lean_ctor_set(x_135, 2, x_147);
return x_72;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_148 = lean_ctor_get(x_135, 0);
x_149 = lean_ctor_get(x_135, 1);
x_150 = lean_ctor_get(x_135, 3);
x_151 = lean_ctor_get(x_135, 4);
x_152 = lean_ctor_get(x_135, 5);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_135);
x_153 = lean_ctor_get(x_136, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_136, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 lean_ctor_release(x_136, 2);
 x_155 = x_136;
} else {
 lean_dec_ref(x_136);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 3, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
lean_ctor_set(x_156, 2, x_60);
x_157 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_157, 0, x_148);
lean_ctor_set(x_157, 1, x_149);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_157, 3, x_150);
lean_ctor_set(x_157, 4, x_151);
lean_ctor_set(x_157, 5, x_152);
lean_ctor_set(x_134, 0, x_157);
return x_72;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_158 = lean_ctor_get(x_134, 1);
x_159 = lean_ctor_get(x_134, 2);
x_160 = lean_ctor_get(x_134, 3);
x_161 = lean_ctor_get(x_134, 4);
x_162 = lean_ctor_get(x_134, 5);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_134);
x_163 = lean_ctor_get(x_135, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_135, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_135, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_135, 4);
lean_inc(x_166);
x_167 = lean_ctor_get(x_135, 5);
lean_inc(x_167);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 lean_ctor_release(x_135, 5);
 x_168 = x_135;
} else {
 lean_dec_ref(x_135);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_136, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_136, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 lean_ctor_release(x_136, 2);
 x_171 = x_136;
} else {
 lean_dec_ref(x_136);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(0, 3, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
lean_ctor_set(x_172, 2, x_60);
if (lean_is_scalar(x_168)) {
 x_173 = lean_alloc_ctor(0, 6, 0);
} else {
 x_173 = x_168;
}
lean_ctor_set(x_173, 0, x_163);
lean_ctor_set(x_173, 1, x_164);
lean_ctor_set(x_173, 2, x_172);
lean_ctor_set(x_173, 3, x_165);
lean_ctor_set(x_173, 4, x_166);
lean_ctor_set(x_173, 5, x_167);
x_174 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_158);
lean_ctor_set(x_174, 2, x_159);
lean_ctor_set(x_174, 3, x_160);
lean_ctor_set(x_174, 4, x_161);
lean_ctor_set(x_174, 5, x_162);
lean_ctor_set(x_72, 1, x_174);
return x_72;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_175 = lean_ctor_get(x_72, 0);
lean_inc(x_175);
lean_dec(x_72);
x_176 = lean_ctor_get(x_134, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_134, 2);
lean_inc(x_177);
x_178 = lean_ctor_get(x_134, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_134, 4);
lean_inc(x_179);
x_180 = lean_ctor_get(x_134, 5);
lean_inc(x_180);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 lean_ctor_release(x_134, 2);
 lean_ctor_release(x_134, 3);
 lean_ctor_release(x_134, 4);
 lean_ctor_release(x_134, 5);
 x_181 = x_134;
} else {
 lean_dec_ref(x_134);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_135, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_135, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_135, 3);
lean_inc(x_184);
x_185 = lean_ctor_get(x_135, 4);
lean_inc(x_185);
x_186 = lean_ctor_get(x_135, 5);
lean_inc(x_186);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 lean_ctor_release(x_135, 5);
 x_187 = x_135;
} else {
 lean_dec_ref(x_135);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_136, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_136, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 lean_ctor_release(x_136, 2);
 x_190 = x_136;
} else {
 lean_dec_ref(x_136);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(0, 3, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
lean_ctor_set(x_191, 2, x_60);
if (lean_is_scalar(x_187)) {
 x_192 = lean_alloc_ctor(0, 6, 0);
} else {
 x_192 = x_187;
}
lean_ctor_set(x_192, 0, x_182);
lean_ctor_set(x_192, 1, x_183);
lean_ctor_set(x_192, 2, x_191);
lean_ctor_set(x_192, 3, x_184);
lean_ctor_set(x_192, 4, x_185);
lean_ctor_set(x_192, 5, x_186);
if (lean_is_scalar(x_181)) {
 x_193 = lean_alloc_ctor(0, 6, 0);
} else {
 x_193 = x_181;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_176);
lean_ctor_set(x_193, 2, x_177);
lean_ctor_set(x_193, 3, x_178);
lean_ctor_set(x_193, 4, x_179);
lean_ctor_set(x_193, 5, x_180);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_175);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_195 = lean_ctor_get(x_62, 0);
lean_inc(x_195);
lean_dec(x_62);
x_196 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_20);
lean_ctor_set(x_196, 2, x_21);
lean_ctor_set(x_3, 0, x_196);
x_197 = l_Lean_Expr_Inhabited;
x_198 = lean_unsigned_to_nat(1u);
x_199 = lean_array_get(x_197, x_19, x_198);
lean_dec(x_19);
x_200 = lean_apply_3(x_2, x_199, x_3, x_63);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_202, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_200, 0);
lean_inc(x_204);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_205 = x_200;
} else {
 lean_dec_ref(x_200);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_201, 1);
lean_inc(x_206);
x_207 = lean_ctor_get(x_201, 2);
lean_inc(x_207);
x_208 = lean_ctor_get(x_201, 3);
lean_inc(x_208);
x_209 = lean_ctor_get(x_201, 4);
lean_inc(x_209);
x_210 = lean_ctor_get(x_201, 5);
lean_inc(x_210);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 lean_ctor_release(x_201, 2);
 lean_ctor_release(x_201, 3);
 lean_ctor_release(x_201, 4);
 lean_ctor_release(x_201, 5);
 x_211 = x_201;
} else {
 lean_dec_ref(x_201);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_202, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_202, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_202, 3);
lean_inc(x_214);
x_215 = lean_ctor_get(x_202, 4);
lean_inc(x_215);
x_216 = lean_ctor_get(x_202, 5);
lean_inc(x_216);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 lean_ctor_release(x_202, 2);
 lean_ctor_release(x_202, 3);
 lean_ctor_release(x_202, 4);
 lean_ctor_release(x_202, 5);
 x_217 = x_202;
} else {
 lean_dec_ref(x_202);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_203, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_203, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 lean_ctor_release(x_203, 2);
 x_220 = x_203;
} else {
 lean_dec_ref(x_203);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 3, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
lean_ctor_set(x_221, 2, x_60);
if (lean_is_scalar(x_217)) {
 x_222 = lean_alloc_ctor(0, 6, 0);
} else {
 x_222 = x_217;
}
lean_ctor_set(x_222, 0, x_212);
lean_ctor_set(x_222, 1, x_213);
lean_ctor_set(x_222, 2, x_221);
lean_ctor_set(x_222, 3, x_214);
lean_ctor_set(x_222, 4, x_215);
lean_ctor_set(x_222, 5, x_216);
if (lean_is_scalar(x_211)) {
 x_223 = lean_alloc_ctor(0, 6, 0);
} else {
 x_223 = x_211;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_206);
lean_ctor_set(x_223, 2, x_207);
lean_ctor_set(x_223, 3, x_208);
lean_ctor_set(x_223, 4, x_209);
lean_ctor_set(x_223, 5, x_210);
if (lean_is_scalar(x_205)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_205;
}
lean_ctor_set(x_224, 0, x_204);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_225 = lean_ctor_get(x_200, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_226, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_200, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_229 = x_200;
} else {
 lean_dec_ref(x_200);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_225, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_225, 2);
lean_inc(x_231);
x_232 = lean_ctor_get(x_225, 3);
lean_inc(x_232);
x_233 = lean_ctor_get(x_225, 4);
lean_inc(x_233);
x_234 = lean_ctor_get(x_225, 5);
lean_inc(x_234);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 lean_ctor_release(x_225, 2);
 lean_ctor_release(x_225, 3);
 lean_ctor_release(x_225, 4);
 lean_ctor_release(x_225, 5);
 x_235 = x_225;
} else {
 lean_dec_ref(x_225);
 x_235 = lean_box(0);
}
x_236 = lean_ctor_get(x_226, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_226, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_226, 3);
lean_inc(x_238);
x_239 = lean_ctor_get(x_226, 4);
lean_inc(x_239);
x_240 = lean_ctor_get(x_226, 5);
lean_inc(x_240);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 lean_ctor_release(x_226, 2);
 lean_ctor_release(x_226, 3);
 lean_ctor_release(x_226, 4);
 lean_ctor_release(x_226, 5);
 x_241 = x_226;
} else {
 lean_dec_ref(x_226);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_227, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_227, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 lean_ctor_release(x_227, 2);
 x_244 = x_227;
} else {
 lean_dec_ref(x_227);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(0, 3, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
lean_ctor_set(x_245, 2, x_60);
if (lean_is_scalar(x_241)) {
 x_246 = lean_alloc_ctor(0, 6, 0);
} else {
 x_246 = x_241;
}
lean_ctor_set(x_246, 0, x_236);
lean_ctor_set(x_246, 1, x_237);
lean_ctor_set(x_246, 2, x_245);
lean_ctor_set(x_246, 3, x_238);
lean_ctor_set(x_246, 4, x_239);
lean_ctor_set(x_246, 5, x_240);
if (lean_is_scalar(x_235)) {
 x_247 = lean_alloc_ctor(0, 6, 0);
} else {
 x_247 = x_235;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_230);
lean_ctor_set(x_247, 2, x_231);
lean_ctor_set(x_247, 3, x_232);
lean_ctor_set(x_247, 4, x_233);
lean_ctor_set(x_247, 5, x_234);
if (lean_is_scalar(x_229)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_229;
}
lean_ctor_set(x_248, 0, x_228);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_249 = lean_ctor_get(x_3, 1);
x_250 = lean_ctor_get(x_3, 2);
x_251 = lean_ctor_get(x_3, 3);
x_252 = lean_ctor_get(x_3, 4);
x_253 = lean_ctor_get(x_3, 5);
x_254 = lean_ctor_get(x_3, 6);
x_255 = lean_ctor_get(x_3, 7);
x_256 = lean_ctor_get(x_3, 8);
x_257 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_3);
x_258 = lean_ctor_get(x_62, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 x_259 = x_62;
} else {
 lean_dec_ref(x_62);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(0, 3, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_20);
lean_ctor_set(x_260, 2, x_21);
x_261 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_249);
lean_ctor_set(x_261, 2, x_250);
lean_ctor_set(x_261, 3, x_251);
lean_ctor_set(x_261, 4, x_252);
lean_ctor_set(x_261, 5, x_253);
lean_ctor_set(x_261, 6, x_254);
lean_ctor_set(x_261, 7, x_255);
lean_ctor_set(x_261, 8, x_256);
lean_ctor_set_uint8(x_261, sizeof(void*)*9, x_257);
x_262 = l_Lean_Expr_Inhabited;
x_263 = lean_unsigned_to_nat(1u);
x_264 = lean_array_get(x_262, x_19, x_263);
lean_dec(x_19);
x_265 = lean_apply_3(x_2, x_264, x_261, x_63);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_267, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_265, 0);
lean_inc(x_269);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_270 = x_265;
} else {
 lean_dec_ref(x_265);
 x_270 = lean_box(0);
}
x_271 = lean_ctor_get(x_266, 1);
lean_inc(x_271);
x_272 = lean_ctor_get(x_266, 2);
lean_inc(x_272);
x_273 = lean_ctor_get(x_266, 3);
lean_inc(x_273);
x_274 = lean_ctor_get(x_266, 4);
lean_inc(x_274);
x_275 = lean_ctor_get(x_266, 5);
lean_inc(x_275);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 lean_ctor_release(x_266, 2);
 lean_ctor_release(x_266, 3);
 lean_ctor_release(x_266, 4);
 lean_ctor_release(x_266, 5);
 x_276 = x_266;
} else {
 lean_dec_ref(x_266);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_267, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_267, 1);
lean_inc(x_278);
x_279 = lean_ctor_get(x_267, 3);
lean_inc(x_279);
x_280 = lean_ctor_get(x_267, 4);
lean_inc(x_280);
x_281 = lean_ctor_get(x_267, 5);
lean_inc(x_281);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 lean_ctor_release(x_267, 2);
 lean_ctor_release(x_267, 3);
 lean_ctor_release(x_267, 4);
 lean_ctor_release(x_267, 5);
 x_282 = x_267;
} else {
 lean_dec_ref(x_267);
 x_282 = lean_box(0);
}
x_283 = lean_ctor_get(x_268, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_268, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 lean_ctor_release(x_268, 2);
 x_285 = x_268;
} else {
 lean_dec_ref(x_268);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(0, 3, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_284);
lean_ctor_set(x_286, 2, x_60);
if (lean_is_scalar(x_282)) {
 x_287 = lean_alloc_ctor(0, 6, 0);
} else {
 x_287 = x_282;
}
lean_ctor_set(x_287, 0, x_277);
lean_ctor_set(x_287, 1, x_278);
lean_ctor_set(x_287, 2, x_286);
lean_ctor_set(x_287, 3, x_279);
lean_ctor_set(x_287, 4, x_280);
lean_ctor_set(x_287, 5, x_281);
if (lean_is_scalar(x_276)) {
 x_288 = lean_alloc_ctor(0, 6, 0);
} else {
 x_288 = x_276;
}
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_271);
lean_ctor_set(x_288, 2, x_272);
lean_ctor_set(x_288, 3, x_273);
lean_ctor_set(x_288, 4, x_274);
lean_ctor_set(x_288, 5, x_275);
if (lean_is_scalar(x_270)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_270;
}
lean_ctor_set(x_289, 0, x_269);
lean_ctor_set(x_289, 1, x_288);
return x_289;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_290 = lean_ctor_get(x_265, 1);
lean_inc(x_290);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_291, 2);
lean_inc(x_292);
x_293 = lean_ctor_get(x_265, 0);
lean_inc(x_293);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_294 = x_265;
} else {
 lean_dec_ref(x_265);
 x_294 = lean_box(0);
}
x_295 = lean_ctor_get(x_290, 1);
lean_inc(x_295);
x_296 = lean_ctor_get(x_290, 2);
lean_inc(x_296);
x_297 = lean_ctor_get(x_290, 3);
lean_inc(x_297);
x_298 = lean_ctor_get(x_290, 4);
lean_inc(x_298);
x_299 = lean_ctor_get(x_290, 5);
lean_inc(x_299);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 lean_ctor_release(x_290, 2);
 lean_ctor_release(x_290, 3);
 lean_ctor_release(x_290, 4);
 lean_ctor_release(x_290, 5);
 x_300 = x_290;
} else {
 lean_dec_ref(x_290);
 x_300 = lean_box(0);
}
x_301 = lean_ctor_get(x_291, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_291, 1);
lean_inc(x_302);
x_303 = lean_ctor_get(x_291, 3);
lean_inc(x_303);
x_304 = lean_ctor_get(x_291, 4);
lean_inc(x_304);
x_305 = lean_ctor_get(x_291, 5);
lean_inc(x_305);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 lean_ctor_release(x_291, 2);
 lean_ctor_release(x_291, 3);
 lean_ctor_release(x_291, 4);
 lean_ctor_release(x_291, 5);
 x_306 = x_291;
} else {
 lean_dec_ref(x_291);
 x_306 = lean_box(0);
}
x_307 = lean_ctor_get(x_292, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_292, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 lean_ctor_release(x_292, 2);
 x_309 = x_292;
} else {
 lean_dec_ref(x_292);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(0, 3, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_308);
lean_ctor_set(x_310, 2, x_60);
if (lean_is_scalar(x_306)) {
 x_311 = lean_alloc_ctor(0, 6, 0);
} else {
 x_311 = x_306;
}
lean_ctor_set(x_311, 0, x_301);
lean_ctor_set(x_311, 1, x_302);
lean_ctor_set(x_311, 2, x_310);
lean_ctor_set(x_311, 3, x_303);
lean_ctor_set(x_311, 4, x_304);
lean_ctor_set(x_311, 5, x_305);
if (lean_is_scalar(x_300)) {
 x_312 = lean_alloc_ctor(0, 6, 0);
} else {
 x_312 = x_300;
}
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_295);
lean_ctor_set(x_312, 2, x_296);
lean_ctor_set(x_312, 3, x_297);
lean_ctor_set(x_312, 4, x_298);
lean_ctor_set(x_312, 5, x_299);
if (lean_is_scalar(x_294)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_294;
}
lean_ctor_set(x_313, 0, x_293);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
}
else
{
uint8_t x_314; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_314 = !lean_is_exclusive(x_15);
if (x_314 == 0)
{
return x_15;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_15, 0);
x_316 = lean_ctor_get(x_15, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_15);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabBinder(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinder___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Elab_Term_getLCtx(x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_stxInh;
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_array_get(x_9, x_5, x_10);
x_12 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_array_get(x_9, x_5, x_13);
x_15 = l_Lean_Elab_Term_getLocalInsts(x_3, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Array_empty___closed__1;
lean_inc(x_3);
lean_inc(x_16);
x_20 = l___private_Init_Lean_Elab_Term_11__elabBindersAux___main(x_12, x_18, x_19, x_7, x_16, x_3, x_17);
lean_dec(x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_array_get_size(x_16);
lean_dec(x_16);
x_28 = lean_array_get_size(x_26);
x_29 = lean_nat_dec_lt(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_3, 0);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 2);
lean_dec(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_dec(x_34);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 1, x_25);
lean_inc(x_3);
x_35 = l_Lean_Elab_Term_elabType(x_14, x_3, x_23);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Term_mkForall(x_1, x_24, x_36, x_3, x_37);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_3);
lean_dec(x_24);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 0);
lean_inc(x_43);
lean_dec(x_31);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_25);
lean_ctor_set(x_44, 2, x_26);
lean_ctor_set(x_3, 0, x_44);
lean_inc(x_3);
x_45 = l_Lean_Elab_Term_elabType(x_14, x_3, x_23);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Elab_Term_mkForall(x_1, x_24, x_46, x_3, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
lean_dec(x_24);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_51 = x_45;
} else {
 lean_dec_ref(x_45);
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
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_53 = lean_ctor_get(x_3, 0);
x_54 = lean_ctor_get(x_3, 1);
x_55 = lean_ctor_get(x_3, 2);
x_56 = lean_ctor_get(x_3, 3);
x_57 = lean_ctor_get(x_3, 4);
x_58 = lean_ctor_get(x_3, 5);
x_59 = lean_ctor_get(x_3, 6);
x_60 = lean_ctor_get(x_3, 7);
x_61 = lean_ctor_get(x_3, 8);
x_62 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_3);
x_63 = lean_ctor_get(x_53, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 x_64 = x_53;
} else {
 lean_dec_ref(x_53);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 3, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_25);
lean_ctor_set(x_65, 2, x_26);
x_66 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_54);
lean_ctor_set(x_66, 2, x_55);
lean_ctor_set(x_66, 3, x_56);
lean_ctor_set(x_66, 4, x_57);
lean_ctor_set(x_66, 5, x_58);
lean_ctor_set(x_66, 6, x_59);
lean_ctor_set(x_66, 7, x_60);
lean_ctor_set(x_66, 8, x_61);
lean_ctor_set_uint8(x_66, sizeof(void*)*9, x_62);
lean_inc(x_66);
x_67 = l_Lean_Elab_Term_elabType(x_14, x_66, x_23);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Elab_Term_mkForall(x_1, x_24, x_68, x_66, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_66);
lean_dec(x_24);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_73 = x_67;
} else {
 lean_dec_ref(x_67);
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
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_75 = lean_ctor_get(x_23, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 2);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_ctor_get(x_76, 2);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_23);
x_79 = lean_ctor_get(x_3, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = !lean_is_exclusive(x_3);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_3, 0);
lean_dec(x_82);
x_83 = !lean_is_exclusive(x_79);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_79, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_79, 1);
lean_dec(x_85);
lean_ctor_set(x_79, 2, x_26);
lean_ctor_set(x_79, 1, x_25);
lean_inc(x_3);
x_86 = l_Lean_Elab_Term_elabType(x_14, x_3, x_80);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Elab_Term_mkForall(x_1, x_24, x_87, x_3, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 2);
lean_inc(x_92);
x_93 = !lean_is_exclusive(x_89);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_89, 1);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_90);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_90, 0);
lean_dec(x_96);
x_97 = !lean_is_exclusive(x_91);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_91, 2);
lean_dec(x_98);
x_99 = !lean_is_exclusive(x_92);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_92, 2);
lean_dec(x_100);
lean_ctor_set(x_92, 2, x_77);
return x_89;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_92, 0);
x_102 = lean_ctor_get(x_92, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_92);
x_103 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_77);
lean_ctor_set(x_91, 2, x_103);
return x_89;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_104 = lean_ctor_get(x_91, 0);
x_105 = lean_ctor_get(x_91, 1);
x_106 = lean_ctor_get(x_91, 3);
x_107 = lean_ctor_get(x_91, 4);
x_108 = lean_ctor_get(x_91, 5);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_91);
x_109 = lean_ctor_get(x_92, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_92, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 x_111 = x_92;
} else {
 lean_dec_ref(x_92);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 3, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
lean_ctor_set(x_112, 2, x_77);
x_113 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_113, 0, x_104);
lean_ctor_set(x_113, 1, x_105);
lean_ctor_set(x_113, 2, x_112);
lean_ctor_set(x_113, 3, x_106);
lean_ctor_set(x_113, 4, x_107);
lean_ctor_set(x_113, 5, x_108);
lean_ctor_set(x_90, 0, x_113);
return x_89;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_114 = lean_ctor_get(x_90, 1);
x_115 = lean_ctor_get(x_90, 2);
x_116 = lean_ctor_get(x_90, 3);
x_117 = lean_ctor_get(x_90, 4);
x_118 = lean_ctor_get(x_90, 5);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_90);
x_119 = lean_ctor_get(x_91, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_91, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_91, 3);
lean_inc(x_121);
x_122 = lean_ctor_get(x_91, 4);
lean_inc(x_122);
x_123 = lean_ctor_get(x_91, 5);
lean_inc(x_123);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 lean_ctor_release(x_91, 3);
 lean_ctor_release(x_91, 4);
 lean_ctor_release(x_91, 5);
 x_124 = x_91;
} else {
 lean_dec_ref(x_91);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_92, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_92, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 x_127 = x_92;
} else {
 lean_dec_ref(x_92);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 3, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
lean_ctor_set(x_128, 2, x_77);
if (lean_is_scalar(x_124)) {
 x_129 = lean_alloc_ctor(0, 6, 0);
} else {
 x_129 = x_124;
}
lean_ctor_set(x_129, 0, x_119);
lean_ctor_set(x_129, 1, x_120);
lean_ctor_set(x_129, 2, x_128);
lean_ctor_set(x_129, 3, x_121);
lean_ctor_set(x_129, 4, x_122);
lean_ctor_set(x_129, 5, x_123);
x_130 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_114);
lean_ctor_set(x_130, 2, x_115);
lean_ctor_set(x_130, 3, x_116);
lean_ctor_set(x_130, 4, x_117);
lean_ctor_set(x_130, 5, x_118);
lean_ctor_set(x_89, 1, x_130);
return x_89;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_131 = lean_ctor_get(x_89, 0);
lean_inc(x_131);
lean_dec(x_89);
x_132 = lean_ctor_get(x_90, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_90, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_90, 3);
lean_inc(x_134);
x_135 = lean_ctor_get(x_90, 4);
lean_inc(x_135);
x_136 = lean_ctor_get(x_90, 5);
lean_inc(x_136);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 lean_ctor_release(x_90, 3);
 lean_ctor_release(x_90, 4);
 lean_ctor_release(x_90, 5);
 x_137 = x_90;
} else {
 lean_dec_ref(x_90);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_91, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_91, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_91, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_91, 4);
lean_inc(x_141);
x_142 = lean_ctor_get(x_91, 5);
lean_inc(x_142);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 lean_ctor_release(x_91, 3);
 lean_ctor_release(x_91, 4);
 lean_ctor_release(x_91, 5);
 x_143 = x_91;
} else {
 lean_dec_ref(x_91);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_92, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_92, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 x_146 = x_92;
} else {
 lean_dec_ref(x_92);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 3, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
lean_ctor_set(x_147, 2, x_77);
if (lean_is_scalar(x_143)) {
 x_148 = lean_alloc_ctor(0, 6, 0);
} else {
 x_148 = x_143;
}
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_139);
lean_ctor_set(x_148, 2, x_147);
lean_ctor_set(x_148, 3, x_140);
lean_ctor_set(x_148, 4, x_141);
lean_ctor_set(x_148, 5, x_142);
if (lean_is_scalar(x_137)) {
 x_149 = lean_alloc_ctor(0, 6, 0);
} else {
 x_149 = x_137;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_132);
lean_ctor_set(x_149, 2, x_133);
lean_ctor_set(x_149, 3, x_134);
lean_ctor_set(x_149, 4, x_135);
lean_ctor_set(x_149, 5, x_136);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_131);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_151 = lean_ctor_get(x_89, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_152, 2);
lean_inc(x_153);
x_154 = !lean_is_exclusive(x_89);
if (x_154 == 0)
{
lean_object* x_155; uint8_t x_156; 
x_155 = lean_ctor_get(x_89, 1);
lean_dec(x_155);
x_156 = !lean_is_exclusive(x_151);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_ctor_get(x_151, 0);
lean_dec(x_157);
x_158 = !lean_is_exclusive(x_152);
if (x_158 == 0)
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_ctor_get(x_152, 2);
lean_dec(x_159);
x_160 = !lean_is_exclusive(x_153);
if (x_160 == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_153, 2);
lean_dec(x_161);
lean_ctor_set(x_153, 2, x_77);
return x_89;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_153, 0);
x_163 = lean_ctor_get(x_153, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_153);
x_164 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_164, 2, x_77);
lean_ctor_set(x_152, 2, x_164);
return x_89;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_165 = lean_ctor_get(x_152, 0);
x_166 = lean_ctor_get(x_152, 1);
x_167 = lean_ctor_get(x_152, 3);
x_168 = lean_ctor_get(x_152, 4);
x_169 = lean_ctor_get(x_152, 5);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_152);
x_170 = lean_ctor_get(x_153, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_153, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 lean_ctor_release(x_153, 2);
 x_172 = x_153;
} else {
 lean_dec_ref(x_153);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 3, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
lean_ctor_set(x_173, 2, x_77);
x_174 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_174, 0, x_165);
lean_ctor_set(x_174, 1, x_166);
lean_ctor_set(x_174, 2, x_173);
lean_ctor_set(x_174, 3, x_167);
lean_ctor_set(x_174, 4, x_168);
lean_ctor_set(x_174, 5, x_169);
lean_ctor_set(x_151, 0, x_174);
return x_89;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_175 = lean_ctor_get(x_151, 1);
x_176 = lean_ctor_get(x_151, 2);
x_177 = lean_ctor_get(x_151, 3);
x_178 = lean_ctor_get(x_151, 4);
x_179 = lean_ctor_get(x_151, 5);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_151);
x_180 = lean_ctor_get(x_152, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_152, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_152, 3);
lean_inc(x_182);
x_183 = lean_ctor_get(x_152, 4);
lean_inc(x_183);
x_184 = lean_ctor_get(x_152, 5);
lean_inc(x_184);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 lean_ctor_release(x_152, 2);
 lean_ctor_release(x_152, 3);
 lean_ctor_release(x_152, 4);
 lean_ctor_release(x_152, 5);
 x_185 = x_152;
} else {
 lean_dec_ref(x_152);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_153, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_153, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 lean_ctor_release(x_153, 2);
 x_188 = x_153;
} else {
 lean_dec_ref(x_153);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(0, 3, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
lean_ctor_set(x_189, 2, x_77);
if (lean_is_scalar(x_185)) {
 x_190 = lean_alloc_ctor(0, 6, 0);
} else {
 x_190 = x_185;
}
lean_ctor_set(x_190, 0, x_180);
lean_ctor_set(x_190, 1, x_181);
lean_ctor_set(x_190, 2, x_189);
lean_ctor_set(x_190, 3, x_182);
lean_ctor_set(x_190, 4, x_183);
lean_ctor_set(x_190, 5, x_184);
x_191 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_175);
lean_ctor_set(x_191, 2, x_176);
lean_ctor_set(x_191, 3, x_177);
lean_ctor_set(x_191, 4, x_178);
lean_ctor_set(x_191, 5, x_179);
lean_ctor_set(x_89, 1, x_191);
return x_89;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_192 = lean_ctor_get(x_89, 0);
lean_inc(x_192);
lean_dec(x_89);
x_193 = lean_ctor_get(x_151, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_151, 2);
lean_inc(x_194);
x_195 = lean_ctor_get(x_151, 3);
lean_inc(x_195);
x_196 = lean_ctor_get(x_151, 4);
lean_inc(x_196);
x_197 = lean_ctor_get(x_151, 5);
lean_inc(x_197);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 lean_ctor_release(x_151, 2);
 lean_ctor_release(x_151, 3);
 lean_ctor_release(x_151, 4);
 lean_ctor_release(x_151, 5);
 x_198 = x_151;
} else {
 lean_dec_ref(x_151);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get(x_152, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_152, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_152, 3);
lean_inc(x_201);
x_202 = lean_ctor_get(x_152, 4);
lean_inc(x_202);
x_203 = lean_ctor_get(x_152, 5);
lean_inc(x_203);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 lean_ctor_release(x_152, 2);
 lean_ctor_release(x_152, 3);
 lean_ctor_release(x_152, 4);
 lean_ctor_release(x_152, 5);
 x_204 = x_152;
} else {
 lean_dec_ref(x_152);
 x_204 = lean_box(0);
}
x_205 = lean_ctor_get(x_153, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_153, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 lean_ctor_release(x_153, 2);
 x_207 = x_153;
} else {
 lean_dec_ref(x_153);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(0, 3, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
lean_ctor_set(x_208, 2, x_77);
if (lean_is_scalar(x_204)) {
 x_209 = lean_alloc_ctor(0, 6, 0);
} else {
 x_209 = x_204;
}
lean_ctor_set(x_209, 0, x_199);
lean_ctor_set(x_209, 1, x_200);
lean_ctor_set(x_209, 2, x_208);
lean_ctor_set(x_209, 3, x_201);
lean_ctor_set(x_209, 4, x_202);
lean_ctor_set(x_209, 5, x_203);
if (lean_is_scalar(x_198)) {
 x_210 = lean_alloc_ctor(0, 6, 0);
} else {
 x_210 = x_198;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_193);
lean_ctor_set(x_210, 2, x_194);
lean_ctor_set(x_210, 3, x_195);
lean_ctor_set(x_210, 4, x_196);
lean_ctor_set(x_210, 5, x_197);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_192);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
lean_dec(x_3);
lean_dec(x_24);
x_212 = lean_ctor_get(x_86, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_213, 2);
lean_inc(x_214);
x_215 = !lean_is_exclusive(x_86);
if (x_215 == 0)
{
lean_object* x_216; uint8_t x_217; 
x_216 = lean_ctor_get(x_86, 1);
lean_dec(x_216);
x_217 = !lean_is_exclusive(x_212);
if (x_217 == 0)
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_ctor_get(x_212, 0);
lean_dec(x_218);
x_219 = !lean_is_exclusive(x_213);
if (x_219 == 0)
{
lean_object* x_220; uint8_t x_221; 
x_220 = lean_ctor_get(x_213, 2);
lean_dec(x_220);
x_221 = !lean_is_exclusive(x_214);
if (x_221 == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_214, 2);
lean_dec(x_222);
lean_ctor_set(x_214, 2, x_77);
return x_86;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_214, 0);
x_224 = lean_ctor_get(x_214, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_214);
x_225 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set(x_225, 2, x_77);
lean_ctor_set(x_213, 2, x_225);
return x_86;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_226 = lean_ctor_get(x_213, 0);
x_227 = lean_ctor_get(x_213, 1);
x_228 = lean_ctor_get(x_213, 3);
x_229 = lean_ctor_get(x_213, 4);
x_230 = lean_ctor_get(x_213, 5);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_213);
x_231 = lean_ctor_get(x_214, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_214, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 x_233 = x_214;
} else {
 lean_dec_ref(x_214);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(0, 3, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
lean_ctor_set(x_234, 2, x_77);
x_235 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_235, 0, x_226);
lean_ctor_set(x_235, 1, x_227);
lean_ctor_set(x_235, 2, x_234);
lean_ctor_set(x_235, 3, x_228);
lean_ctor_set(x_235, 4, x_229);
lean_ctor_set(x_235, 5, x_230);
lean_ctor_set(x_212, 0, x_235);
return x_86;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_236 = lean_ctor_get(x_212, 1);
x_237 = lean_ctor_get(x_212, 2);
x_238 = lean_ctor_get(x_212, 3);
x_239 = lean_ctor_get(x_212, 4);
x_240 = lean_ctor_get(x_212, 5);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_212);
x_241 = lean_ctor_get(x_213, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_213, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_213, 3);
lean_inc(x_243);
x_244 = lean_ctor_get(x_213, 4);
lean_inc(x_244);
x_245 = lean_ctor_get(x_213, 5);
lean_inc(x_245);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 lean_ctor_release(x_213, 4);
 lean_ctor_release(x_213, 5);
 x_246 = x_213;
} else {
 lean_dec_ref(x_213);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_214, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_214, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 x_249 = x_214;
} else {
 lean_dec_ref(x_214);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(0, 3, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
lean_ctor_set(x_250, 2, x_77);
if (lean_is_scalar(x_246)) {
 x_251 = lean_alloc_ctor(0, 6, 0);
} else {
 x_251 = x_246;
}
lean_ctor_set(x_251, 0, x_241);
lean_ctor_set(x_251, 1, x_242);
lean_ctor_set(x_251, 2, x_250);
lean_ctor_set(x_251, 3, x_243);
lean_ctor_set(x_251, 4, x_244);
lean_ctor_set(x_251, 5, x_245);
x_252 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_236);
lean_ctor_set(x_252, 2, x_237);
lean_ctor_set(x_252, 3, x_238);
lean_ctor_set(x_252, 4, x_239);
lean_ctor_set(x_252, 5, x_240);
lean_ctor_set(x_86, 1, x_252);
return x_86;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_253 = lean_ctor_get(x_86, 0);
lean_inc(x_253);
lean_dec(x_86);
x_254 = lean_ctor_get(x_212, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_212, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_212, 3);
lean_inc(x_256);
x_257 = lean_ctor_get(x_212, 4);
lean_inc(x_257);
x_258 = lean_ctor_get(x_212, 5);
lean_inc(x_258);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 lean_ctor_release(x_212, 2);
 lean_ctor_release(x_212, 3);
 lean_ctor_release(x_212, 4);
 lean_ctor_release(x_212, 5);
 x_259 = x_212;
} else {
 lean_dec_ref(x_212);
 x_259 = lean_box(0);
}
x_260 = lean_ctor_get(x_213, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_213, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_213, 3);
lean_inc(x_262);
x_263 = lean_ctor_get(x_213, 4);
lean_inc(x_263);
x_264 = lean_ctor_get(x_213, 5);
lean_inc(x_264);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 lean_ctor_release(x_213, 4);
 lean_ctor_release(x_213, 5);
 x_265 = x_213;
} else {
 lean_dec_ref(x_213);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get(x_214, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_214, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 x_268 = x_214;
} else {
 lean_dec_ref(x_214);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(0, 3, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
lean_ctor_set(x_269, 2, x_77);
if (lean_is_scalar(x_265)) {
 x_270 = lean_alloc_ctor(0, 6, 0);
} else {
 x_270 = x_265;
}
lean_ctor_set(x_270, 0, x_260);
lean_ctor_set(x_270, 1, x_261);
lean_ctor_set(x_270, 2, x_269);
lean_ctor_set(x_270, 3, x_262);
lean_ctor_set(x_270, 4, x_263);
lean_ctor_set(x_270, 5, x_264);
if (lean_is_scalar(x_259)) {
 x_271 = lean_alloc_ctor(0, 6, 0);
} else {
 x_271 = x_259;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_254);
lean_ctor_set(x_271, 2, x_255);
lean_ctor_set(x_271, 3, x_256);
lean_ctor_set(x_271, 4, x_257);
lean_ctor_set(x_271, 5, x_258);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_253);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_79, 0);
lean_inc(x_273);
lean_dec(x_79);
x_274 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_25);
lean_ctor_set(x_274, 2, x_26);
lean_ctor_set(x_3, 0, x_274);
lean_inc(x_3);
x_275 = l_Lean_Elab_Term_elabType(x_14, x_3, x_80);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = l_Lean_Elab_Term_mkForall(x_1, x_24, x_276, x_3, x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_280, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_278, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_283 = x_278;
} else {
 lean_dec_ref(x_278);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_279, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_279, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_279, 3);
lean_inc(x_286);
x_287 = lean_ctor_get(x_279, 4);
lean_inc(x_287);
x_288 = lean_ctor_get(x_279, 5);
lean_inc(x_288);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 lean_ctor_release(x_279, 2);
 lean_ctor_release(x_279, 3);
 lean_ctor_release(x_279, 4);
 lean_ctor_release(x_279, 5);
 x_289 = x_279;
} else {
 lean_dec_ref(x_279);
 x_289 = lean_box(0);
}
x_290 = lean_ctor_get(x_280, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_280, 1);
lean_inc(x_291);
x_292 = lean_ctor_get(x_280, 3);
lean_inc(x_292);
x_293 = lean_ctor_get(x_280, 4);
lean_inc(x_293);
x_294 = lean_ctor_get(x_280, 5);
lean_inc(x_294);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 lean_ctor_release(x_280, 2);
 lean_ctor_release(x_280, 3);
 lean_ctor_release(x_280, 4);
 lean_ctor_release(x_280, 5);
 x_295 = x_280;
} else {
 lean_dec_ref(x_280);
 x_295 = lean_box(0);
}
x_296 = lean_ctor_get(x_281, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_281, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 lean_ctor_release(x_281, 2);
 x_298 = x_281;
} else {
 lean_dec_ref(x_281);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(0, 3, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
lean_ctor_set(x_299, 2, x_77);
if (lean_is_scalar(x_295)) {
 x_300 = lean_alloc_ctor(0, 6, 0);
} else {
 x_300 = x_295;
}
lean_ctor_set(x_300, 0, x_290);
lean_ctor_set(x_300, 1, x_291);
lean_ctor_set(x_300, 2, x_299);
lean_ctor_set(x_300, 3, x_292);
lean_ctor_set(x_300, 4, x_293);
lean_ctor_set(x_300, 5, x_294);
if (lean_is_scalar(x_289)) {
 x_301 = lean_alloc_ctor(0, 6, 0);
} else {
 x_301 = x_289;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_284);
lean_ctor_set(x_301, 2, x_285);
lean_ctor_set(x_301, 3, x_286);
lean_ctor_set(x_301, 4, x_287);
lean_ctor_set(x_301, 5, x_288);
if (lean_is_scalar(x_283)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_283;
}
lean_ctor_set(x_302, 0, x_282);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_303 = lean_ctor_get(x_278, 1);
lean_inc(x_303);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_304, 2);
lean_inc(x_305);
x_306 = lean_ctor_get(x_278, 0);
lean_inc(x_306);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_307 = x_278;
} else {
 lean_dec_ref(x_278);
 x_307 = lean_box(0);
}
x_308 = lean_ctor_get(x_303, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_303, 2);
lean_inc(x_309);
x_310 = lean_ctor_get(x_303, 3);
lean_inc(x_310);
x_311 = lean_ctor_get(x_303, 4);
lean_inc(x_311);
x_312 = lean_ctor_get(x_303, 5);
lean_inc(x_312);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 lean_ctor_release(x_303, 2);
 lean_ctor_release(x_303, 3);
 lean_ctor_release(x_303, 4);
 lean_ctor_release(x_303, 5);
 x_313 = x_303;
} else {
 lean_dec_ref(x_303);
 x_313 = lean_box(0);
}
x_314 = lean_ctor_get(x_304, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_304, 1);
lean_inc(x_315);
x_316 = lean_ctor_get(x_304, 3);
lean_inc(x_316);
x_317 = lean_ctor_get(x_304, 4);
lean_inc(x_317);
x_318 = lean_ctor_get(x_304, 5);
lean_inc(x_318);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 lean_ctor_release(x_304, 2);
 lean_ctor_release(x_304, 3);
 lean_ctor_release(x_304, 4);
 lean_ctor_release(x_304, 5);
 x_319 = x_304;
} else {
 lean_dec_ref(x_304);
 x_319 = lean_box(0);
}
x_320 = lean_ctor_get(x_305, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_305, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 lean_ctor_release(x_305, 2);
 x_322 = x_305;
} else {
 lean_dec_ref(x_305);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(0, 3, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
lean_ctor_set(x_323, 2, x_77);
if (lean_is_scalar(x_319)) {
 x_324 = lean_alloc_ctor(0, 6, 0);
} else {
 x_324 = x_319;
}
lean_ctor_set(x_324, 0, x_314);
lean_ctor_set(x_324, 1, x_315);
lean_ctor_set(x_324, 2, x_323);
lean_ctor_set(x_324, 3, x_316);
lean_ctor_set(x_324, 4, x_317);
lean_ctor_set(x_324, 5, x_318);
if (lean_is_scalar(x_313)) {
 x_325 = lean_alloc_ctor(0, 6, 0);
} else {
 x_325 = x_313;
}
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_308);
lean_ctor_set(x_325, 2, x_309);
lean_ctor_set(x_325, 3, x_310);
lean_ctor_set(x_325, 4, x_311);
lean_ctor_set(x_325, 5, x_312);
if (lean_is_scalar(x_307)) {
 x_326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_326 = x_307;
}
lean_ctor_set(x_326, 0, x_306);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_3);
lean_dec(x_24);
x_327 = lean_ctor_get(x_275, 1);
lean_inc(x_327);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_328, 2);
lean_inc(x_329);
x_330 = lean_ctor_get(x_275, 0);
lean_inc(x_330);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_331 = x_275;
} else {
 lean_dec_ref(x_275);
 x_331 = lean_box(0);
}
x_332 = lean_ctor_get(x_327, 1);
lean_inc(x_332);
x_333 = lean_ctor_get(x_327, 2);
lean_inc(x_333);
x_334 = lean_ctor_get(x_327, 3);
lean_inc(x_334);
x_335 = lean_ctor_get(x_327, 4);
lean_inc(x_335);
x_336 = lean_ctor_get(x_327, 5);
lean_inc(x_336);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 lean_ctor_release(x_327, 2);
 lean_ctor_release(x_327, 3);
 lean_ctor_release(x_327, 4);
 lean_ctor_release(x_327, 5);
 x_337 = x_327;
} else {
 lean_dec_ref(x_327);
 x_337 = lean_box(0);
}
x_338 = lean_ctor_get(x_328, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_328, 1);
lean_inc(x_339);
x_340 = lean_ctor_get(x_328, 3);
lean_inc(x_340);
x_341 = lean_ctor_get(x_328, 4);
lean_inc(x_341);
x_342 = lean_ctor_get(x_328, 5);
lean_inc(x_342);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 lean_ctor_release(x_328, 2);
 lean_ctor_release(x_328, 3);
 lean_ctor_release(x_328, 4);
 lean_ctor_release(x_328, 5);
 x_343 = x_328;
} else {
 lean_dec_ref(x_328);
 x_343 = lean_box(0);
}
x_344 = lean_ctor_get(x_329, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_329, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 lean_ctor_release(x_329, 2);
 x_346 = x_329;
} else {
 lean_dec_ref(x_329);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(0, 3, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_344);
lean_ctor_set(x_347, 1, x_345);
lean_ctor_set(x_347, 2, x_77);
if (lean_is_scalar(x_343)) {
 x_348 = lean_alloc_ctor(0, 6, 0);
} else {
 x_348 = x_343;
}
lean_ctor_set(x_348, 0, x_338);
lean_ctor_set(x_348, 1, x_339);
lean_ctor_set(x_348, 2, x_347);
lean_ctor_set(x_348, 3, x_340);
lean_ctor_set(x_348, 4, x_341);
lean_ctor_set(x_348, 5, x_342);
if (lean_is_scalar(x_337)) {
 x_349 = lean_alloc_ctor(0, 6, 0);
} else {
 x_349 = x_337;
}
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_332);
lean_ctor_set(x_349, 2, x_333);
lean_ctor_set(x_349, 3, x_334);
lean_ctor_set(x_349, 4, x_335);
lean_ctor_set(x_349, 5, x_336);
if (lean_is_scalar(x_331)) {
 x_350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_350 = x_331;
}
lean_ctor_set(x_350, 0, x_330);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_351 = lean_ctor_get(x_3, 1);
x_352 = lean_ctor_get(x_3, 2);
x_353 = lean_ctor_get(x_3, 3);
x_354 = lean_ctor_get(x_3, 4);
x_355 = lean_ctor_get(x_3, 5);
x_356 = lean_ctor_get(x_3, 6);
x_357 = lean_ctor_get(x_3, 7);
x_358 = lean_ctor_get(x_3, 8);
x_359 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_inc(x_355);
lean_inc(x_354);
lean_inc(x_353);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_3);
x_360 = lean_ctor_get(x_79, 0);
lean_inc(x_360);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 x_361 = x_79;
} else {
 lean_dec_ref(x_79);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(0, 3, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_25);
lean_ctor_set(x_362, 2, x_26);
x_363 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_351);
lean_ctor_set(x_363, 2, x_352);
lean_ctor_set(x_363, 3, x_353);
lean_ctor_set(x_363, 4, x_354);
lean_ctor_set(x_363, 5, x_355);
lean_ctor_set(x_363, 6, x_356);
lean_ctor_set(x_363, 7, x_357);
lean_ctor_set(x_363, 8, x_358);
lean_ctor_set_uint8(x_363, sizeof(void*)*9, x_359);
lean_inc(x_363);
x_364 = l_Lean_Elab_Term_elabType(x_14, x_363, x_80);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
x_367 = l_Lean_Elab_Term_mkForall(x_1, x_24, x_365, x_363, x_366);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_368 = lean_ctor_get(x_367, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_369, 2);
lean_inc(x_370);
x_371 = lean_ctor_get(x_367, 0);
lean_inc(x_371);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_372 = x_367;
} else {
 lean_dec_ref(x_367);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_368, 1);
lean_inc(x_373);
x_374 = lean_ctor_get(x_368, 2);
lean_inc(x_374);
x_375 = lean_ctor_get(x_368, 3);
lean_inc(x_375);
x_376 = lean_ctor_get(x_368, 4);
lean_inc(x_376);
x_377 = lean_ctor_get(x_368, 5);
lean_inc(x_377);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 lean_ctor_release(x_368, 2);
 lean_ctor_release(x_368, 3);
 lean_ctor_release(x_368, 4);
 lean_ctor_release(x_368, 5);
 x_378 = x_368;
} else {
 lean_dec_ref(x_368);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_369, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_369, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_369, 3);
lean_inc(x_381);
x_382 = lean_ctor_get(x_369, 4);
lean_inc(x_382);
x_383 = lean_ctor_get(x_369, 5);
lean_inc(x_383);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 lean_ctor_release(x_369, 2);
 lean_ctor_release(x_369, 3);
 lean_ctor_release(x_369, 4);
 lean_ctor_release(x_369, 5);
 x_384 = x_369;
} else {
 lean_dec_ref(x_369);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_370, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_370, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 lean_ctor_release(x_370, 2);
 x_387 = x_370;
} else {
 lean_dec_ref(x_370);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(0, 3, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_386);
lean_ctor_set(x_388, 2, x_77);
if (lean_is_scalar(x_384)) {
 x_389 = lean_alloc_ctor(0, 6, 0);
} else {
 x_389 = x_384;
}
lean_ctor_set(x_389, 0, x_379);
lean_ctor_set(x_389, 1, x_380);
lean_ctor_set(x_389, 2, x_388);
lean_ctor_set(x_389, 3, x_381);
lean_ctor_set(x_389, 4, x_382);
lean_ctor_set(x_389, 5, x_383);
if (lean_is_scalar(x_378)) {
 x_390 = lean_alloc_ctor(0, 6, 0);
} else {
 x_390 = x_378;
}
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_373);
lean_ctor_set(x_390, 2, x_374);
lean_ctor_set(x_390, 3, x_375);
lean_ctor_set(x_390, 4, x_376);
lean_ctor_set(x_390, 5, x_377);
if (lean_is_scalar(x_372)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_372;
}
lean_ctor_set(x_391, 0, x_371);
lean_ctor_set(x_391, 1, x_390);
return x_391;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_392 = lean_ctor_get(x_367, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_393, 2);
lean_inc(x_394);
x_395 = lean_ctor_get(x_367, 0);
lean_inc(x_395);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_396 = x_367;
} else {
 lean_dec_ref(x_367);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_392, 1);
lean_inc(x_397);
x_398 = lean_ctor_get(x_392, 2);
lean_inc(x_398);
x_399 = lean_ctor_get(x_392, 3);
lean_inc(x_399);
x_400 = lean_ctor_get(x_392, 4);
lean_inc(x_400);
x_401 = lean_ctor_get(x_392, 5);
lean_inc(x_401);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 lean_ctor_release(x_392, 2);
 lean_ctor_release(x_392, 3);
 lean_ctor_release(x_392, 4);
 lean_ctor_release(x_392, 5);
 x_402 = x_392;
} else {
 lean_dec_ref(x_392);
 x_402 = lean_box(0);
}
x_403 = lean_ctor_get(x_393, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_393, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_393, 3);
lean_inc(x_405);
x_406 = lean_ctor_get(x_393, 4);
lean_inc(x_406);
x_407 = lean_ctor_get(x_393, 5);
lean_inc(x_407);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 lean_ctor_release(x_393, 2);
 lean_ctor_release(x_393, 3);
 lean_ctor_release(x_393, 4);
 lean_ctor_release(x_393, 5);
 x_408 = x_393;
} else {
 lean_dec_ref(x_393);
 x_408 = lean_box(0);
}
x_409 = lean_ctor_get(x_394, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_394, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 lean_ctor_release(x_394, 2);
 x_411 = x_394;
} else {
 lean_dec_ref(x_394);
 x_411 = lean_box(0);
}
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(0, 3, 0);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_409);
lean_ctor_set(x_412, 1, x_410);
lean_ctor_set(x_412, 2, x_77);
if (lean_is_scalar(x_408)) {
 x_413 = lean_alloc_ctor(0, 6, 0);
} else {
 x_413 = x_408;
}
lean_ctor_set(x_413, 0, x_403);
lean_ctor_set(x_413, 1, x_404);
lean_ctor_set(x_413, 2, x_412);
lean_ctor_set(x_413, 3, x_405);
lean_ctor_set(x_413, 4, x_406);
lean_ctor_set(x_413, 5, x_407);
if (lean_is_scalar(x_402)) {
 x_414 = lean_alloc_ctor(0, 6, 0);
} else {
 x_414 = x_402;
}
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_397);
lean_ctor_set(x_414, 2, x_398);
lean_ctor_set(x_414, 3, x_399);
lean_ctor_set(x_414, 4, x_400);
lean_ctor_set(x_414, 5, x_401);
if (lean_is_scalar(x_396)) {
 x_415 = lean_alloc_ctor(1, 2, 0);
} else {
 x_415 = x_396;
}
lean_ctor_set(x_415, 0, x_395);
lean_ctor_set(x_415, 1, x_414);
return x_415;
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_363);
lean_dec(x_24);
x_416 = lean_ctor_get(x_364, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_417, 2);
lean_inc(x_418);
x_419 = lean_ctor_get(x_364, 0);
lean_inc(x_419);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_420 = x_364;
} else {
 lean_dec_ref(x_364);
 x_420 = lean_box(0);
}
x_421 = lean_ctor_get(x_416, 1);
lean_inc(x_421);
x_422 = lean_ctor_get(x_416, 2);
lean_inc(x_422);
x_423 = lean_ctor_get(x_416, 3);
lean_inc(x_423);
x_424 = lean_ctor_get(x_416, 4);
lean_inc(x_424);
x_425 = lean_ctor_get(x_416, 5);
lean_inc(x_425);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 lean_ctor_release(x_416, 4);
 lean_ctor_release(x_416, 5);
 x_426 = x_416;
} else {
 lean_dec_ref(x_416);
 x_426 = lean_box(0);
}
x_427 = lean_ctor_get(x_417, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_417, 1);
lean_inc(x_428);
x_429 = lean_ctor_get(x_417, 3);
lean_inc(x_429);
x_430 = lean_ctor_get(x_417, 4);
lean_inc(x_430);
x_431 = lean_ctor_get(x_417, 5);
lean_inc(x_431);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 lean_ctor_release(x_417, 4);
 lean_ctor_release(x_417, 5);
 x_432 = x_417;
} else {
 lean_dec_ref(x_417);
 x_432 = lean_box(0);
}
x_433 = lean_ctor_get(x_418, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_418, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 lean_ctor_release(x_418, 2);
 x_435 = x_418;
} else {
 lean_dec_ref(x_418);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(0, 3, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_433);
lean_ctor_set(x_436, 1, x_434);
lean_ctor_set(x_436, 2, x_77);
if (lean_is_scalar(x_432)) {
 x_437 = lean_alloc_ctor(0, 6, 0);
} else {
 x_437 = x_432;
}
lean_ctor_set(x_437, 0, x_427);
lean_ctor_set(x_437, 1, x_428);
lean_ctor_set(x_437, 2, x_436);
lean_ctor_set(x_437, 3, x_429);
lean_ctor_set(x_437, 4, x_430);
lean_ctor_set(x_437, 5, x_431);
if (lean_is_scalar(x_426)) {
 x_438 = lean_alloc_ctor(0, 6, 0);
} else {
 x_438 = x_426;
}
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_421);
lean_ctor_set(x_438, 2, x_422);
lean_ctor_set(x_438, 3, x_423);
lean_ctor_set(x_438, 4, x_424);
lean_ctor_set(x_438, 5, x_425);
if (lean_is_scalar(x_420)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_420;
}
lean_ctor_set(x_439, 0, x_419);
lean_ctor_set(x_439, 1, x_438);
return x_439;
}
}
}
}
else
{
uint8_t x_440; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_3);
x_440 = !lean_is_exclusive(x_20);
if (x_440 == 0)
{
return x_20;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_20, 0);
x_442 = lean_ctor_get(x_20, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_20);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
return x_443;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabForall(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabForall");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabForall___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabForall(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_mkExplicitBinder___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_HasRepr___rarg___closed__1;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkExplicitBinder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkExplicitBinder___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_2 = l_Lean_Elab_Term_mkExplicitBinder___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_mkExplicitBinder___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Option_HasRepr___rarg___closed__3;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkExplicitBinder___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_mkExplicitBinder___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_mkExplicitBinder___closed__5;
x_2 = l_Lean_Elab_Term_mkExplicitBinder___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_mkExplicitBinder(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_3 = l_Lean_mkOptionalNode___closed__1;
x_4 = lean_array_push(x_3, x_1);
x_5 = l_Lean_nullKind;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Lean_Elab_Term_mkExplicitBinder___closed__3;
x_8 = lean_array_push(x_7, x_2);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Elab_Term_mkExplicitBinder___closed__6;
x_11 = lean_array_push(x_10, x_6);
x_12 = lean_array_push(x_11, x_9);
x_13 = l_Lean_Syntax_asNode___closed__1;
x_14 = lean_array_push(x_12, x_13);
x_15 = l_Lean_Elab_Term_mkExplicitBinder___closed__4;
x_16 = lean_array_push(x_14, x_15);
x_17 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrow___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_forall___elambda__1___closed__1;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_List_format___rarg___closed__2;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabArrow___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_2 = l_Lean_Elab_Term_elabArrow___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Lean_mkIdentFrom(x_1, x_6);
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = l_Lean_stxInh;
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get(x_13, x_8, x_14);
x_16 = l_Lean_Elab_Term_mkExplicitBinder(x_9, x_15);
x_17 = l_Lean_mkOptionalNode___closed__1;
x_18 = lean_array_push(x_17, x_16);
x_19 = l_Lean_nullKind;
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_19);
x_20 = l_Lean_Elab_Term_elabArrow___closed__3;
x_21 = lean_array_push(x_20, x_1);
x_22 = l_Lean_Elab_Term_elabArrow___closed__2;
x_23 = lean_array_push(x_21, x_22);
x_24 = lean_unsigned_to_nat(2u);
x_25 = lean_array_get(x_13, x_8, x_24);
lean_dec(x_8);
x_26 = lean_array_push(x_23, x_25);
x_27 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Elab_Term_elabTerm(x_28, x_2, x_3, x_7);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_1);
x_30 = l_Lean_stxInh;
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_array_get(x_30, x_8, x_31);
x_33 = l_Lean_Elab_Term_mkExplicitBinder(x_9, x_32);
x_34 = l_Lean_mkOptionalNode___closed__1;
x_35 = lean_array_push(x_34, x_33);
x_36 = l_Lean_nullKind;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Elab_Term_elabArrow___closed__3;
x_39 = lean_array_push(x_38, x_37);
x_40 = l_Lean_Elab_Term_elabArrow___closed__2;
x_41 = lean_array_push(x_39, x_40);
x_42 = lean_unsigned_to_nat(2u);
x_43 = lean_array_get(x_30, x_8, x_42);
lean_dec(x_8);
x_44 = lean_array_push(x_41, x_43);
x_45 = l_Lean_Parser_Term_forall___elambda__1___closed__2;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_Elab_Term_elabTerm(x_46, x_2, x_3, x_7);
return x_47;
}
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabArrow");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabArrow), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrow(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabDepArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Elab_Term_getLCtx(x_3, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_stxInh;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_5, x_10);
x_12 = l_Lean_mkOptionalNode___closed__1;
x_13 = lean_array_push(x_12, x_11);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_array_get(x_9, x_5, x_14);
x_16 = l_Lean_Elab_Term_getLocalInsts(x_3, x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Array_empty___closed__1;
lean_inc(x_3);
lean_inc(x_17);
x_20 = l___private_Init_Lean_Elab_Term_11__elabBindersAux___main(x_13, x_10, x_19, x_7, x_17, x_3, x_18);
lean_dec(x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_array_get_size(x_17);
lean_dec(x_17);
x_28 = lean_array_get_size(x_26);
x_29 = lean_nat_dec_lt(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_3, 0);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 2);
lean_dec(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_dec(x_34);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 1, x_25);
lean_inc(x_3);
x_35 = l_Lean_Elab_Term_elabType(x_15, x_3, x_23);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Term_mkForall(x_1, x_24, x_36, x_3, x_37);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_3);
lean_dec(x_24);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 0);
lean_inc(x_43);
lean_dec(x_31);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_25);
lean_ctor_set(x_44, 2, x_26);
lean_ctor_set(x_3, 0, x_44);
lean_inc(x_3);
x_45 = l_Lean_Elab_Term_elabType(x_15, x_3, x_23);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Elab_Term_mkForall(x_1, x_24, x_46, x_3, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
lean_dec(x_24);
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_51 = x_45;
} else {
 lean_dec_ref(x_45);
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
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_53 = lean_ctor_get(x_3, 0);
x_54 = lean_ctor_get(x_3, 1);
x_55 = lean_ctor_get(x_3, 2);
x_56 = lean_ctor_get(x_3, 3);
x_57 = lean_ctor_get(x_3, 4);
x_58 = lean_ctor_get(x_3, 5);
x_59 = lean_ctor_get(x_3, 6);
x_60 = lean_ctor_get(x_3, 7);
x_61 = lean_ctor_get(x_3, 8);
x_62 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_3);
x_63 = lean_ctor_get(x_53, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 x_64 = x_53;
} else {
 lean_dec_ref(x_53);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 3, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_25);
lean_ctor_set(x_65, 2, x_26);
x_66 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_54);
lean_ctor_set(x_66, 2, x_55);
lean_ctor_set(x_66, 3, x_56);
lean_ctor_set(x_66, 4, x_57);
lean_ctor_set(x_66, 5, x_58);
lean_ctor_set(x_66, 6, x_59);
lean_ctor_set(x_66, 7, x_60);
lean_ctor_set(x_66, 8, x_61);
lean_ctor_set_uint8(x_66, sizeof(void*)*9, x_62);
lean_inc(x_66);
x_67 = l_Lean_Elab_Term_elabType(x_15, x_66, x_23);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Elab_Term_mkForall(x_1, x_24, x_68, x_66, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_66);
lean_dec(x_24);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_73 = x_67;
} else {
 lean_dec_ref(x_67);
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
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_75 = lean_ctor_get(x_23, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 2);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_ctor_get(x_76, 2);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Lean_Elab_Term_resetSynthInstanceCache___rarg(x_23);
x_79 = lean_ctor_get(x_3, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = !lean_is_exclusive(x_3);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_3, 0);
lean_dec(x_82);
x_83 = !lean_is_exclusive(x_79);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_79, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_79, 1);
lean_dec(x_85);
lean_ctor_set(x_79, 2, x_26);
lean_ctor_set(x_79, 1, x_25);
lean_inc(x_3);
x_86 = l_Lean_Elab_Term_elabType(x_15, x_3, x_80);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Elab_Term_mkForall(x_1, x_24, x_87, x_3, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 2);
lean_inc(x_92);
x_93 = !lean_is_exclusive(x_89);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_89, 1);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_90);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_90, 0);
lean_dec(x_96);
x_97 = !lean_is_exclusive(x_91);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_91, 2);
lean_dec(x_98);
x_99 = !lean_is_exclusive(x_92);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_92, 2);
lean_dec(x_100);
lean_ctor_set(x_92, 2, x_77);
return x_89;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_92, 0);
x_102 = lean_ctor_get(x_92, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_92);
x_103 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_77);
lean_ctor_set(x_91, 2, x_103);
return x_89;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_104 = lean_ctor_get(x_91, 0);
x_105 = lean_ctor_get(x_91, 1);
x_106 = lean_ctor_get(x_91, 3);
x_107 = lean_ctor_get(x_91, 4);
x_108 = lean_ctor_get(x_91, 5);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_91);
x_109 = lean_ctor_get(x_92, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_92, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 x_111 = x_92;
} else {
 lean_dec_ref(x_92);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 3, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
lean_ctor_set(x_112, 2, x_77);
x_113 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_113, 0, x_104);
lean_ctor_set(x_113, 1, x_105);
lean_ctor_set(x_113, 2, x_112);
lean_ctor_set(x_113, 3, x_106);
lean_ctor_set(x_113, 4, x_107);
lean_ctor_set(x_113, 5, x_108);
lean_ctor_set(x_90, 0, x_113);
return x_89;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_114 = lean_ctor_get(x_90, 1);
x_115 = lean_ctor_get(x_90, 2);
x_116 = lean_ctor_get(x_90, 3);
x_117 = lean_ctor_get(x_90, 4);
x_118 = lean_ctor_get(x_90, 5);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_90);
x_119 = lean_ctor_get(x_91, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_91, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_91, 3);
lean_inc(x_121);
x_122 = lean_ctor_get(x_91, 4);
lean_inc(x_122);
x_123 = lean_ctor_get(x_91, 5);
lean_inc(x_123);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 lean_ctor_release(x_91, 3);
 lean_ctor_release(x_91, 4);
 lean_ctor_release(x_91, 5);
 x_124 = x_91;
} else {
 lean_dec_ref(x_91);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_92, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_92, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 x_127 = x_92;
} else {
 lean_dec_ref(x_92);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 3, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
lean_ctor_set(x_128, 2, x_77);
if (lean_is_scalar(x_124)) {
 x_129 = lean_alloc_ctor(0, 6, 0);
} else {
 x_129 = x_124;
}
lean_ctor_set(x_129, 0, x_119);
lean_ctor_set(x_129, 1, x_120);
lean_ctor_set(x_129, 2, x_128);
lean_ctor_set(x_129, 3, x_121);
lean_ctor_set(x_129, 4, x_122);
lean_ctor_set(x_129, 5, x_123);
x_130 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_114);
lean_ctor_set(x_130, 2, x_115);
lean_ctor_set(x_130, 3, x_116);
lean_ctor_set(x_130, 4, x_117);
lean_ctor_set(x_130, 5, x_118);
lean_ctor_set(x_89, 1, x_130);
return x_89;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_131 = lean_ctor_get(x_89, 0);
lean_inc(x_131);
lean_dec(x_89);
x_132 = lean_ctor_get(x_90, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_90, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_90, 3);
lean_inc(x_134);
x_135 = lean_ctor_get(x_90, 4);
lean_inc(x_135);
x_136 = lean_ctor_get(x_90, 5);
lean_inc(x_136);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 lean_ctor_release(x_90, 3);
 lean_ctor_release(x_90, 4);
 lean_ctor_release(x_90, 5);
 x_137 = x_90;
} else {
 lean_dec_ref(x_90);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_91, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_91, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_91, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_91, 4);
lean_inc(x_141);
x_142 = lean_ctor_get(x_91, 5);
lean_inc(x_142);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 lean_ctor_release(x_91, 3);
 lean_ctor_release(x_91, 4);
 lean_ctor_release(x_91, 5);
 x_143 = x_91;
} else {
 lean_dec_ref(x_91);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_92, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_92, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 x_146 = x_92;
} else {
 lean_dec_ref(x_92);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 3, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
lean_ctor_set(x_147, 2, x_77);
if (lean_is_scalar(x_143)) {
 x_148 = lean_alloc_ctor(0, 6, 0);
} else {
 x_148 = x_143;
}
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_139);
lean_ctor_set(x_148, 2, x_147);
lean_ctor_set(x_148, 3, x_140);
lean_ctor_set(x_148, 4, x_141);
lean_ctor_set(x_148, 5, x_142);
if (lean_is_scalar(x_137)) {
 x_149 = lean_alloc_ctor(0, 6, 0);
} else {
 x_149 = x_137;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_132);
lean_ctor_set(x_149, 2, x_133);
lean_ctor_set(x_149, 3, x_134);
lean_ctor_set(x_149, 4, x_135);
lean_ctor_set(x_149, 5, x_136);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_131);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_151 = lean_ctor_get(x_89, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_152, 2);
lean_inc(x_153);
x_154 = !lean_is_exclusive(x_89);
if (x_154 == 0)
{
lean_object* x_155; uint8_t x_156; 
x_155 = lean_ctor_get(x_89, 1);
lean_dec(x_155);
x_156 = !lean_is_exclusive(x_151);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_ctor_get(x_151, 0);
lean_dec(x_157);
x_158 = !lean_is_exclusive(x_152);
if (x_158 == 0)
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_ctor_get(x_152, 2);
lean_dec(x_159);
x_160 = !lean_is_exclusive(x_153);
if (x_160 == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_153, 2);
lean_dec(x_161);
lean_ctor_set(x_153, 2, x_77);
return x_89;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_153, 0);
x_163 = lean_ctor_get(x_153, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_153);
x_164 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_164, 2, x_77);
lean_ctor_set(x_152, 2, x_164);
return x_89;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_165 = lean_ctor_get(x_152, 0);
x_166 = lean_ctor_get(x_152, 1);
x_167 = lean_ctor_get(x_152, 3);
x_168 = lean_ctor_get(x_152, 4);
x_169 = lean_ctor_get(x_152, 5);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_152);
x_170 = lean_ctor_get(x_153, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_153, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 lean_ctor_release(x_153, 2);
 x_172 = x_153;
} else {
 lean_dec_ref(x_153);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 3, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
lean_ctor_set(x_173, 2, x_77);
x_174 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_174, 0, x_165);
lean_ctor_set(x_174, 1, x_166);
lean_ctor_set(x_174, 2, x_173);
lean_ctor_set(x_174, 3, x_167);
lean_ctor_set(x_174, 4, x_168);
lean_ctor_set(x_174, 5, x_169);
lean_ctor_set(x_151, 0, x_174);
return x_89;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_175 = lean_ctor_get(x_151, 1);
x_176 = lean_ctor_get(x_151, 2);
x_177 = lean_ctor_get(x_151, 3);
x_178 = lean_ctor_get(x_151, 4);
x_179 = lean_ctor_get(x_151, 5);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_151);
x_180 = lean_ctor_get(x_152, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_152, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_152, 3);
lean_inc(x_182);
x_183 = lean_ctor_get(x_152, 4);
lean_inc(x_183);
x_184 = lean_ctor_get(x_152, 5);
lean_inc(x_184);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 lean_ctor_release(x_152, 2);
 lean_ctor_release(x_152, 3);
 lean_ctor_release(x_152, 4);
 lean_ctor_release(x_152, 5);
 x_185 = x_152;
} else {
 lean_dec_ref(x_152);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_153, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_153, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 lean_ctor_release(x_153, 2);
 x_188 = x_153;
} else {
 lean_dec_ref(x_153);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(0, 3, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
lean_ctor_set(x_189, 2, x_77);
if (lean_is_scalar(x_185)) {
 x_190 = lean_alloc_ctor(0, 6, 0);
} else {
 x_190 = x_185;
}
lean_ctor_set(x_190, 0, x_180);
lean_ctor_set(x_190, 1, x_181);
lean_ctor_set(x_190, 2, x_189);
lean_ctor_set(x_190, 3, x_182);
lean_ctor_set(x_190, 4, x_183);
lean_ctor_set(x_190, 5, x_184);
x_191 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_175);
lean_ctor_set(x_191, 2, x_176);
lean_ctor_set(x_191, 3, x_177);
lean_ctor_set(x_191, 4, x_178);
lean_ctor_set(x_191, 5, x_179);
lean_ctor_set(x_89, 1, x_191);
return x_89;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_192 = lean_ctor_get(x_89, 0);
lean_inc(x_192);
lean_dec(x_89);
x_193 = lean_ctor_get(x_151, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_151, 2);
lean_inc(x_194);
x_195 = lean_ctor_get(x_151, 3);
lean_inc(x_195);
x_196 = lean_ctor_get(x_151, 4);
lean_inc(x_196);
x_197 = lean_ctor_get(x_151, 5);
lean_inc(x_197);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 lean_ctor_release(x_151, 2);
 lean_ctor_release(x_151, 3);
 lean_ctor_release(x_151, 4);
 lean_ctor_release(x_151, 5);
 x_198 = x_151;
} else {
 lean_dec_ref(x_151);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get(x_152, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_152, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_152, 3);
lean_inc(x_201);
x_202 = lean_ctor_get(x_152, 4);
lean_inc(x_202);
x_203 = lean_ctor_get(x_152, 5);
lean_inc(x_203);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 lean_ctor_release(x_152, 2);
 lean_ctor_release(x_152, 3);
 lean_ctor_release(x_152, 4);
 lean_ctor_release(x_152, 5);
 x_204 = x_152;
} else {
 lean_dec_ref(x_152);
 x_204 = lean_box(0);
}
x_205 = lean_ctor_get(x_153, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_153, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 lean_ctor_release(x_153, 2);
 x_207 = x_153;
} else {
 lean_dec_ref(x_153);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(0, 3, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
lean_ctor_set(x_208, 2, x_77);
if (lean_is_scalar(x_204)) {
 x_209 = lean_alloc_ctor(0, 6, 0);
} else {
 x_209 = x_204;
}
lean_ctor_set(x_209, 0, x_199);
lean_ctor_set(x_209, 1, x_200);
lean_ctor_set(x_209, 2, x_208);
lean_ctor_set(x_209, 3, x_201);
lean_ctor_set(x_209, 4, x_202);
lean_ctor_set(x_209, 5, x_203);
if (lean_is_scalar(x_198)) {
 x_210 = lean_alloc_ctor(0, 6, 0);
} else {
 x_210 = x_198;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_193);
lean_ctor_set(x_210, 2, x_194);
lean_ctor_set(x_210, 3, x_195);
lean_ctor_set(x_210, 4, x_196);
lean_ctor_set(x_210, 5, x_197);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_192);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
lean_dec(x_3);
lean_dec(x_24);
x_212 = lean_ctor_get(x_86, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_213, 2);
lean_inc(x_214);
x_215 = !lean_is_exclusive(x_86);
if (x_215 == 0)
{
lean_object* x_216; uint8_t x_217; 
x_216 = lean_ctor_get(x_86, 1);
lean_dec(x_216);
x_217 = !lean_is_exclusive(x_212);
if (x_217 == 0)
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_ctor_get(x_212, 0);
lean_dec(x_218);
x_219 = !lean_is_exclusive(x_213);
if (x_219 == 0)
{
lean_object* x_220; uint8_t x_221; 
x_220 = lean_ctor_get(x_213, 2);
lean_dec(x_220);
x_221 = !lean_is_exclusive(x_214);
if (x_221 == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_214, 2);
lean_dec(x_222);
lean_ctor_set(x_214, 2, x_77);
return x_86;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_214, 0);
x_224 = lean_ctor_get(x_214, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_214);
x_225 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set(x_225, 2, x_77);
lean_ctor_set(x_213, 2, x_225);
return x_86;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_226 = lean_ctor_get(x_213, 0);
x_227 = lean_ctor_get(x_213, 1);
x_228 = lean_ctor_get(x_213, 3);
x_229 = lean_ctor_get(x_213, 4);
x_230 = lean_ctor_get(x_213, 5);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_213);
x_231 = lean_ctor_get(x_214, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_214, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 x_233 = x_214;
} else {
 lean_dec_ref(x_214);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(0, 3, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
lean_ctor_set(x_234, 2, x_77);
x_235 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_235, 0, x_226);
lean_ctor_set(x_235, 1, x_227);
lean_ctor_set(x_235, 2, x_234);
lean_ctor_set(x_235, 3, x_228);
lean_ctor_set(x_235, 4, x_229);
lean_ctor_set(x_235, 5, x_230);
lean_ctor_set(x_212, 0, x_235);
return x_86;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_236 = lean_ctor_get(x_212, 1);
x_237 = lean_ctor_get(x_212, 2);
x_238 = lean_ctor_get(x_212, 3);
x_239 = lean_ctor_get(x_212, 4);
x_240 = lean_ctor_get(x_212, 5);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_212);
x_241 = lean_ctor_get(x_213, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_213, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_213, 3);
lean_inc(x_243);
x_244 = lean_ctor_get(x_213, 4);
lean_inc(x_244);
x_245 = lean_ctor_get(x_213, 5);
lean_inc(x_245);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 lean_ctor_release(x_213, 4);
 lean_ctor_release(x_213, 5);
 x_246 = x_213;
} else {
 lean_dec_ref(x_213);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_214, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_214, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 x_249 = x_214;
} else {
 lean_dec_ref(x_214);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(0, 3, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
lean_ctor_set(x_250, 2, x_77);
if (lean_is_scalar(x_246)) {
 x_251 = lean_alloc_ctor(0, 6, 0);
} else {
 x_251 = x_246;
}
lean_ctor_set(x_251, 0, x_241);
lean_ctor_set(x_251, 1, x_242);
lean_ctor_set(x_251, 2, x_250);
lean_ctor_set(x_251, 3, x_243);
lean_ctor_set(x_251, 4, x_244);
lean_ctor_set(x_251, 5, x_245);
x_252 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_236);
lean_ctor_set(x_252, 2, x_237);
lean_ctor_set(x_252, 3, x_238);
lean_ctor_set(x_252, 4, x_239);
lean_ctor_set(x_252, 5, x_240);
lean_ctor_set(x_86, 1, x_252);
return x_86;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_253 = lean_ctor_get(x_86, 0);
lean_inc(x_253);
lean_dec(x_86);
x_254 = lean_ctor_get(x_212, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_212, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_212, 3);
lean_inc(x_256);
x_257 = lean_ctor_get(x_212, 4);
lean_inc(x_257);
x_258 = lean_ctor_get(x_212, 5);
lean_inc(x_258);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 lean_ctor_release(x_212, 2);
 lean_ctor_release(x_212, 3);
 lean_ctor_release(x_212, 4);
 lean_ctor_release(x_212, 5);
 x_259 = x_212;
} else {
 lean_dec_ref(x_212);
 x_259 = lean_box(0);
}
x_260 = lean_ctor_get(x_213, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_213, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_213, 3);
lean_inc(x_262);
x_263 = lean_ctor_get(x_213, 4);
lean_inc(x_263);
x_264 = lean_ctor_get(x_213, 5);
lean_inc(x_264);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 lean_ctor_release(x_213, 4);
 lean_ctor_release(x_213, 5);
 x_265 = x_213;
} else {
 lean_dec_ref(x_213);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get(x_214, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_214, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 x_268 = x_214;
} else {
 lean_dec_ref(x_214);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(0, 3, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
lean_ctor_set(x_269, 2, x_77);
if (lean_is_scalar(x_265)) {
 x_270 = lean_alloc_ctor(0, 6, 0);
} else {
 x_270 = x_265;
}
lean_ctor_set(x_270, 0, x_260);
lean_ctor_set(x_270, 1, x_261);
lean_ctor_set(x_270, 2, x_269);
lean_ctor_set(x_270, 3, x_262);
lean_ctor_set(x_270, 4, x_263);
lean_ctor_set(x_270, 5, x_264);
if (lean_is_scalar(x_259)) {
 x_271 = lean_alloc_ctor(0, 6, 0);
} else {
 x_271 = x_259;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_254);
lean_ctor_set(x_271, 2, x_255);
lean_ctor_set(x_271, 3, x_256);
lean_ctor_set(x_271, 4, x_257);
lean_ctor_set(x_271, 5, x_258);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_253);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_79, 0);
lean_inc(x_273);
lean_dec(x_79);
x_274 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_25);
lean_ctor_set(x_274, 2, x_26);
lean_ctor_set(x_3, 0, x_274);
lean_inc(x_3);
x_275 = l_Lean_Elab_Term_elabType(x_15, x_3, x_80);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = l_Lean_Elab_Term_mkForall(x_1, x_24, x_276, x_3, x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_280, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_278, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_283 = x_278;
} else {
 lean_dec_ref(x_278);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_279, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_279, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_279, 3);
lean_inc(x_286);
x_287 = lean_ctor_get(x_279, 4);
lean_inc(x_287);
x_288 = lean_ctor_get(x_279, 5);
lean_inc(x_288);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 lean_ctor_release(x_279, 2);
 lean_ctor_release(x_279, 3);
 lean_ctor_release(x_279, 4);
 lean_ctor_release(x_279, 5);
 x_289 = x_279;
} else {
 lean_dec_ref(x_279);
 x_289 = lean_box(0);
}
x_290 = lean_ctor_get(x_280, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_280, 1);
lean_inc(x_291);
x_292 = lean_ctor_get(x_280, 3);
lean_inc(x_292);
x_293 = lean_ctor_get(x_280, 4);
lean_inc(x_293);
x_294 = lean_ctor_get(x_280, 5);
lean_inc(x_294);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 lean_ctor_release(x_280, 2);
 lean_ctor_release(x_280, 3);
 lean_ctor_release(x_280, 4);
 lean_ctor_release(x_280, 5);
 x_295 = x_280;
} else {
 lean_dec_ref(x_280);
 x_295 = lean_box(0);
}
x_296 = lean_ctor_get(x_281, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_281, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 lean_ctor_release(x_281, 2);
 x_298 = x_281;
} else {
 lean_dec_ref(x_281);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(0, 3, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_297);
lean_ctor_set(x_299, 2, x_77);
if (lean_is_scalar(x_295)) {
 x_300 = lean_alloc_ctor(0, 6, 0);
} else {
 x_300 = x_295;
}
lean_ctor_set(x_300, 0, x_290);
lean_ctor_set(x_300, 1, x_291);
lean_ctor_set(x_300, 2, x_299);
lean_ctor_set(x_300, 3, x_292);
lean_ctor_set(x_300, 4, x_293);
lean_ctor_set(x_300, 5, x_294);
if (lean_is_scalar(x_289)) {
 x_301 = lean_alloc_ctor(0, 6, 0);
} else {
 x_301 = x_289;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_284);
lean_ctor_set(x_301, 2, x_285);
lean_ctor_set(x_301, 3, x_286);
lean_ctor_set(x_301, 4, x_287);
lean_ctor_set(x_301, 5, x_288);
if (lean_is_scalar(x_283)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_283;
}
lean_ctor_set(x_302, 0, x_282);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_303 = lean_ctor_get(x_278, 1);
lean_inc(x_303);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_304, 2);
lean_inc(x_305);
x_306 = lean_ctor_get(x_278, 0);
lean_inc(x_306);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_307 = x_278;
} else {
 lean_dec_ref(x_278);
 x_307 = lean_box(0);
}
x_308 = lean_ctor_get(x_303, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_303, 2);
lean_inc(x_309);
x_310 = lean_ctor_get(x_303, 3);
lean_inc(x_310);
x_311 = lean_ctor_get(x_303, 4);
lean_inc(x_311);
x_312 = lean_ctor_get(x_303, 5);
lean_inc(x_312);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 lean_ctor_release(x_303, 2);
 lean_ctor_release(x_303, 3);
 lean_ctor_release(x_303, 4);
 lean_ctor_release(x_303, 5);
 x_313 = x_303;
} else {
 lean_dec_ref(x_303);
 x_313 = lean_box(0);
}
x_314 = lean_ctor_get(x_304, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_304, 1);
lean_inc(x_315);
x_316 = lean_ctor_get(x_304, 3);
lean_inc(x_316);
x_317 = lean_ctor_get(x_304, 4);
lean_inc(x_317);
x_318 = lean_ctor_get(x_304, 5);
lean_inc(x_318);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 lean_ctor_release(x_304, 2);
 lean_ctor_release(x_304, 3);
 lean_ctor_release(x_304, 4);
 lean_ctor_release(x_304, 5);
 x_319 = x_304;
} else {
 lean_dec_ref(x_304);
 x_319 = lean_box(0);
}
x_320 = lean_ctor_get(x_305, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_305, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 lean_ctor_release(x_305, 2);
 x_322 = x_305;
} else {
 lean_dec_ref(x_305);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(0, 3, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
lean_ctor_set(x_323, 2, x_77);
if (lean_is_scalar(x_319)) {
 x_324 = lean_alloc_ctor(0, 6, 0);
} else {
 x_324 = x_319;
}
lean_ctor_set(x_324, 0, x_314);
lean_ctor_set(x_324, 1, x_315);
lean_ctor_set(x_324, 2, x_323);
lean_ctor_set(x_324, 3, x_316);
lean_ctor_set(x_324, 4, x_317);
lean_ctor_set(x_324, 5, x_318);
if (lean_is_scalar(x_313)) {
 x_325 = lean_alloc_ctor(0, 6, 0);
} else {
 x_325 = x_313;
}
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_308);
lean_ctor_set(x_325, 2, x_309);
lean_ctor_set(x_325, 3, x_310);
lean_ctor_set(x_325, 4, x_311);
lean_ctor_set(x_325, 5, x_312);
if (lean_is_scalar(x_307)) {
 x_326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_326 = x_307;
}
lean_ctor_set(x_326, 0, x_306);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_3);
lean_dec(x_24);
x_327 = lean_ctor_get(x_275, 1);
lean_inc(x_327);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_328, 2);
lean_inc(x_329);
x_330 = lean_ctor_get(x_275, 0);
lean_inc(x_330);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_331 = x_275;
} else {
 lean_dec_ref(x_275);
 x_331 = lean_box(0);
}
x_332 = lean_ctor_get(x_327, 1);
lean_inc(x_332);
x_333 = lean_ctor_get(x_327, 2);
lean_inc(x_333);
x_334 = lean_ctor_get(x_327, 3);
lean_inc(x_334);
x_335 = lean_ctor_get(x_327, 4);
lean_inc(x_335);
x_336 = lean_ctor_get(x_327, 5);
lean_inc(x_336);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 lean_ctor_release(x_327, 2);
 lean_ctor_release(x_327, 3);
 lean_ctor_release(x_327, 4);
 lean_ctor_release(x_327, 5);
 x_337 = x_327;
} else {
 lean_dec_ref(x_327);
 x_337 = lean_box(0);
}
x_338 = lean_ctor_get(x_328, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_328, 1);
lean_inc(x_339);
x_340 = lean_ctor_get(x_328, 3);
lean_inc(x_340);
x_341 = lean_ctor_get(x_328, 4);
lean_inc(x_341);
x_342 = lean_ctor_get(x_328, 5);
lean_inc(x_342);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 lean_ctor_release(x_328, 2);
 lean_ctor_release(x_328, 3);
 lean_ctor_release(x_328, 4);
 lean_ctor_release(x_328, 5);
 x_343 = x_328;
} else {
 lean_dec_ref(x_328);
 x_343 = lean_box(0);
}
x_344 = lean_ctor_get(x_329, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_329, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 lean_ctor_release(x_329, 2);
 x_346 = x_329;
} else {
 lean_dec_ref(x_329);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(0, 3, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_344);
lean_ctor_set(x_347, 1, x_345);
lean_ctor_set(x_347, 2, x_77);
if (lean_is_scalar(x_343)) {
 x_348 = lean_alloc_ctor(0, 6, 0);
} else {
 x_348 = x_343;
}
lean_ctor_set(x_348, 0, x_338);
lean_ctor_set(x_348, 1, x_339);
lean_ctor_set(x_348, 2, x_347);
lean_ctor_set(x_348, 3, x_340);
lean_ctor_set(x_348, 4, x_341);
lean_ctor_set(x_348, 5, x_342);
if (lean_is_scalar(x_337)) {
 x_349 = lean_alloc_ctor(0, 6, 0);
} else {
 x_349 = x_337;
}
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_332);
lean_ctor_set(x_349, 2, x_333);
lean_ctor_set(x_349, 3, x_334);
lean_ctor_set(x_349, 4, x_335);
lean_ctor_set(x_349, 5, x_336);
if (lean_is_scalar(x_331)) {
 x_350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_350 = x_331;
}
lean_ctor_set(x_350, 0, x_330);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_351 = lean_ctor_get(x_3, 1);
x_352 = lean_ctor_get(x_3, 2);
x_353 = lean_ctor_get(x_3, 3);
x_354 = lean_ctor_get(x_3, 4);
x_355 = lean_ctor_get(x_3, 5);
x_356 = lean_ctor_get(x_3, 6);
x_357 = lean_ctor_get(x_3, 7);
x_358 = lean_ctor_get(x_3, 8);
x_359 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_inc(x_355);
lean_inc(x_354);
lean_inc(x_353);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_3);
x_360 = lean_ctor_get(x_79, 0);
lean_inc(x_360);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 x_361 = x_79;
} else {
 lean_dec_ref(x_79);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(0, 3, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_25);
lean_ctor_set(x_362, 2, x_26);
x_363 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_351);
lean_ctor_set(x_363, 2, x_352);
lean_ctor_set(x_363, 3, x_353);
lean_ctor_set(x_363, 4, x_354);
lean_ctor_set(x_363, 5, x_355);
lean_ctor_set(x_363, 6, x_356);
lean_ctor_set(x_363, 7, x_357);
lean_ctor_set(x_363, 8, x_358);
lean_ctor_set_uint8(x_363, sizeof(void*)*9, x_359);
lean_inc(x_363);
x_364 = l_Lean_Elab_Term_elabType(x_15, x_363, x_80);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
x_367 = l_Lean_Elab_Term_mkForall(x_1, x_24, x_365, x_363, x_366);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_368 = lean_ctor_get(x_367, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_369, 2);
lean_inc(x_370);
x_371 = lean_ctor_get(x_367, 0);
lean_inc(x_371);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_372 = x_367;
} else {
 lean_dec_ref(x_367);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_368, 1);
lean_inc(x_373);
x_374 = lean_ctor_get(x_368, 2);
lean_inc(x_374);
x_375 = lean_ctor_get(x_368, 3);
lean_inc(x_375);
x_376 = lean_ctor_get(x_368, 4);
lean_inc(x_376);
x_377 = lean_ctor_get(x_368, 5);
lean_inc(x_377);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 lean_ctor_release(x_368, 2);
 lean_ctor_release(x_368, 3);
 lean_ctor_release(x_368, 4);
 lean_ctor_release(x_368, 5);
 x_378 = x_368;
} else {
 lean_dec_ref(x_368);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_369, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_369, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_369, 3);
lean_inc(x_381);
x_382 = lean_ctor_get(x_369, 4);
lean_inc(x_382);
x_383 = lean_ctor_get(x_369, 5);
lean_inc(x_383);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 lean_ctor_release(x_369, 2);
 lean_ctor_release(x_369, 3);
 lean_ctor_release(x_369, 4);
 lean_ctor_release(x_369, 5);
 x_384 = x_369;
} else {
 lean_dec_ref(x_369);
 x_384 = lean_box(0);
}
x_385 = lean_ctor_get(x_370, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_370, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 lean_ctor_release(x_370, 2);
 x_387 = x_370;
} else {
 lean_dec_ref(x_370);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(0, 3, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_386);
lean_ctor_set(x_388, 2, x_77);
if (lean_is_scalar(x_384)) {
 x_389 = lean_alloc_ctor(0, 6, 0);
} else {
 x_389 = x_384;
}
lean_ctor_set(x_389, 0, x_379);
lean_ctor_set(x_389, 1, x_380);
lean_ctor_set(x_389, 2, x_388);
lean_ctor_set(x_389, 3, x_381);
lean_ctor_set(x_389, 4, x_382);
lean_ctor_set(x_389, 5, x_383);
if (lean_is_scalar(x_378)) {
 x_390 = lean_alloc_ctor(0, 6, 0);
} else {
 x_390 = x_378;
}
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_373);
lean_ctor_set(x_390, 2, x_374);
lean_ctor_set(x_390, 3, x_375);
lean_ctor_set(x_390, 4, x_376);
lean_ctor_set(x_390, 5, x_377);
if (lean_is_scalar(x_372)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_372;
}
lean_ctor_set(x_391, 0, x_371);
lean_ctor_set(x_391, 1, x_390);
return x_391;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_392 = lean_ctor_get(x_367, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_393, 2);
lean_inc(x_394);
x_395 = lean_ctor_get(x_367, 0);
lean_inc(x_395);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_396 = x_367;
} else {
 lean_dec_ref(x_367);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_392, 1);
lean_inc(x_397);
x_398 = lean_ctor_get(x_392, 2);
lean_inc(x_398);
x_399 = lean_ctor_get(x_392, 3);
lean_inc(x_399);
x_400 = lean_ctor_get(x_392, 4);
lean_inc(x_400);
x_401 = lean_ctor_get(x_392, 5);
lean_inc(x_401);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 lean_ctor_release(x_392, 2);
 lean_ctor_release(x_392, 3);
 lean_ctor_release(x_392, 4);
 lean_ctor_release(x_392, 5);
 x_402 = x_392;
} else {
 lean_dec_ref(x_392);
 x_402 = lean_box(0);
}
x_403 = lean_ctor_get(x_393, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_393, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_393, 3);
lean_inc(x_405);
x_406 = lean_ctor_get(x_393, 4);
lean_inc(x_406);
x_407 = lean_ctor_get(x_393, 5);
lean_inc(x_407);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 lean_ctor_release(x_393, 2);
 lean_ctor_release(x_393, 3);
 lean_ctor_release(x_393, 4);
 lean_ctor_release(x_393, 5);
 x_408 = x_393;
} else {
 lean_dec_ref(x_393);
 x_408 = lean_box(0);
}
x_409 = lean_ctor_get(x_394, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_394, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 lean_ctor_release(x_394, 2);
 x_411 = x_394;
} else {
 lean_dec_ref(x_394);
 x_411 = lean_box(0);
}
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(0, 3, 0);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_409);
lean_ctor_set(x_412, 1, x_410);
lean_ctor_set(x_412, 2, x_77);
if (lean_is_scalar(x_408)) {
 x_413 = lean_alloc_ctor(0, 6, 0);
} else {
 x_413 = x_408;
}
lean_ctor_set(x_413, 0, x_403);
lean_ctor_set(x_413, 1, x_404);
lean_ctor_set(x_413, 2, x_412);
lean_ctor_set(x_413, 3, x_405);
lean_ctor_set(x_413, 4, x_406);
lean_ctor_set(x_413, 5, x_407);
if (lean_is_scalar(x_402)) {
 x_414 = lean_alloc_ctor(0, 6, 0);
} else {
 x_414 = x_402;
}
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_397);
lean_ctor_set(x_414, 2, x_398);
lean_ctor_set(x_414, 3, x_399);
lean_ctor_set(x_414, 4, x_400);
lean_ctor_set(x_414, 5, x_401);
if (lean_is_scalar(x_396)) {
 x_415 = lean_alloc_ctor(1, 2, 0);
} else {
 x_415 = x_396;
}
lean_ctor_set(x_415, 0, x_395);
lean_ctor_set(x_415, 1, x_414);
return x_415;
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_363);
lean_dec(x_24);
x_416 = lean_ctor_get(x_364, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_417, 2);
lean_inc(x_418);
x_419 = lean_ctor_get(x_364, 0);
lean_inc(x_419);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_420 = x_364;
} else {
 lean_dec_ref(x_364);
 x_420 = lean_box(0);
}
x_421 = lean_ctor_get(x_416, 1);
lean_inc(x_421);
x_422 = lean_ctor_get(x_416, 2);
lean_inc(x_422);
x_423 = lean_ctor_get(x_416, 3);
lean_inc(x_423);
x_424 = lean_ctor_get(x_416, 4);
lean_inc(x_424);
x_425 = lean_ctor_get(x_416, 5);
lean_inc(x_425);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 lean_ctor_release(x_416, 4);
 lean_ctor_release(x_416, 5);
 x_426 = x_416;
} else {
 lean_dec_ref(x_416);
 x_426 = lean_box(0);
}
x_427 = lean_ctor_get(x_417, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_417, 1);
lean_inc(x_428);
x_429 = lean_ctor_get(x_417, 3);
lean_inc(x_429);
x_430 = lean_ctor_get(x_417, 4);
lean_inc(x_430);
x_431 = lean_ctor_get(x_417, 5);
lean_inc(x_431);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 lean_ctor_release(x_417, 4);
 lean_ctor_release(x_417, 5);
 x_432 = x_417;
} else {
 lean_dec_ref(x_417);
 x_432 = lean_box(0);
}
x_433 = lean_ctor_get(x_418, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_418, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 lean_ctor_release(x_418, 2);
 x_435 = x_418;
} else {
 lean_dec_ref(x_418);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(0, 3, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_433);
lean_ctor_set(x_436, 1, x_434);
lean_ctor_set(x_436, 2, x_77);
if (lean_is_scalar(x_432)) {
 x_437 = lean_alloc_ctor(0, 6, 0);
} else {
 x_437 = x_432;
}
lean_ctor_set(x_437, 0, x_427);
lean_ctor_set(x_437, 1, x_428);
lean_ctor_set(x_437, 2, x_436);
lean_ctor_set(x_437, 3, x_429);
lean_ctor_set(x_437, 4, x_430);
lean_ctor_set(x_437, 5, x_431);
if (lean_is_scalar(x_426)) {
 x_438 = lean_alloc_ctor(0, 6, 0);
} else {
 x_438 = x_426;
}
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_421);
lean_ctor_set(x_438, 2, x_422);
lean_ctor_set(x_438, 3, x_423);
lean_ctor_set(x_438, 4, x_424);
lean_ctor_set(x_438, 5, x_425);
if (lean_is_scalar(x_420)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_420;
}
lean_ctor_set(x_439, 0, x_419);
lean_ctor_set(x_439, 1, x_438);
return x_439;
}
}
}
}
else
{
uint8_t x_440; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_3);
x_440 = !lean_is_exclusive(x_20);
if (x_440 == 0)
{
return x_20;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_20, 0);
x_442 = lean_ctor_get(x_20, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_20);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
return x_443;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabDepArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabDepArrow(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabDepArrow");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDepArrow___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Term_elabParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unit");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabParen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareBuiltinParser___closed__5;
x_2 = l_Lean_Elab_Term_elabParen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabParen___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabParen___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabParen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_stxInh;
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_array_get(x_6, x_5, x_7);
x_9 = l_Lean_Syntax_isNone(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_8, x_10);
lean_dec(x_8);
x_12 = l_Lean_Elab_Term_elabTerm(x_11, x_2, x_3, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_13 = l_Lean_Elab_Term_elabParen___closed__3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
}
}
lean_object* l_Lean_Elab_Term_elabParen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabParen(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabParen");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabParen___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabParen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_paren___elambda__1___closed__1;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_mkTermId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_mkIdentFrom(x_1, x_2);
x_4 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_5 = lean_array_push(x_4, x_3);
x_6 = l_Lean_Syntax_asNode___closed__1;
x_7 = lean_array_push(x_5, x_6);
x_8 = l_Lean_Parser_Term_id___elambda__1___closed__2;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_mkTermId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_mkTermId(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabListLit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_array_fget(x_3, x_10);
x_12 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1___closed__1;
x_13 = lean_array_push(x_12, x_11);
x_14 = lean_array_push(x_13, x_6);
lean_inc(x_2);
x_15 = l_Array_iterateMAux___main___at_Lean_mkAppStx___spec__1(x_14, x_14, x_7, x_2);
lean_dec(x_14);
x_4 = x_10;
x_5 = lean_box(0);
x_6 = x_15;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
}
lean_object* _init_l_Lean_Elab_Term_elabListLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("List");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabListLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_elabListLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabListLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabListLit___closed__2;
x_2 = l_Lean_Parser_Term_cons___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_elabListLit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nil");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabListLit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_elabListLit___closed__2;
x_2 = l_Lean_Elab_Term_elabListLit___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabListLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_stxInh;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get(x_6, x_5, x_7);
x_9 = l_Lean_Elab_Term_elabListLit___closed__3;
x_10 = l_Lean_Elab_Term_mkTermId(x_8, x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_array_get(x_6, x_5, x_11);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Array_empty___closed__1;
x_16 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(x_14, x_13, x_7, x_15);
lean_dec(x_13);
x_17 = lean_array_get_size(x_16);
x_18 = lean_array_get(x_6, x_5, x_14);
x_19 = l_Lean_Elab_Term_elabListLit___closed__5;
x_20 = l_Lean_Elab_Term_mkTermId(x_18, x_19);
lean_dec(x_18);
x_21 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabListLit___spec__1(x_5, x_10, x_16, x_17, lean_box(0), x_20);
lean_dec(x_16);
x_22 = l_Lean_Elab_Term_elabTerm(x_21, x_2, x_3, x_4);
return x_22;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabListLit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabListLit___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_elabListLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabListLit(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabListLit");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabListLit___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabListLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_listLit___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabExplicitUniv___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabExplicitUniv___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_elabExplicitUniv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_elabExplicitUniv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_NamedArg_hasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Name_toString___closed__1;
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_2);
x_5 = l_Prod_HasRepr___rarg___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lean_formatEntry___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Syntax_formatStx___main(x_9);
x_11 = l_Lean_Options_empty;
x_12 = l_Lean_Format_pretty(x_10, x_11);
x_13 = lean_string_append(x_8, x_12);
lean_dec(x_12);
x_14 = l_Option_HasRepr___rarg___closed__3;
x_15 = lean_string_append(x_13, x_14);
return x_15;
}
}
lean_object* _init_l_Lean_Elab_Term_NamedArg_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_NamedArg_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_NamedArg_inhabited___closed__1;
return x_1;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_5);
return x_11;
}
}
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_addNamedArg___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 2;
x_6 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_withNode___spec__2(x_2, x_5, x_1, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("argument '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' was already set");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(x_1, x_2, x_1, x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_push(x_1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_Name_toString___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_11);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Elab_Term_addNamedArg___closed__3;
x_17 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_Term_addNamedArg___closed__6;
x_19 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_throwError___at_Lean_Elab_Term_addNamedArg___spec__2(x_3, x_19, x_4, x_5);
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
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Term_addNamedArg___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwError___at_Lean_Elab_Term_addNamedArg___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_addNamedArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Term_12__resolveLocalNameAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = lean_local_ctx_find_from_user_name(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_3);
x_2 = x_4;
x_3 = x_7;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = l_Lean_LocalDecl_toExpr(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
lean_dec(x_6);
x_14 = l_Lean_LocalDecl_toExpr(x_13);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
return x_17;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_12__resolveLocalNameAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_12__resolveLocalNameAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Term_13__resolveLocalName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Term_getLCtx(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(0);
x_8 = l___private_Init_Lean_Elab_Term_12__resolveLocalNameAux___main(x_6, x_1, x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = l___private_Init_Lean_Elab_Term_12__resolveLocalNameAux___main(x_9, x_1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_13__resolveLocalName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_13__resolveLocalName(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_14__mkFreshLevelMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
lean_inc(x_5);
x_11 = l_Lean_Elab_Term_mkFreshLevelMVar(x_1, x_5, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_4);
x_3 = x_10;
x_4 = x_14;
x_6 = x_13;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_14__mkFreshLevelMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
lean_inc(x_2);
x_6 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_14__mkFreshLevelMVars___spec__1(x_1, x_2, x_2, x_5, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_14__mkFreshLevelMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldMAux___main___at___private_Init_Lean_Elab_Term_14__mkFreshLevelMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_Term_14__mkFreshLevelMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_Term_14__mkFreshLevelMVars(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_Term_15__mkConsts___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_TermElabM_inhabited(lean_box(0));
return x_1;
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_15__mkConsts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_3);
x_15 = lean_environment_find(x_3, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_10);
lean_dec(x_14);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_4);
x_16 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_15__mkConsts___spec__1___closed__1;
x_17 = l_unreachable_x21___rarg(x_16);
lean_inc(x_6);
x_18 = lean_apply_2(x_17, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_4 = x_19;
x_5 = x_12;
x_7 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = l_Lean_ConstantInfo_lparams(x_26);
lean_dec(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_List_lengthAux___main___rarg(x_27, x_28);
lean_dec(x_27);
x_30 = l_List_lengthAux___main___rarg(x_2, x_28);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_nat_sub(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
lean_inc(x_6);
x_33 = l___private_Init_Lean_Elab_Term_14__mkFreshLevelMVars(x_1, x_32, x_6, x_7);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_2);
x_36 = l_List_append___rarg(x_2, x_34);
x_37 = l_Lean_mkConst(x_13, x_36);
lean_ctor_set(x_10, 0, x_37);
lean_ctor_set(x_5, 1, x_4);
x_4 = x_5;
x_5 = x_12;
x_7 = x_35;
goto _start;
}
else
{
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_10);
lean_dec(x_14);
lean_dec(x_13);
lean_free_object(x_5);
x_5 = x_12;
goto _start;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_5, 1);
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
lean_inc(x_41);
lean_inc(x_3);
x_43 = lean_environment_find(x_3, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_5);
lean_dec(x_4);
x_44 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_15__mkConsts___spec__1___closed__1;
x_45 = l_unreachable_x21___rarg(x_44);
lean_inc(x_6);
x_46 = lean_apply_2(x_45, x_6, x_7);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_4 = x_47;
x_5 = x_40;
x_7 = x_48;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_52 = x_46;
} else {
 lean_dec_ref(x_46);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_43, 0);
lean_inc(x_54);
lean_dec(x_43);
x_55 = l_Lean_ConstantInfo_lparams(x_54);
lean_dec(x_54);
x_56 = lean_unsigned_to_nat(0u);
x_57 = l_List_lengthAux___main___rarg(x_55, x_56);
lean_dec(x_55);
x_58 = l_List_lengthAux___main___rarg(x_2, x_56);
x_59 = lean_nat_dec_lt(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_nat_sub(x_57, x_58);
lean_dec(x_58);
lean_dec(x_57);
lean_inc(x_6);
x_61 = l___private_Init_Lean_Elab_Term_14__mkFreshLevelMVars(x_1, x_60, x_6, x_7);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_2);
x_64 = l_List_append___rarg(x_2, x_62);
x_65 = l_Lean_mkConst(x_41, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_42);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 0, x_66);
x_4 = x_5;
x_5 = x_40;
x_7 = x_63;
goto _start;
}
else
{
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_5);
x_5 = x_40;
goto _start;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_5, 0);
x_70 = lean_ctor_get(x_5, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_5);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_73 = x_69;
} else {
 lean_dec_ref(x_69);
 x_73 = lean_box(0);
}
lean_inc(x_71);
lean_inc(x_3);
x_74 = lean_environment_find(x_3, x_71);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_4);
x_75 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_15__mkConsts___spec__1___closed__1;
x_76 = l_unreachable_x21___rarg(x_75);
lean_inc(x_6);
x_77 = lean_apply_2(x_76, x_6, x_7);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_4 = x_78;
x_5 = x_70;
x_7 = x_79;
goto _start;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_70);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_83 = x_77;
} else {
 lean_dec_ref(x_77);
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
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_85 = lean_ctor_get(x_74, 0);
lean_inc(x_85);
lean_dec(x_74);
x_86 = l_Lean_ConstantInfo_lparams(x_85);
lean_dec(x_85);
x_87 = lean_unsigned_to_nat(0u);
x_88 = l_List_lengthAux___main___rarg(x_86, x_87);
lean_dec(x_86);
x_89 = l_List_lengthAux___main___rarg(x_2, x_87);
x_90 = lean_nat_dec_lt(x_88, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_91 = lean_nat_sub(x_88, x_89);
lean_dec(x_89);
lean_dec(x_88);
lean_inc(x_6);
x_92 = l___private_Init_Lean_Elab_Term_14__mkFreshLevelMVars(x_1, x_91, x_6, x_7);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_2);
x_95 = l_List_append___rarg(x_2, x_93);
x_96 = l_Lean_mkConst(x_71, x_95);
if (lean_is_scalar(x_73)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_73;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_72);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_4);
x_4 = x_98;
x_5 = x_70;
x_7 = x_94;
goto _start;
}
else
{
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
x_5 = x_70;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_15__mkConsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Elab_Term_getEnv___rarg(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_15__mkConsts___spec__1(x_1, x_3, x_7, x_9, x_2, x_4, x_8);
return x_10;
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_15__mkConsts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_15__mkConsts___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_15__mkConsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Term_15__mkConsts(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many explicit universe levels");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_resolveName___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_resolveName___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown identifier '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_resolveName___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_resolveName___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_resolveName___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of explicit universe parameters, '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_resolveName___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_resolveName___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is a local");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_resolveName___closed__12;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_resolveName___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_resolveName___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_resolveName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = l___private_Init_Lean_Elab_Term_13__resolveLocalName(x_1, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_List_isEmpty___rarg(x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
lean_inc(x_5);
x_11 = l___private_Init_Lean_Elab_Term_15__mkConsts(x_4, x_2, x_3, x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = l_List_isEmpty___rarg(x_13);
if (x_15 == 0)
{
lean_dec(x_5);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_free_object(x_11);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_resolveName___closed__3;
x_17 = l_Lean_Elab_throwError___at_Lean_Elab_Term_addNamedArg___spec__2(x_4, x_16, x_5, x_14);
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = l_List_isEmpty___rarg(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_22);
x_26 = l_Lean_Elab_Term_resolveName___closed__3;
x_27 = l_Lean_Elab_throwError___at_Lean_Elab_Term_addNamedArg___spec__2(x_4, x_26, x_5, x_23);
lean_dec(x_5);
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
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_2);
x_36 = l_Lean_Elab_Term_getEnv___rarg(x_9);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Elab_Term_getCurrNamespace(x_5, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_Term_getOpenDecls(x_5, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_1);
x_45 = l_Lean_Elab_resolveGlobalName(x_37, x_40, x_43, x_1);
lean_dec(x_40);
lean_dec(x_37);
x_46 = l_List_isEmpty___rarg(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_1);
lean_inc(x_5);
x_47 = l___private_Init_Lean_Elab_Term_15__mkConsts(x_4, x_45, x_3, x_5, x_44);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_51 = l_List_isEmpty___rarg(x_49);
if (x_51 == 0)
{
lean_dec(x_5);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_free_object(x_47);
lean_dec(x_49);
x_52 = l_Lean_Elab_Term_resolveName___closed__3;
x_53 = l_Lean_Elab_throwError___at_Lean_Elab_Term_addNamedArg___spec__2(x_4, x_52, x_5, x_50);
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
return x_53;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_47, 0);
x_59 = lean_ctor_get(x_47, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_47);
x_60 = l_List_isEmpty___rarg(x_58);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_5);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_58);
x_62 = l_Lean_Elab_Term_resolveName___closed__3;
x_63 = l_Lean_Elab_throwError___at_Lean_Elab_Term_addNamedArg___spec__2(x_4, x_62, x_5, x_59);
lean_dec(x_5);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_5);
x_68 = !lean_is_exclusive(x_47);
if (x_68 == 0)
{
return x_47;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_47, 0);
x_70 = lean_ctor_get(x_47, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_47);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_45);
lean_dec(x_3);
x_72 = l_Lean_Name_toString___closed__1;
x_73 = l_Lean_Name_toStringWithSep___main(x_72, x_1);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = l_Lean_Elab_Term_resolveName___closed__6;
x_77 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_Elab_Term_resolveName___closed__8;
x_79 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_Elab_throwError___at_Lean_Elab_Term_addNamedArg___spec__2(x_4, x_79, x_5, x_44);
lean_dec(x_5);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
return x_80;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_80);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
else
{
lean_object* x_85; uint8_t x_86; 
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_ctor_get(x_8, 0);
lean_inc(x_85);
lean_dec(x_8);
x_86 = !lean_is_exclusive(x_7);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_7, 1);
x_88 = lean_ctor_get(x_7, 0);
lean_dec(x_88);
x_89 = lean_ctor_get(x_85, 0);
lean_inc(x_89);
x_90 = l_List_isEmpty___rarg(x_3);
lean_dec(x_3);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_free_object(x_7);
lean_dec(x_85);
x_91 = l_Lean_Expr_fvarId_x21(x_89);
lean_dec(x_89);
x_92 = l_Lean_Name_toString___closed__1;
x_93 = l_Lean_Name_toStringWithSep___main(x_92, x_91);
x_94 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = l_Lean_Elab_Term_resolveName___closed__11;
x_97 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_Elab_Term_resolveName___closed__14;
x_99 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Elab_throwError___at_Lean_Elab_Term_addNamedArg___spec__2(x_4, x_99, x_5, x_87);
lean_dec(x_5);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
return x_100;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_100);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_89);
lean_dec(x_5);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_85);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_7, 0, x_106);
return x_7;
}
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_7, 1);
lean_inc(x_107);
lean_dec(x_7);
x_108 = lean_ctor_get(x_85, 0);
lean_inc(x_108);
x_109 = l_List_isEmpty___rarg(x_3);
lean_dec(x_3);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_85);
x_110 = l_Lean_Expr_fvarId_x21(x_108);
lean_dec(x_108);
x_111 = l_Lean_Name_toString___closed__1;
x_112 = l_Lean_Name_toStringWithSep___main(x_111, x_110);
x_113 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = l_Lean_Elab_Term_resolveName___closed__11;
x_116 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = l_Lean_Elab_Term_resolveName___closed__14;
x_118 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_Elab_throwError___at_Lean_Elab_Term_addNamedArg___spec__2(x_4, x_118, x_5, x_107);
lean_dec(x_5);
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
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_108);
lean_dec(x_5);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_85);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_107);
return x_126;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_resolveName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_resolveName(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Term_ensureHasType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type mismatch");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_ensureHasType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_ensureHasType___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_ensureHasType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_ensureHasType___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_5);
lean_inc(x_8);
lean_inc(x_3);
x_9 = l_Lean_Elab_Term_isDefEq(x_1, x_3, x_8, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
lean_inc(x_5);
x_13 = l_Lean_Elab_Term_instantiateMVars(x_1, x_4, x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_5);
x_16 = l_Lean_Elab_Term_instantiateMVars(x_1, x_3, x_5, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_5);
x_19 = l_Lean_Elab_Term_instantiateMVars(x_1, x_8, x_5, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_14);
x_23 = l_Lean_indentExpr(x_22);
x_24 = l_Lean_Elab_Term_ensureHasType___closed__3;
x_25 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_MessageData_ofList___closed__3;
x_27 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Meta_Exception_mkAppTypeMismatchMessage___closed__8;
x_29 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_17);
x_31 = l_Lean_indentExpr(x_30);
x_32 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
x_34 = l_Lean_KernelException_toMessageData___closed__12;
x_35 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_20);
x_37 = l_Lean_indentExpr(x_36);
x_38 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(x_1, x_38, x_5, x_21);
lean_dec(x_5);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_9, 0);
lean_dec(x_41);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_9, 1);
lean_inc(x_42);
lean_dec(x_9);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_9);
if (x_44 == 0)
{
return x_9;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_9, 0);
x_46 = lean_ctor_get(x_9, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_9);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_ensureHasType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Term_ensureHasType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_consumeDefaultParams___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_consumeDefaultParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_consumeDefaultParams___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_consumeDefaultParams___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_consumeDefaultParams___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_consumeDefaultParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_consumeDefaultParams(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_synthesizeInstMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to synthesize instance");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_synthesizeInstMVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_synthesizeInstMVar___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_synthesizeInstMVar___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_synthesizeInstMVar___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_synthesizeInstMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_2);
x_5 = l_Lean_Elab_Term_isExprMVarAssigned(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_Elab_Term_getMVarDecl(x_2, x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_3);
x_13 = l_Lean_Elab_Term_instantiateMVars(x_1, x_12, x_3, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_3);
lean_inc(x_14);
x_16 = l_Lean_Elab_Term_trySynthInstance(x_1, x_14, x_3, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_20 = l_Lean_indentExpr(x_19);
x_21 = l_Lean_Elab_Term_synthesizeInstMVar___closed__3;
x_22 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Elab_throwError___at_Lean_Elab_Term_addNamedArg___spec__2(x_1, x_22, x_3, x_18);
lean_dec(x_3);
return x_23;
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = l_Lean_Elab_Term_assignExprMVar(x_2, x_25, x_3, x_24);
lean_dec(x_3);
return x_26;
}
default: 
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_16, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_16, 0, x_29);
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_dec(x_16);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_5);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_5, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_5, 0, x_39);
return x_5;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_5, 1);
lean_inc(x_40);
lean_dec(x_5);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
lean_object* l_Lean_Elab_Term_synthesizeInstMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_synthesizeInstMVar(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeInstMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
lean_inc(x_4);
x_13 = l_Lean_Elab_Term_synthesizeInstMVar(x_1, x_10, x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_3 = x_12;
x_5 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_synthesizeInstMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeInstMVars___spec__1(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeInstMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeInstMVars___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_synthesizeInstMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_synthesizeInstMVars(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_10, x_1, x_14);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many arguments");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit parameter '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is missing, unused named arguments ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_8);
x_12 = l_Lean_Elab_Term_whnfForall(x_1, x_8, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 7)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint64_t x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_13, 2);
lean_inc(x_43);
x_44 = lean_ctor_get_uint64(x_13, sizeof(void*)*3);
lean_dec(x_13);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___spec__1(x_41, x_6, x_45);
if (lean_obj_tag(x_46) == 0)
{
if (x_4 == 0)
{
uint8_t x_47; lean_object* x_48; 
x_47 = (uint8_t)((x_44 << 24) >> 61);
x_48 = lean_box(x_47);
switch (lean_obj_tag(x_48)) {
case 1:
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_41);
lean_dec(x_8);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_42);
x_50 = 0;
x_51 = lean_box(0);
lean_inc(x_10);
x_52 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_49, x_50, x_51, x_10, x_14);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_expr_instantiate1(x_43, x_53);
lean_dec(x_43);
x_56 = l_Lean_mkApp(x_9, x_53);
x_8 = x_55;
x_9 = x_56;
x_11 = x_54;
goto _start;
}
case 3:
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_41);
lean_dec(x_8);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_42);
x_59 = 1;
x_60 = lean_box(0);
lean_inc(x_10);
x_61 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_58, x_59, x_60, x_10, x_14);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Expr_mvarId_x21(x_62);
x_65 = lean_box(0);
lean_inc(x_1);
lean_inc(x_64);
x_66 = l_Lean_Elab_Term_registerSyntheticMVar(x_64, x_1, x_65, x_10, x_63);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_array_push(x_7, x_64);
x_69 = lean_expr_instantiate1(x_43, x_62);
lean_dec(x_43);
x_70 = l_Lean_mkApp(x_9, x_62);
x_7 = x_68;
x_8 = x_69;
x_9 = x_70;
x_11 = x_67;
goto _start;
}
default: 
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_48);
x_72 = lean_array_get_size(x_2);
x_73 = lean_nat_dec_lt(x_5, x_72);
lean_dec(x_72);
if (x_73 == 0)
{
uint8_t x_74; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_5);
x_74 = l_Array_isEmpty___rarg(x_6);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_75 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_75, 0, x_41);
x_76 = l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__6;
x_77 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__9;
x_79 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___spec__2(x_45, x_6);
x_81 = l_Array_toList___rarg(x_80);
lean_dec(x_80);
x_82 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_81);
x_83 = l_Array_HasRepr___rarg___closed__1;
x_84 = lean_string_append(x_83, x_82);
lean_dec(x_82);
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(x_1, x_87, x_10, x_14);
lean_dec(x_10);
lean_dec(x_1);
return x_88;
}
else
{
lean_object* x_89; 
lean_dec(x_41);
lean_dec(x_6);
lean_inc(x_10);
x_89 = l_Lean_Elab_Term_ensureHasType(x_1, x_3, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeInstMVars___spec__1(x_1, x_7, x_45, x_10, x_91);
lean_dec(x_7);
lean_dec(x_1);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
lean_ctor_set(x_92, 0, x_90);
return x_92;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_dec(x_90);
x_97 = !lean_is_exclusive(x_92);
if (x_97 == 0)
{
return x_92;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_92, 0);
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_92);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_89);
if (x_101 == 0)
{
return x_89;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_89, 0);
x_103 = lean_ctor_get(x_89, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_89);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_41);
lean_dec(x_8);
x_105 = lean_array_fget(x_2, x_5);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_42);
lean_inc(x_10);
x_107 = l_Lean_Elab_Term_elabTerm(x_105, x_106, x_10, x_14);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_nat_add(x_5, x_110);
lean_dec(x_5);
x_112 = lean_expr_instantiate1(x_43, x_108);
lean_dec(x_43);
x_113 = l_Lean_mkApp(x_9, x_108);
x_5 = x_111;
x_8 = x_112;
x_9 = x_113;
x_11 = x_109;
goto _start;
}
else
{
uint8_t x_115; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_107);
if (x_115 == 0)
{
return x_107;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_107, 0);
x_117 = lean_ctor_get(x_107, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_107);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
}
}
else
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_array_get_size(x_2);
x_120 = lean_nat_dec_lt(x_5, x_119);
lean_dec(x_119);
if (x_120 == 0)
{
uint8_t x_121; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_5);
x_121 = l_Array_isEmpty___rarg(x_6);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_122 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_122, 0, x_41);
x_123 = l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__6;
x_124 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__9;
x_126 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___spec__2(x_45, x_6);
x_128 = l_Array_toList___rarg(x_127);
lean_dec(x_127);
x_129 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_128);
x_130 = l_Array_HasRepr___rarg___closed__1;
x_131 = lean_string_append(x_130, x_129);
lean_dec(x_129);
x_132 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_134, 0, x_126);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(x_1, x_134, x_10, x_14);
lean_dec(x_10);
lean_dec(x_1);
return x_135;
}
else
{
lean_object* x_136; 
lean_dec(x_41);
lean_dec(x_6);
lean_inc(x_10);
x_136 = l_Lean_Elab_Term_ensureHasType(x_1, x_3, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeInstMVars___spec__1(x_1, x_7, x_45, x_10, x_138);
lean_dec(x_7);
lean_dec(x_1);
if (lean_obj_tag(x_139) == 0)
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_139, 0);
lean_dec(x_141);
lean_ctor_set(x_139, 0, x_137);
return x_139;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
else
{
uint8_t x_144; 
lean_dec(x_137);
x_144 = !lean_is_exclusive(x_139);
if (x_144 == 0)
{
return x_139;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_139, 0);
x_146 = lean_ctor_get(x_139, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_139);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
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
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_41);
lean_dec(x_8);
x_152 = lean_array_fget(x_2, x_5);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_42);
lean_inc(x_10);
x_154 = l_Lean_Elab_Term_elabTerm(x_152, x_153, x_10, x_14);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_unsigned_to_nat(1u);
x_158 = lean_nat_add(x_5, x_157);
lean_dec(x_5);
x_159 = lean_expr_instantiate1(x_43, x_155);
lean_dec(x_43);
x_160 = l_Lean_mkApp(x_9, x_155);
x_5 = x_158;
x_8 = x_159;
x_9 = x_160;
x_11 = x_156;
goto _start;
}
else
{
uint8_t x_162; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_154);
if (x_162 == 0)
{
return x_154;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_154, 0);
x_164 = lean_ctor_get(x_154, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_154);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_41);
lean_dec(x_8);
x_166 = !lean_is_exclusive(x_46);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_167 = lean_ctor_get(x_46, 0);
x_168 = l_Lean_Elab_Term_NamedArg_inhabited;
x_169 = lean_array_get(x_168, x_6, x_167);
x_170 = l_Array_eraseIdx___rarg(x_6, x_167);
lean_dec(x_167);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
lean_ctor_set(x_46, 0, x_42);
lean_inc(x_10);
x_172 = l_Lean_Elab_Term_elabTerm(x_171, x_46, x_10, x_14);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_expr_instantiate1(x_43, x_173);
lean_dec(x_43);
x_176 = l_Lean_mkApp(x_9, x_173);
x_6 = x_170;
x_8 = x_175;
x_9 = x_176;
x_11 = x_174;
goto _start;
}
else
{
uint8_t x_178; 
lean_dec(x_170);
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_178 = !lean_is_exclusive(x_172);
if (x_178 == 0)
{
return x_172;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_172, 0);
x_180 = lean_ctor_get(x_172, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_172);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_182 = lean_ctor_get(x_46, 0);
lean_inc(x_182);
lean_dec(x_46);
x_183 = l_Lean_Elab_Term_NamedArg_inhabited;
x_184 = lean_array_get(x_183, x_6, x_182);
x_185 = l_Array_eraseIdx___rarg(x_6, x_182);
lean_dec(x_182);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_42);
lean_inc(x_10);
x_188 = l_Lean_Elab_Term_elabTerm(x_186, x_187, x_10, x_14);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_expr_instantiate1(x_43, x_189);
lean_dec(x_43);
x_192 = l_Lean_mkApp(x_9, x_189);
x_6 = x_185;
x_8 = x_191;
x_9 = x_192;
x_11 = x_190;
goto _start;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_185);
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_194 = lean_ctor_get(x_188, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_196 = x_188;
} else {
 lean_dec_ref(x_188);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
}
}
else
{
lean_object* x_198; 
lean_dec(x_13);
x_198 = lean_box(0);
x_15 = x_198;
goto block_40;
}
block_40:
{
uint8_t x_16; 
lean_dec(x_15);
x_16 = l_Array_isEmpty___rarg(x_6);
lean_dec(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_17 = l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__3;
x_18 = l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(x_1, x_17, x_10, x_14);
lean_dec(x_10);
lean_dec(x_1);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_array_get_size(x_2);
x_20 = lean_nat_dec_eq(x_5, x_19);
lean_dec(x_19);
lean_dec(x_5);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_21 = l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__3;
x_22 = l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(x_1, x_21, x_10, x_14);
lean_dec(x_10);
lean_dec(x_1);
return x_22;
}
else
{
lean_object* x_23; 
lean_inc(x_10);
x_23 = l_Lean_Elab_Term_ensureHasType(x_1, x_3, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeInstMVars___spec__1(x_1, x_7, x_26, x_10, x_25);
lean_dec(x_7);
lean_dec(x_1);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_24);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_24);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_12);
if (x_199 == 0)
{
return x_12;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_12, 0);
x_201 = lean_ctor_get(x_12, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_12);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_13;
}
}
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Lean_Elab_Term_16__elabAppArgsAux(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_13;
}
}
lean_object* l___private_Init_Lean_Elab_Term_17__elabAppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_2);
x_9 = l_Lean_Elab_Term_inferType(x_1, x_2, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_empty___closed__1;
x_14 = l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main(x_1, x_4, x_5, x_6, x_12, x_3, x_13, x_10, x_2, x_7, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_17__elabAppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Lean_Elab_Term_17__elabAppArgs(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_18__throwFieldError___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 2;
x_6 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_withNode___spec__2(x_2, x_5, x_1, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_18__throwFieldError___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_18__throwFieldError___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = l_Lean_indentExpr(x_7);
x_9 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_MessageData_ofList___closed__3;
x_11 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_Exception_mkAppTypeMismatchMessage___closed__8;
x_13 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = l_Lean_indentExpr(x_14);
x_16 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_18__throwFieldError___spec__1___rarg(x_1, x_16, x_5, x_6);
return x_17;
}
}
lean_object* l___private_Init_Lean_Elab_Term_18__throwFieldError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_18__throwFieldError___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_18__throwFieldError___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure has only ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" field(s)");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure expected");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, index must be greater than 0");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a valid \"field\" because environment does not contain '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__20;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_getAppFn___main(x_3);
if (lean_obj_tag(x_7) == 4)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_37; 
x_12 = l_Lean_Elab_Term_getEnv___rarg(x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_13);
x_37 = l_Lean_isStructureLike(x_13, x_8);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
x_38 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__12;
x_39 = l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(x_1, x_2, x_3, x_38, x_5, x_14);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_39);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
x_16 = x_14;
goto block_36;
}
block_36:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc(x_8);
lean_inc(x_13);
x_17 = l_Lean_getStructureFields(x_13, x_8);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_9, x_18);
lean_dec(x_9);
x_20 = lean_array_get_size(x_17);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
x_22 = l_Nat_repr(x_20);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__6;
x_26 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__9;
x_28 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(x_1, x_2, x_3, x_28, x_5, x_16);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_8);
x_30 = l_Lean_isStructure(x_13, x_8);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_19);
if (lean_is_scalar(x_15)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_15;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_16);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_array_fget(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
lean_inc(x_8);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_8);
lean_ctor_set(x_34, 2, x_8);
if (lean_is_scalar(x_15)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_15;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_16);
return x_35;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_44 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__15;
x_45 = l_Lean_Elab_throwError___at_Lean_Elab_Term_addNamedArg___spec__2(x_1, x_44, x_5, x_6);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_7, 0);
lean_inc(x_50);
lean_dec(x_7);
x_51 = lean_ctor_get(x_4, 0);
lean_inc(x_51);
lean_dec(x_4);
x_52 = l_Lean_Elab_Term_getEnv___rarg(x_6);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_50);
lean_inc(x_54);
x_56 = l_Lean_isStructure(x_54, x_50);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_free_object(x_52);
x_57 = lean_box(0);
lean_inc(x_51);
x_58 = lean_name_mk_string(x_57, x_51);
x_59 = l_Lean_Name_append___main(x_50, x_58);
lean_dec(x_50);
x_60 = l_Lean_Elab_Term_getCurrNamespace(x_5, x_55);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_59);
x_63 = l_Lean_Name_replacePrefix___main(x_59, x_61, x_57);
lean_dec(x_61);
x_64 = l_Lean_Elab_Term_getLCtx(x_5, x_62);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
x_68 = lean_local_ctx_find_from_user_name(x_66, x_63);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
lean_inc(x_59);
x_69 = lean_environment_find(x_54, x_59);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_free_object(x_64);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_51);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18;
x_73 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21;
x_75 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_76, 0, x_59);
x_77 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Elab_Term_resolveName___closed__8;
x_79 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(x_1, x_2, x_3, x_79, x_5, x_67);
return x_80;
}
else
{
lean_object* x_81; 
lean_dec(x_69);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_59);
lean_ctor_set(x_64, 0, x_81);
return x_64;
}
}
else
{
lean_object* x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_68, 0);
lean_inc(x_82);
lean_dec(x_68);
x_83 = l_Lean_LocalDecl_binderInfo(x_82);
x_84 = 4;
x_85 = l_Lean_BinderInfo_beq(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_82);
lean_inc(x_59);
x_86 = lean_environment_find(x_54, x_59);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_free_object(x_64);
x_87 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_87, 0, x_51);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18;
x_90 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21;
x_92 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_93, 0, x_59);
x_94 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_Elab_Term_resolveName___closed__8;
x_96 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(x_1, x_2, x_3, x_96, x_5, x_67);
return x_97;
}
else
{
lean_object* x_98; 
lean_dec(x_86);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_98, 0, x_59);
lean_ctor_set(x_64, 0, x_98);
return x_64;
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_59);
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_99 = l_Lean_LocalDecl_toExpr(x_82);
lean_dec(x_82);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_64, 0, x_100);
return x_64;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_64, 0);
x_102 = lean_ctor_get(x_64, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_64);
x_103 = lean_local_ctx_find_from_user_name(x_101, x_63);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
lean_inc(x_59);
x_104 = lean_environment_find(x_54, x_59);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_105 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_105, 0, x_51);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18;
x_108 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21;
x_110 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_111, 0, x_59);
x_112 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_Elab_Term_resolveName___closed__8;
x_114 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(x_1, x_2, x_3, x_114, x_5, x_102);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_104);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_116 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_116, 0, x_59);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_102);
return x_117;
}
}
else
{
lean_object* x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; 
x_118 = lean_ctor_get(x_103, 0);
lean_inc(x_118);
lean_dec(x_103);
x_119 = l_Lean_LocalDecl_binderInfo(x_118);
x_120 = 4;
x_121 = l_Lean_BinderInfo_beq(x_119, x_120);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_118);
lean_inc(x_59);
x_122 = lean_environment_find(x_54, x_59);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_123 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_123, 0, x_51);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18;
x_126 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21;
x_128 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_129, 0, x_59);
x_130 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_Elab_Term_resolveName___closed__8;
x_132 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(x_1, x_2, x_3, x_132, x_5, x_102);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_122);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_134 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_134, 0, x_59);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_102);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_59);
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_136 = l_Lean_LocalDecl_toExpr(x_118);
lean_dec(x_118);
x_137 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_102);
return x_138;
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_box(0);
lean_inc(x_51);
x_140 = lean_name_mk_string(x_139, x_51);
lean_inc(x_50);
lean_inc(x_54);
x_141 = l_Lean_findField_x3f___main(x_54, x_50, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_free_object(x_52);
x_142 = l_Lean_Name_append___main(x_50, x_140);
lean_dec(x_50);
x_143 = l_Lean_Elab_Term_getCurrNamespace(x_5, x_55);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
lean_inc(x_142);
x_146 = l_Lean_Name_replacePrefix___main(x_142, x_144, x_139);
lean_dec(x_144);
x_147 = l_Lean_Elab_Term_getLCtx(x_5, x_145);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_147, 0);
x_150 = lean_ctor_get(x_147, 1);
x_151 = lean_local_ctx_find_from_user_name(x_149, x_146);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; 
lean_inc(x_142);
x_152 = lean_environment_find(x_54, x_142);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_free_object(x_147);
x_153 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_153, 0, x_51);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18;
x_156 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
x_157 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21;
x_158 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_159, 0, x_142);
x_160 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_Elab_Term_resolveName___closed__8;
x_162 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(x_1, x_2, x_3, x_162, x_5, x_150);
return x_163;
}
else
{
lean_object* x_164; 
lean_dec(x_152);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_164 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_164, 0, x_142);
lean_ctor_set(x_147, 0, x_164);
return x_147;
}
}
else
{
lean_object* x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; 
x_165 = lean_ctor_get(x_151, 0);
lean_inc(x_165);
lean_dec(x_151);
x_166 = l_Lean_LocalDecl_binderInfo(x_165);
x_167 = 4;
x_168 = l_Lean_BinderInfo_beq(x_166, x_167);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_165);
lean_inc(x_142);
x_169 = lean_environment_find(x_54, x_142);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_free_object(x_147);
x_170 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_170, 0, x_51);
x_171 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_171, 0, x_170);
x_172 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18;
x_173 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
x_174 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21;
x_175 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_176, 0, x_142);
x_177 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = l_Lean_Elab_Term_resolveName___closed__8;
x_179 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(x_1, x_2, x_3, x_179, x_5, x_150);
return x_180;
}
else
{
lean_object* x_181; 
lean_dec(x_169);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_181 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_181, 0, x_142);
lean_ctor_set(x_147, 0, x_181);
return x_147;
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_142);
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_182 = l_Lean_LocalDecl_toExpr(x_165);
lean_dec(x_165);
x_183 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_147, 0, x_183);
return x_147;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_147, 0);
x_185 = lean_ctor_get(x_147, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_147);
x_186 = lean_local_ctx_find_from_user_name(x_184, x_146);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; 
lean_inc(x_142);
x_187 = lean_environment_find(x_54, x_142);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_188 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_188, 0, x_51);
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18;
x_191 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_189);
x_192 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21;
x_193 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_194, 0, x_142);
x_195 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_Elab_Term_resolveName___closed__8;
x_197 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_198 = l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(x_1, x_2, x_3, x_197, x_5, x_185);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_187);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_199 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_199, 0, x_142);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_185);
return x_200;
}
}
else
{
lean_object* x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; 
x_201 = lean_ctor_get(x_186, 0);
lean_inc(x_201);
lean_dec(x_186);
x_202 = l_Lean_LocalDecl_binderInfo(x_201);
x_203 = 4;
x_204 = l_Lean_BinderInfo_beq(x_202, x_203);
if (x_204 == 0)
{
lean_object* x_205; 
lean_dec(x_201);
lean_inc(x_142);
x_205 = lean_environment_find(x_54, x_142);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_206 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_206, 0, x_51);
x_207 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_208 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18;
x_209 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
x_210 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21;
x_211 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_212, 0, x_142);
x_213 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_Lean_Elab_Term_resolveName___closed__8;
x_215 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
x_216 = l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(x_1, x_2, x_3, x_215, x_5, x_185);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_205);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_217 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_217, 0, x_142);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_185);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_142);
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_219 = l_Lean_LocalDecl_toExpr(x_201);
lean_dec(x_201);
x_220 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_220, 0, x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_185);
return x_221;
}
}
}
}
else
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_222 = lean_ctor_get(x_141, 0);
lean_inc(x_222);
lean_dec(x_141);
x_223 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_223, 0, x_140);
lean_ctor_set(x_223, 1, x_222);
lean_ctor_set(x_223, 2, x_50);
lean_ctor_set(x_52, 0, x_223);
return x_52;
}
}
}
else
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_224 = lean_ctor_get(x_52, 0);
x_225 = lean_ctor_get(x_52, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_52);
lean_inc(x_50);
lean_inc(x_224);
x_226 = l_Lean_isStructure(x_224, x_50);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_227 = lean_box(0);
lean_inc(x_51);
x_228 = lean_name_mk_string(x_227, x_51);
x_229 = l_Lean_Name_append___main(x_50, x_228);
lean_dec(x_50);
x_230 = l_Lean_Elab_Term_getCurrNamespace(x_5, x_225);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
lean_inc(x_229);
x_233 = l_Lean_Name_replacePrefix___main(x_229, x_231, x_227);
lean_dec(x_231);
x_234 = l_Lean_Elab_Term_getLCtx(x_5, x_232);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_237 = x_234;
} else {
 lean_dec_ref(x_234);
 x_237 = lean_box(0);
}
x_238 = lean_local_ctx_find_from_user_name(x_235, x_233);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; 
lean_inc(x_229);
x_239 = lean_environment_find(x_224, x_229);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_237);
x_240 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_240, 0, x_51);
x_241 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_241, 0, x_240);
x_242 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18;
x_243 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_241);
x_244 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21;
x_245 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_246, 0, x_229);
x_247 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = l_Lean_Elab_Term_resolveName___closed__8;
x_249 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
x_250 = l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(x_1, x_2, x_3, x_249, x_5, x_236);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_239);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_251 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_251, 0, x_229);
if (lean_is_scalar(x_237)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_237;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_236);
return x_252;
}
}
else
{
lean_object* x_253; uint8_t x_254; uint8_t x_255; uint8_t x_256; 
x_253 = lean_ctor_get(x_238, 0);
lean_inc(x_253);
lean_dec(x_238);
x_254 = l_Lean_LocalDecl_binderInfo(x_253);
x_255 = 4;
x_256 = l_Lean_BinderInfo_beq(x_254, x_255);
if (x_256 == 0)
{
lean_object* x_257; 
lean_dec(x_253);
lean_inc(x_229);
x_257 = lean_environment_find(x_224, x_229);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_237);
x_258 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_258, 0, x_51);
x_259 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_259, 0, x_258);
x_260 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18;
x_261 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
x_262 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21;
x_263 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
x_264 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_264, 0, x_229);
x_265 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
x_266 = l_Lean_Elab_Term_resolveName___closed__8;
x_267 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
x_268 = l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(x_1, x_2, x_3, x_267, x_5, x_236);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; 
lean_dec(x_257);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_269 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_269, 0, x_229);
if (lean_is_scalar(x_237)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_237;
}
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_236);
return x_270;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_229);
lean_dec(x_224);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_271 = l_Lean_LocalDecl_toExpr(x_253);
lean_dec(x_253);
x_272 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_272, 0, x_271);
if (lean_is_scalar(x_237)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_237;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_236);
return x_273;
}
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_box(0);
lean_inc(x_51);
x_275 = lean_name_mk_string(x_274, x_51);
lean_inc(x_50);
lean_inc(x_224);
x_276 = l_Lean_findField_x3f___main(x_224, x_50, x_275);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_277 = l_Lean_Name_append___main(x_50, x_275);
lean_dec(x_50);
x_278 = l_Lean_Elab_Term_getCurrNamespace(x_5, x_225);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
lean_inc(x_277);
x_281 = l_Lean_Name_replacePrefix___main(x_277, x_279, x_274);
lean_dec(x_279);
x_282 = l_Lean_Elab_Term_getLCtx(x_5, x_280);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_285 = x_282;
} else {
 lean_dec_ref(x_282);
 x_285 = lean_box(0);
}
x_286 = lean_local_ctx_find_from_user_name(x_283, x_281);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; 
lean_inc(x_277);
x_287 = lean_environment_find(x_224, x_277);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_285);
x_288 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_288, 0, x_51);
x_289 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_289, 0, x_288);
x_290 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18;
x_291 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_289);
x_292 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21;
x_293 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_294, 0, x_277);
x_295 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
x_296 = l_Lean_Elab_Term_resolveName___closed__8;
x_297 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
x_298 = l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(x_1, x_2, x_3, x_297, x_5, x_284);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; 
lean_dec(x_287);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_299 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_299, 0, x_277);
if (lean_is_scalar(x_285)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_285;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_284);
return x_300;
}
}
else
{
lean_object* x_301; uint8_t x_302; uint8_t x_303; uint8_t x_304; 
x_301 = lean_ctor_get(x_286, 0);
lean_inc(x_301);
lean_dec(x_286);
x_302 = l_Lean_LocalDecl_binderInfo(x_301);
x_303 = 4;
x_304 = l_Lean_BinderInfo_beq(x_302, x_303);
if (x_304 == 0)
{
lean_object* x_305; 
lean_dec(x_301);
lean_inc(x_277);
x_305 = lean_environment_find(x_224, x_277);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_285);
x_306 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_306, 0, x_51);
x_307 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_307, 0, x_306);
x_308 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18;
x_309 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_307);
x_310 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21;
x_311 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_312, 0, x_277);
x_313 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
x_314 = l_Lean_Elab_Term_resolveName___closed__8;
x_315 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
x_316 = l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(x_1, x_2, x_3, x_315, x_5, x_284);
return x_316;
}
else
{
lean_object* x_317; lean_object* x_318; 
lean_dec(x_305);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_317 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_317, 0, x_277);
if (lean_is_scalar(x_285)) {
 x_318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_318 = x_285;
}
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_284);
return x_318;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_277);
lean_dec(x_224);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_319 = l_Lean_LocalDecl_toExpr(x_301);
lean_dec(x_301);
x_320 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_320, 0, x_319);
if (lean_is_scalar(x_285)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_285;
}
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_284);
return x_321;
}
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_224);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_2);
x_322 = lean_ctor_get(x_276, 0);
lean_inc(x_322);
lean_dec(x_276);
x_323 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_323, 0, x_275);
lean_ctor_set(x_323, 1, x_322);
lean_ctor_set(x_323, 2, x_50);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_225);
return x_324;
}
}
}
}
}
else
{
lean_object* x_325; lean_object* x_326; 
lean_dec(x_7);
lean_dec(x_4);
x_325 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__3;
x_326 = l___private_Init_Lean_Elab_Term_18__throwFieldError___rarg(x_1, x_2, x_3, x_325, x_5, x_6);
return x_326;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_19__resolveFieldAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Term_20__resolveFieldLoop___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_4, 2, x_14);
x_2 = x_11;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 2);
x_19 = lean_ctor_get(x_4, 3);
x_20 = lean_ctor_get(x_4, 4);
x_21 = lean_ctor_get(x_4, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_18);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set(x_23, 5, x_21);
x_2 = x_11;
x_4 = x_23;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_20__resolveFieldLoop___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
x_8 = l_Lean_Elab_Term_whnfCore(x_1, x_4, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_2);
x_11 = l___private_Init_Lean_Elab_Term_19__resolveFieldAux(x_1, x_2, x_9, x_3, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
x_14 = l_Lean_Elab_Term_unfoldDefinition_x3f(x_1, x_9, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_forMAux___main___at___private_Init_Lean_Elab_Term_20__resolveFieldLoop___main___spec__1(x_5, x_17, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_12);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_array_push(x_5, x_12);
x_4 = x_24;
x_5 = x_25;
x_7 = x_23;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
return x_8;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Term_20__resolveFieldLoop___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at___private_Init_Lean_Elab_Term_20__resolveFieldLoop___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_Term_20__resolveFieldLoop___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_20__resolveFieldLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_20__resolveFieldLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_20__resolveFieldLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_20__resolveFieldLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_20__resolveFieldLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_21__resolveField(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_2);
x_6 = l_Lean_Elab_Term_inferType(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Array_empty___closed__1;
x_10 = l___private_Init_Lean_Elab_Term_20__resolveFieldLoop___main(x_1, x_2, x_3, x_7, x_9, x_4, x_8);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_3);
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
}
lean_object* l___private_Init_Lean_Elab_Term_21__resolveField___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Term_21__resolveField(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Term_22__elabAppFieldsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Elab_Term_17__elabAppArgs(x_1, x_6, x_2, x_3, x_4, x_5, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_inc(x_8);
lean_inc(x_6);
x_11 = l_Lean_Elab_Term_inferType(x_1, x_6, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l___private_Init_Lean_Elab_Term_17__elabAppArgs(x_1, x_6, x_2, x_3, x_4, x_5, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_22__elabAppFieldsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Lean_Elab_Term_22__elabAppFieldsAux(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_3);
return x_11;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of projection notation with `@` modifier");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_23__elabAppFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_List_isEmpty___rarg(x_3);
if (x_10 == 0)
{
if (x_7 == 0)
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Elab_Term_22__elabAppFieldsAux(x_1, x_4, x_5, x_6, x_7, x_2, x_3, x_8, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_12 = l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__3;
x_13 = l_Lean_Elab_throwError___at_Lean_Elab_Term_addNamedArg___spec__2(x_1, x_12, x_8, x_9);
lean_dec(x_8);
lean_dec(x_1);
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
}
else
{
lean_object* x_18; 
x_18 = l___private_Init_Lean_Elab_Term_22__elabAppFieldsAux(x_1, x_4, x_5, x_6, x_7, x_2, x_3, x_8, x_9);
return x_18;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_23__elabAppFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l___private_Init_Lean_Elab_Term_23__elabAppFields(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8, x_9);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__1(lean_object* x_1) {
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
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_List_map___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__1(x_15);
lean_inc(x_2);
x_17 = l_List_append___rarg(x_16, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l___private_Init_Lean_Elab_Term_23__elabAppFields(x_1, x_14, x_17, x_3, x_4, x_5, x_6, x_9, x_10);
lean_dec(x_17);
x_19 = lean_array_push(x_7, x_18);
x_7 = x_19;
x_8 = x_13;
goto _start;
}
}
}
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 2;
x_6 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_withNode___spec__2(x_2, x_5, x_1, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_8);
x_14 = lean_nat_dec_lt(x_9, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_8, x_9);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_9, x_17);
lean_dec(x_9);
lean_inc(x_11);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_19 = l___private_Init_Lean_Elab_Term_24__elabAppFn___main(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_9 = x_18;
x_10 = x_20;
x_12 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected kind of field access");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_24__elabAppFn___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Syntax_getKind(x_2);
x_12 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
x_13 = lean_name_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_choiceKind;
x_15 = lean_name_eq(x_11, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
x_17 = lean_name_eq(x_11, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Parser_Term_id___elambda__1___closed__2;
x_19 = lean_name_eq(x_11, x_18);
lean_dec(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_box(0);
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_9, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_9, 4);
lean_inc(x_25);
x_26 = lean_ctor_get(x_9, 5);
lean_inc(x_26);
x_27 = lean_ctor_get(x_9, 6);
lean_inc(x_27);
x_28 = lean_ctor_get(x_9, 7);
lean_inc(x_28);
x_29 = lean_ctor_get(x_9, 8);
lean_inc(x_29);
x_30 = 0;
x_31 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_23);
lean_ctor_set(x_31, 3, x_24);
lean_ctor_set(x_31, 4, x_25);
lean_ctor_set(x_31, 5, x_26);
lean_ctor_set(x_31, 6, x_27);
lean_ctor_set(x_31, 7, x_28);
lean_ctor_set(x_31, 8, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*9, x_30);
x_32 = l_Lean_Elab_Term_elabTerm(x_2, x_20, x_31, x_10);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = l___private_Init_Lean_Elab_Term_23__elabAppFields(x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_9, x_35);
lean_dec(x_3);
x_37 = lean_array_push(x_8, x_36);
lean_ctor_set(x_32, 0, x_37);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
lean_inc(x_39);
x_40 = l___private_Init_Lean_Elab_Term_23__elabAppFields(x_1, x_38, x_3, x_4, x_5, x_6, x_7, x_9, x_39);
lean_dec(x_3);
x_41 = lean_array_push(x_8, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_32);
if (x_43 == 0)
{
return x_32;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_32, 0);
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_32);
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
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lean_Syntax_getArg(x_2, x_47);
if (lean_obj_tag(x_48) == 3)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_48, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 3);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Elab_Term_elabExplicitUniv___rarg(x_10);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_9);
x_54 = l_Lean_Elab_Term_resolveName(x_49, x_50, x_52, x_2, x_9, x_53);
lean_dec(x_2);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_55, x_9, x_56);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_54, 0);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_54);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_15__mkConsts___spec__1___closed__1;
x_63 = l_unreachable_x21___rarg(x_62);
x_64 = lean_apply_2(x_63, x_9, x_10);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_11);
x_65 = lean_unsigned_to_nat(2u);
x_66 = l_Lean_Syntax_getArg(x_2, x_65);
x_67 = l_Lean_fieldIdxKind;
x_68 = l_Lean_Syntax_isNatLitAux(x_67, x_66);
if (lean_obj_tag(x_68) == 0)
{
if (lean_obj_tag(x_66) == 3)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_unsigned_to_nat(0u);
x_71 = l_Lean_Syntax_getArg(x_2, x_70);
lean_dec(x_2);
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 2);
lean_inc(x_74);
lean_dec(x_69);
x_75 = lean_string_utf8_extract(x_72, x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_3);
x_78 = 1;
x_2 = x_71;
x_3 = x_77;
x_7 = x_78;
goto _start;
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__3;
x_81 = l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__3(x_66, x_80, x_9, x_10);
lean_dec(x_9);
lean_dec(x_66);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_66);
x_82 = lean_ctor_get(x_68, 0);
lean_inc(x_82);
lean_dec(x_68);
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_Syntax_getArg(x_2, x_83);
lean_dec(x_2);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_82);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_3);
x_87 = 1;
x_2 = x_84;
x_3 = x_86;
x_7 = x_87;
goto _start;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_11);
x_89 = l_Lean_Syntax_getArgs(x_2);
x_90 = lean_unsigned_to_nat(0u);
x_91 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_89, x_90, x_8, x_9, x_10);
lean_dec(x_89);
lean_dec(x_2);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_11);
x_92 = lean_unsigned_to_nat(1u);
x_93 = l_Lean_Syntax_getArg(x_2, x_92);
lean_dec(x_2);
x_94 = 1;
x_2 = x_93;
x_7 = x_94;
goto _start;
}
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_24__elabAppFn___main___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
return x_14;
}
}
lean_object* l___private_Init_Lean_Elab_Term_24__elabAppFn___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_7);
lean_dec(x_7);
x_12 = l___private_Init_Lean_Elab_Term_24__elabAppFn___main(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
lean_dec(x_5);
return x_12;
}
}
lean_object* l___private_Init_Lean_Elab_Term_24__elabAppFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Elab_Term_24__elabAppFn___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l___private_Init_Lean_Elab_Term_24__elabAppFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_7);
lean_dec(x_7);
x_12 = l___private_Init_Lean_Elab_Term_24__elabAppFn(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
lean_dec(x_5);
return x_12;
}
}
lean_object* l_Array_filterAux___main___at___private_Init_Lean_Elab_Term_25__getSuccess___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; 
x_7 = lean_array_fget(x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_7);
x_8 = lean_nat_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_11 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_fswap(x_1, x_2, x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_16 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
x_1 = x_13;
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_2);
x_2 = x_19;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_25__getSuccess(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_filterAux___main___at___private_Init_Lean_Elab_Term_25__getSuccess___spec__1(x_1, x_2, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_Term_26__toMessageData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = l_Lean_FileMap_toPosition(x_4, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_Lean_FileMap_toPosition(x_8, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_26__toMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_26__toMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_26__toMessageData___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_26__toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = l_Lean_Elab_getPos___at_Lean_Elab_Term_withNode___spec__3(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_Term_26__toMessageData___spec__1(x_8, x_3, x_7);
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = l_Lean_Position_DecidableEq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = l_Nat_repr(x_14);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l___private_Init_Lean_Elab_Term_26__toMessageData___closed__2;
x_19 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = l_Nat_repr(x_20);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_26 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_ctor_get(x_1, 4);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_9, 0, x_28);
return x_9;
}
else
{
lean_object* x_29; 
lean_dec(x_12);
x_29 = lean_ctor_get(x_1, 4);
lean_inc(x_29);
lean_dec(x_1);
lean_ctor_set(x_9, 0, x_29);
return x_9;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = l_Lean_Position_DecidableEq(x_30, x_32);
lean_dec(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = l_Nat_repr(x_34);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l___private_Init_Lean_Elab_Term_26__toMessageData___closed__2;
x_39 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = l_Nat_repr(x_40);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_46 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_ctor_get(x_1, 4);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_31);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_32);
x_50 = lean_ctor_get(x_1, 4);
lean_inc(x_50);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_31);
return x_51;
}
}
}
}
lean_object* l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_Term_26__toMessageData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_Term_26__toMessageData___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Term_26__toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_Term_26__toMessageData(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_27__mergeFailures___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = l_Array_empty___closed__1;
x_9 = x_3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_3, x_2);
x_12 = lean_box(0);
lean_inc(x_11);
x_13 = x_12;
x_14 = lean_array_fset(x_3, x_2, x_13);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_List_foldlM___main___at___private_Init_Lean_Elab_Term_15__mkConsts___spec__1___closed__1;
x_16 = l_unreachable_x21___rarg(x_15);
lean_inc(x_4);
x_17 = lean_apply_2(x_16, x_4, x_5);
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
x_23 = lean_array_fset(x_14, x_2, x_22);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_23;
x_5 = x_19;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_11, 0);
lean_inc(x_29);
x_30 = l___private_Init_Lean_Elab_Term_26__toMessageData(x_29, x_1, x_4, x_5);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_2, x_33);
x_35 = x_31;
x_36 = lean_array_fset(x_14, x_2, x_35);
lean_dec(x_2);
x_2 = x_34;
x_3 = x_36;
x_5 = x_32;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_27__mergeFailures___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 2;
x_6 = l_Lean_Elab_mkMessage___at_Lean_Elab_Term_withNode___spec__2(x_2, x_5, x_1, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_27__mergeFailures___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_27__mergeFailures___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("overloaded, errors ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_6 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_27__mergeFailures___spec__1(x_2, x_5, x_1, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_MessageData_ofArray(x_7);
lean_dec(x_7);
x_10 = l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__3;
x_11 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_27__mergeFailures___spec__2___rarg(x_2, x_11, x_3, x_8);
lean_dec(x_3);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_27__mergeFailures(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_27__mergeFailures___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_27__mergeFailures___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_27__mergeFailures___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwError___at___private_Init_Lean_Elab_Term_27__mergeFailures___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_28__elabAppAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_16);
lean_inc(x_1);
x_20 = lean_alloc_ctor(5, 4, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_1);
lean_ctor_set(x_20, 3, x_19);
x_21 = x_20;
x_22 = lean_array_fset(x_11, x_2, x_21);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lean_MessageData_Inhabited;
x_25 = l_unreachable_x21___rarg(x_24);
x_26 = x_25;
x_27 = lean_array_fset(x_11, x_2, x_26);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_27;
goto _start;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous, possible interpretations ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_28__elabAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_2);
x_11 = l___private_Init_Lean_Elab_Term_24__elabAppFn___main(x_1, x_2, x_8, x_3, x_4, x_5, x_9, x_10, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_get_size(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
x_18 = l_Array_filterAux___main___at___private_Init_Lean_Elab_Term_25__getSuccess___spec__1(x_12, x_17, x_17);
x_19 = lean_array_get_size(x_18);
x_20 = lean_nat_dec_eq(x_19, x_15);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = lean_nat_dec_lt(x_15, x_19);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
x_22 = l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg(x_12, x_2, x_6, x_13);
lean_dec(x_2);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
x_23 = l_Lean_Elab_Term_getLCtx(x_6, x_13);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_Term_28__elabAppAux___spec__1(x_24, x_17, x_18);
x_27 = l_Lean_MessageData_ofArray(x_26);
lean_dec(x_26);
x_28 = l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__3;
x_29 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Elab_throwError___at_Lean_Elab_Term_elabTerm___spec__1(x_2, x_29, x_6, x_25);
lean_dec(x_6);
lean_dec(x_2);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_2);
x_31 = l_Lean_Elab_Term_TermElabResult_inhabited;
x_32 = lean_array_get(x_31, x_18, x_17);
lean_dec(x_18);
x_33 = l_Lean_Elab_Term_applyResult(x_32, x_6, x_13);
lean_dec(x_13);
lean_dec(x_6);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_34 = l_Lean_Elab_Term_TermElabResult_inhabited;
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get(x_34, x_12, x_35);
lean_dec(x_12);
x_37 = l_Lean_Elab_Term_applyResult(x_36, x_6, x_13);
lean_dec(x_13);
lean_dec(x_6);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
return x_11;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_28__elabAppAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Term_28__elabAppAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Term_29__expandAppAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = l_Lean_Parser_Term_app___elambda__1___closed__2;
x_6 = lean_name_eq(x_3, x_5);
lean_dec(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_reverseAux___main___rarg(x_2, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_10 = l_Lean_stxInh;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get(x_10, x_4, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_array_get(x_10, x_4, x_13);
lean_dec(x_4);
x_15 = lean_array_push(x_2, x_14);
x_1 = x_12;
x_2 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_reverseAux___main___rarg(x_2, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_Elab_Term_29__expandAppAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elab_Term_29__expandAppAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_30__expandApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
if (lean_obj_tag(x_10) == 1)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
x_18 = l_Lean_Parser_Term_namedArgument___elambda__1___rarg___closed__2;
x_19 = lean_name_eq(x_16, x_18);
lean_dec(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
x_20 = lean_array_push(x_15, x_10);
lean_ctor_set(x_4, 1, x_20);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = l_Lean_stxInh;
x_23 = lean_array_get(x_22, x_17, x_11);
x_24 = l_Lean_Syntax_getId(x_23);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(3u);
x_26 = lean_array_get(x_22, x_17, x_25);
lean_dec(x_17);
lean_inc(x_10);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_10);
x_28 = l_Lean_Elab_Term_addNamedArg(x_14, x_27, x_10, x_5, x_6);
lean_dec(x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_ctor_set(x_4, 0, x_29);
x_3 = x_12;
x_6 = x_30;
goto _start;
}
else
{
uint8_t x_32; 
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_12);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
x_38 = lean_ctor_get(x_10, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_10, 1);
lean_inc(x_39);
x_40 = l_Lean_Parser_Term_namedArgument___elambda__1___rarg___closed__2;
x_41 = lean_name_eq(x_38, x_40);
lean_dec(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_39);
x_42 = lean_array_push(x_37, x_10);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_42);
x_3 = x_12;
x_4 = x_43;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = l_Lean_stxInh;
x_46 = lean_array_get(x_45, x_39, x_11);
x_47 = l_Lean_Syntax_getId(x_46);
lean_dec(x_46);
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_array_get(x_45, x_39, x_48);
lean_dec(x_39);
lean_inc(x_10);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_10);
x_51 = l_Lean_Elab_Term_addNamedArg(x_36, x_50, x_10, x_5, x_6);
lean_dec(x_10);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_37);
x_3 = x_12;
x_4 = x_54;
x_6 = x_53;
goto _start;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_37);
lean_dec(x_12);
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
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
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_4);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_4, 1);
x_62 = lean_array_push(x_61, x_10);
lean_ctor_set(x_4, 1, x_62);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get(x_4, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_4);
x_66 = lean_array_push(x_65, x_10);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_3 = x_12;
x_4 = x_67;
goto _start;
}
}
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_30__expandApp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Term_30__expandApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Array_empty___closed__1;
x_5 = l___private_Init_Lean_Elab_Term_29__expandAppAux___main(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Lean_Elab_Term_30__expandApp___closed__1;
x_11 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_30__expandApp___spec__1(x_8, x_8, x_9, x_10, x_2, x_3);
lean_dec(x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_5, 1, x_13);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_5, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_free_object(x_5);
lean_dec(x_7);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l___private_Init_Lean_Elab_Term_30__expandApp___closed__1;
x_25 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_30__expandApp___spec__1(x_22, x_22, x_23, x_24, x_2, x_3);
lean_dec(x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_21);
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_33 = x_25;
} else {
 lean_dec_ref(x_25);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_30__expandApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_Term_30__expandApp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_Term_30__expandApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Term_30__expandApp(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l___private_Init_Lean_Elab_Term_30__expandApp(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l___private_Init_Lean_Elab_Term_28__elabAppAux(x_1, x_9, x_10, x_11, x_2, x_3, x_8);
lean_dec(x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabApp");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabApp), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_app___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabApp(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabId");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabId), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_id___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabApp(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabExplicit");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabExplicit), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabApp(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabChoice");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabChoice), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChoice(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_choiceKind___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabApp(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabProj");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__4;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabProj), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProj(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Term_31__regTraceClasses___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_1__regTraceClasses___closed__2;
x_2 = l_Lean_Parser_Term_app___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Term_31__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_Term_31__regTraceClasses___closed__1;
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
lean_object* initialize_Init_Lean_Util_Sorry(lean_object*);
lean_object* initialize_Init_Lean_Structure(lean_object*);
lean_object* initialize_Init_Lean_Meta(lean_object*);
lean_object* initialize_Init_Lean_Hygiene(lean_object*);
lean_object* initialize_Init_Lean_Elab_Log(lean_object*);
lean_object* initialize_Init_Lean_Elab_Alias(lean_object*);
lean_object* initialize_Init_Lean_Elab_ResolveName(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Term(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Util_Sorry(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Structure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Hygiene(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Log(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Alias(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_ResolveName(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_State_inhabited___closed__1 = _init_l_Lean_Elab_Term_State_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_State_inhabited___closed__1);
l_Lean_Elab_Term_State_inhabited___closed__2 = _init_l_Lean_Elab_Term_State_inhabited___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_State_inhabited___closed__2);
l_Lean_Elab_Term_State_inhabited = _init_l_Lean_Elab_Term_State_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_State_inhabited);
l_Lean_Elab_Term_TermElabM_inhabited___closed__1 = _init_l_Lean_Elab_Term_TermElabM_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_inhabited___closed__1);
l_Lean_Elab_Term_TermElabResult_inhabited___closed__1 = _init_l_Lean_Elab_Term_TermElabResult_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_TermElabResult_inhabited___closed__1);
l_Lean_Elab_Term_TermElabResult_inhabited = _init_l_Lean_Elab_Term_TermElabResult_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_TermElabResult_inhabited);
l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__1 = _init_l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__1);
l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__2 = _init_l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__2);
l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__3 = _init_l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__3);
l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__4 = _init_l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__4);
l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__5 = _init_l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_MonadQuotation___closed__5);
l_Lean_Elab_Term_TermElabM_MonadQuotation = _init_l_Lean_Elab_Term_TermElabM_MonadQuotation();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_MonadQuotation);
l_Lean_Elab_Term_TermElabM_monadLog___closed__1 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__1);
l_Lean_Elab_Term_TermElabM_monadLog___closed__2 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__2);
l_Lean_Elab_Term_TermElabM_monadLog___closed__3 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__3);
l_Lean_Elab_Term_TermElabM_monadLog___closed__4 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__4);
l_Lean_Elab_Term_TermElabM_monadLog___closed__5 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__5);
l_Lean_Elab_Term_TermElabM_monadLog___closed__6 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__6);
l_Lean_Elab_Term_TermElabM_monadLog___closed__7 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__7);
l_Lean_Elab_Term_TermElabM_monadLog___closed__8 = _init_l_Lean_Elab_Term_TermElabM_monadLog___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog___closed__8);
l_Lean_Elab_Term_TermElabM_monadLog = _init_l_Lean_Elab_Term_TermElabM_monadLog();
lean_mark_persistent(l_Lean_Elab_Term_TermElabM_monadLog);
l_PersistentHashMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__3 = _init_l_PersistentHashMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__3();
lean_mark_persistent(l_PersistentHashMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__3);
l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1 = _init_l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Term_mkBuiltinTermElabTable___spec__1);
res = l_Lean_Elab_Term_mkBuiltinTermElabTable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_builtinTermElabTable = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_builtinTermElabTable);
lean_dec_ref(res);
l_Lean_Elab_Term_addBuiltinTermElab___closed__1 = _init_l_Lean_Elab_Term_addBuiltinTermElab___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_addBuiltinTermElab___closed__1);
l_Lean_Elab_Term_addBuiltinTermElab___closed__2 = _init_l_Lean_Elab_Term_addBuiltinTermElab___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_addBuiltinTermElab___closed__2);
l_Lean_Elab_Term_declareBuiltinTermElab___closed__1 = _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_declareBuiltinTermElab___closed__1);
l_Lean_Elab_Term_declareBuiltinTermElab___closed__2 = _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_declareBuiltinTermElab___closed__2);
l_Lean_Elab_Term_declareBuiltinTermElab___closed__3 = _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_declareBuiltinTermElab___closed__3);
l_Lean_Elab_Term_declareBuiltinTermElab___closed__4 = _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_declareBuiltinTermElab___closed__4);
l_Lean_Elab_Term_declareBuiltinTermElab___closed__5 = _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_declareBuiltinTermElab___closed__5);
l_Lean_Elab_Term_declareBuiltinTermElab___closed__6 = _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_declareBuiltinTermElab___closed__6);
l_Lean_Elab_Term_declareBuiltinTermElab___closed__7 = _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_declareBuiltinTermElab___closed__7);
l_Lean_Elab_Term_declareBuiltinTermElab___closed__8 = _init_l_Lean_Elab_Term_declareBuiltinTermElab___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_declareBuiltinTermElab___closed__8);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__1);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__2);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__3);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___lambda__1___closed__4);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__1 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__1);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__2);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__3 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__3);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__4 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__4);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__5 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__5);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__6 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__6);
l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__7 = _init_l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_registerBuiltinTermElabAttr___closed__7);
res = l_Lean_Elab_Term_registerBuiltinTermElabAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__1();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__1);
l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__2 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__2();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_Elab_Term_mkTermElabAttribute___spec__4___closed__2);
l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1 = _init_l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_mkElabAttribute___at_Lean_Elab_Term_mkTermElabAttribute___spec__1___closed__1);
l_Lean_Elab_Term_mkTermElabAttribute___closed__1 = _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkTermElabAttribute___closed__1);
l_Lean_Elab_Term_mkTermElabAttribute___closed__2 = _init_l_Lean_Elab_Term_mkTermElabAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkTermElabAttribute___closed__2);
l_Lean_Elab_Term_termElabAttribute___closed__1 = _init_l_Lean_Elab_Term_termElabAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_termElabAttribute___closed__1);
l_Lean_Elab_Term_termElabAttribute___closed__2 = _init_l_Lean_Elab_Term_termElabAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_termElabAttribute___closed__2);
l_Lean_Elab_Term_termElabAttribute___closed__3 = _init_l_Lean_Elab_Term_termElabAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_termElabAttribute___closed__3);
res = l_Lean_Elab_Term_mkTermElabAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_termElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_termElabAttribute);
lean_dec_ref(res);
l_Lean_Elab_Term_tracer___closed__1 = _init_l_Lean_Elab_Term_tracer___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_tracer___closed__1);
l_Lean_Elab_Term_tracer___closed__2 = _init_l_Lean_Elab_Term_tracer___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_tracer___closed__2);
l_Lean_Elab_Term_tracer___closed__3 = _init_l_Lean_Elab_Term_tracer___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_tracer___closed__3);
l_Lean_Elab_Term_tracer___closed__4 = _init_l_Lean_Elab_Term_tracer___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_tracer___closed__4);
l_Lean_Elab_Term_tracer___closed__5 = _init_l_Lean_Elab_Term_tracer___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_tracer___closed__5);
l_Lean_Elab_Term_tracer = _init_l_Lean_Elab_Term_tracer();
lean_mark_persistent(l_Lean_Elab_Term_tracer);
l_Lean_Elab_Term_withNode___rarg___closed__1 = _init_l_Lean_Elab_Term_withNode___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_withNode___rarg___closed__1);
l_Lean_Elab_Term_withNode___rarg___closed__2 = _init_l_Lean_Elab_Term_withNode___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_withNode___rarg___closed__2);
l_Lean_Elab_Term_withNode___rarg___closed__3 = _init_l_Lean_Elab_Term_withNode___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_withNode___rarg___closed__3);
l_Lean_Elab_Term_exceptionToSorry___closed__1 = _init_l_Lean_Elab_Term_exceptionToSorry___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_exceptionToSorry___closed__1);
l_Lean_Elab_Term_exceptionToSorry___closed__2 = _init_l_Lean_Elab_Term_exceptionToSorry___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_exceptionToSorry___closed__2);
l_Lean_Elab_Term_exceptionToSorry___closed__3 = _init_l_Lean_Elab_Term_exceptionToSorry___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_exceptionToSorry___closed__3);
l_Lean_Elab_Term_elabTerm___closed__1 = _init_l_Lean_Elab_Term_elabTerm___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabTerm___closed__1);
l_Lean_Elab_Term_elabTerm___closed__2 = _init_l_Lean_Elab_Term_elabTerm___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabTerm___closed__2);
l_Lean_Elab_Term_elabTerm___closed__3 = _init_l_Lean_Elab_Term_elabTerm___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabTerm___closed__3);
l_Lean_Elab_Term_elabTerm___closed__4 = _init_l_Lean_Elab_Term_elabTerm___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabTerm___closed__4);
l_Lean_Elab_Term_elabTerm___closed__5 = _init_l_Lean_Elab_Term_elabTerm___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabTerm___closed__5);
l_Lean_Elab_Term_elabTerm___closed__6 = _init_l_Lean_Elab_Term_elabTerm___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_elabTerm___closed__6);
l_Lean_Elab_Term_elabTerm___closed__7 = _init_l_Lean_Elab_Term_elabTerm___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_elabTerm___closed__7);
l_Lean_Elab_Term_ensureType___closed__1 = _init_l_Lean_Elab_Term_ensureType___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_ensureType___closed__1);
l_Lean_Elab_Term_ensureType___closed__2 = _init_l_Lean_Elab_Term_ensureType___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_ensureType___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabProp___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabProp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabSort___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabSort(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabTypeStx___rarg___closed__1 = _init_l_Lean_Elab_Term_elabTypeStx___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabTypeStx___rarg___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabTypeStx(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabHole___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabHole(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg___closed__1 = _init_l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg___closed__1);
l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg___closed__2 = _init_l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_4__mkFreshAnonymousName___rarg___closed__2);
l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg___closed__1 = _init_l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg___closed__1);
l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg___closed__2 = _init_l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_5__mkFreshInstanceName___rarg___closed__2);
l_Lean_Elab_Term_mkHole___closed__1 = _init_l_Lean_Elab_Term_mkHole___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkHole___closed__1);
l_Lean_Elab_Term_mkHole___closed__2 = _init_l_Lean_Elab_Term_mkHole___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkHole___closed__2);
l_Lean_Elab_Term_mkHole___closed__3 = _init_l_Lean_Elab_Term_mkHole___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_mkHole___closed__3);
l_Lean_Elab_Term_mkHole = _init_l_Lean_Elab_Term_mkHole();
lean_mark_persistent(l_Lean_Elab_Term_mkHole);
l___private_Init_Lean_Elab_Term_9__matchBinder___closed__1 = _init_l___private_Init_Lean_Elab_Term_9__matchBinder___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_9__matchBinder___closed__1);
l___private_Init_Lean_Elab_Term_9__matchBinder___closed__2 = _init_l___private_Init_Lean_Elab_Term_9__matchBinder___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_9__matchBinder___closed__2);
l___private_Init_Lean_Elab_Term_9__matchBinder___closed__3 = _init_l___private_Init_Lean_Elab_Term_9__matchBinder___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_9__matchBinder___closed__3);
l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabForall___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabForall(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_mkExplicitBinder___closed__1 = _init_l_Lean_Elab_Term_mkExplicitBinder___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_mkExplicitBinder___closed__1);
l_Lean_Elab_Term_mkExplicitBinder___closed__2 = _init_l_Lean_Elab_Term_mkExplicitBinder___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_mkExplicitBinder___closed__2);
l_Lean_Elab_Term_mkExplicitBinder___closed__3 = _init_l_Lean_Elab_Term_mkExplicitBinder___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_mkExplicitBinder___closed__3);
l_Lean_Elab_Term_mkExplicitBinder___closed__4 = _init_l_Lean_Elab_Term_mkExplicitBinder___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_mkExplicitBinder___closed__4);
l_Lean_Elab_Term_mkExplicitBinder___closed__5 = _init_l_Lean_Elab_Term_mkExplicitBinder___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_mkExplicitBinder___closed__5);
l_Lean_Elab_Term_mkExplicitBinder___closed__6 = _init_l_Lean_Elab_Term_mkExplicitBinder___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_mkExplicitBinder___closed__6);
l_Lean_Elab_Term_elabArrow___closed__1 = _init_l_Lean_Elab_Term_elabArrow___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___closed__1);
l_Lean_Elab_Term_elabArrow___closed__2 = _init_l_Lean_Elab_Term_elabArrow___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___closed__2);
l_Lean_Elab_Term_elabArrow___closed__3 = _init_l_Lean_Elab_Term_elabArrow___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabArrow___closed__3);
l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabArrow___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabArrow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabDepArrow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabParen___closed__1 = _init_l_Lean_Elab_Term_elabParen___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__1);
l_Lean_Elab_Term_elabParen___closed__2 = _init_l_Lean_Elab_Term_elabParen___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__2);
l_Lean_Elab_Term_elabParen___closed__3 = _init_l_Lean_Elab_Term_elabParen___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabParen___closed__3);
l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabParen___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabParen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabListLit___closed__1 = _init_l_Lean_Elab_Term_elabListLit___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabListLit___closed__1);
l_Lean_Elab_Term_elabListLit___closed__2 = _init_l_Lean_Elab_Term_elabListLit___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabListLit___closed__2);
l_Lean_Elab_Term_elabListLit___closed__3 = _init_l_Lean_Elab_Term_elabListLit___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabListLit___closed__3);
l_Lean_Elab_Term_elabListLit___closed__4 = _init_l_Lean_Elab_Term_elabListLit___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabListLit___closed__4);
l_Lean_Elab_Term_elabListLit___closed__5 = _init_l_Lean_Elab_Term_elabListLit___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_elabListLit___closed__5);
l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabListLit___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabListLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_NamedArg_inhabited___closed__1 = _init_l_Lean_Elab_Term_NamedArg_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_NamedArg_inhabited___closed__1);
l_Lean_Elab_Term_NamedArg_inhabited = _init_l_Lean_Elab_Term_NamedArg_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_NamedArg_inhabited);
l_Lean_Elab_Term_addNamedArg___closed__1 = _init_l_Lean_Elab_Term_addNamedArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__1);
l_Lean_Elab_Term_addNamedArg___closed__2 = _init_l_Lean_Elab_Term_addNamedArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__2);
l_Lean_Elab_Term_addNamedArg___closed__3 = _init_l_Lean_Elab_Term_addNamedArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__3);
l_Lean_Elab_Term_addNamedArg___closed__4 = _init_l_Lean_Elab_Term_addNamedArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__4);
l_Lean_Elab_Term_addNamedArg___closed__5 = _init_l_Lean_Elab_Term_addNamedArg___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__5);
l_Lean_Elab_Term_addNamedArg___closed__6 = _init_l_Lean_Elab_Term_addNamedArg___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__6);
l_List_foldlM___main___at___private_Init_Lean_Elab_Term_15__mkConsts___spec__1___closed__1 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_Term_15__mkConsts___spec__1___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_Term_15__mkConsts___spec__1___closed__1);
l_Lean_Elab_Term_resolveName___closed__1 = _init_l_Lean_Elab_Term_resolveName___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__1);
l_Lean_Elab_Term_resolveName___closed__2 = _init_l_Lean_Elab_Term_resolveName___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__2);
l_Lean_Elab_Term_resolveName___closed__3 = _init_l_Lean_Elab_Term_resolveName___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__3);
l_Lean_Elab_Term_resolveName___closed__4 = _init_l_Lean_Elab_Term_resolveName___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__4);
l_Lean_Elab_Term_resolveName___closed__5 = _init_l_Lean_Elab_Term_resolveName___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__5);
l_Lean_Elab_Term_resolveName___closed__6 = _init_l_Lean_Elab_Term_resolveName___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__6);
l_Lean_Elab_Term_resolveName___closed__7 = _init_l_Lean_Elab_Term_resolveName___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__7);
l_Lean_Elab_Term_resolveName___closed__8 = _init_l_Lean_Elab_Term_resolveName___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__8);
l_Lean_Elab_Term_resolveName___closed__9 = _init_l_Lean_Elab_Term_resolveName___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__9);
l_Lean_Elab_Term_resolveName___closed__10 = _init_l_Lean_Elab_Term_resolveName___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__10);
l_Lean_Elab_Term_resolveName___closed__11 = _init_l_Lean_Elab_Term_resolveName___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__11);
l_Lean_Elab_Term_resolveName___closed__12 = _init_l_Lean_Elab_Term_resolveName___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__12);
l_Lean_Elab_Term_resolveName___closed__13 = _init_l_Lean_Elab_Term_resolveName___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__13);
l_Lean_Elab_Term_resolveName___closed__14 = _init_l_Lean_Elab_Term_resolveName___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_resolveName___closed__14);
l_Lean_Elab_Term_ensureHasType___closed__1 = _init_l_Lean_Elab_Term_ensureHasType___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_ensureHasType___closed__1);
l_Lean_Elab_Term_ensureHasType___closed__2 = _init_l_Lean_Elab_Term_ensureHasType___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_ensureHasType___closed__2);
l_Lean_Elab_Term_ensureHasType___closed__3 = _init_l_Lean_Elab_Term_ensureHasType___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_ensureHasType___closed__3);
l_Lean_Elab_Term_synthesizeInstMVar___closed__1 = _init_l_Lean_Elab_Term_synthesizeInstMVar___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeInstMVar___closed__1);
l_Lean_Elab_Term_synthesizeInstMVar___closed__2 = _init_l_Lean_Elab_Term_synthesizeInstMVar___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeInstMVar___closed__2);
l_Lean_Elab_Term_synthesizeInstMVar___closed__3 = _init_l_Lean_Elab_Term_synthesizeInstMVar___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_synthesizeInstMVar___closed__3);
l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__1 = _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__1);
l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__2 = _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__2);
l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__3 = _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__3);
l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__4 = _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__4);
l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__5 = _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__5);
l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__6 = _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__6);
l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__7 = _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__7);
l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__8 = _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__8();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__8);
l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__9 = _init_l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__9();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_16__elabAppArgsAux___main___closed__9);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__1 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__1);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__2 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__2);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__3 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__3);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__4 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__4);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__5 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__5);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__6 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__6);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__7 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__7);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__8 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__8();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__8);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__9 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__9();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__9);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__10 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__10();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__10);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__11 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__11();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__11);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__12 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__12();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__12);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__13 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__13();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__13);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__14 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__14();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__14);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__15 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__15();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__15);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__16 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__16();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__16);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__17 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__17();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__17);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__18);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__19 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__19();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__19);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__20 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__20();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__20);
l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21 = _init_l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_19__resolveFieldAux___closed__21);
l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__1 = _init_l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__1);
l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__2 = _init_l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__2);
l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__3 = _init_l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_23__elabAppFields___closed__3);
l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__1 = _init_l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__1);
l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__2 = _init_l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__2);
l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__3 = _init_l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_24__elabAppFn___main___closed__3);
l___private_Init_Lean_Elab_Term_26__toMessageData___closed__1 = _init_l___private_Init_Lean_Elab_Term_26__toMessageData___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_26__toMessageData___closed__1);
l___private_Init_Lean_Elab_Term_26__toMessageData___closed__2 = _init_l___private_Init_Lean_Elab_Term_26__toMessageData___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_26__toMessageData___closed__2);
l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__1 = _init_l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__1);
l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__2 = _init_l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__2);
l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__3 = _init_l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_27__mergeFailures___rarg___closed__3);
l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__1 = _init_l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__1);
l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__2 = _init_l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__2);
l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__3 = _init_l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_28__elabAppAux___closed__3);
l___private_Init_Lean_Elab_Term_30__expandApp___closed__1 = _init_l___private_Init_Lean_Elab_Term_30__expandApp___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_30__expandApp___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabApp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabId(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabChoice(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabProj(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Elab_Term_31__regTraceClasses___closed__1 = _init_l___private_Init_Lean_Elab_Term_31__regTraceClasses___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Term_31__regTraceClasses___closed__1);
res = l___private_Init_Lean_Elab_Term_31__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
