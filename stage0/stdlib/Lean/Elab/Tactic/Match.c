// Lean compiler output
// Module: Lean.Elab.Tactic.Match
// Imports: Init Lean.Parser.Term Lean.Elab.Match Lean.Elab.Tactic.Basic Lean.Elab.Tactic.Induction
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
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15342____closed__13;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalMatch(lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo_x3f(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Elab_Tactic_adaptExpander___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_18139____closed__5;
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20311____closed__5;
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_adaptExpander___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_AuxMatchTermState_cases___default;
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_match__1(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalMatch___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__4;
size_t l_USize_shiftRight(size_t, size_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalMatch___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
uint8_t l_USize_decLt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__2;
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__5;
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalMatch___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_groupKind___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__1;
uint8_t l_Lean_Elab_Term_isAuxDiscrName(lean_object*);
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_stx___x3f___closed__3;
lean_object* l_Lean_Elab_Tactic_evalMatch_match__1(lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalMatch___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__3;
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs___closed__1;
extern lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___closed__1;
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_16821____closed__12;
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_9577____closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalMatch___closed__1;
extern lean_object* l_Lean_Parser_Tactic_paren___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Elab_Tactic_AuxMatchTermState_nextIdx___default;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_refine___closed__1;
lean_object* l_Lean_Elab_Tactic_evalMatch_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_refine___closed__2;
lean_object* l_List_forM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_case___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_match___elambda__1___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___boxed__const__1;
extern lean_object* l_Lean_Parser_Tactic_case___closed__2;
lean_object* l_Lean_LocalContext_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___closed__1;
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___boxed(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__5(lean_object*, size_t, size_t, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_focusAndDone___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_liftMacroM___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_18139____closed__3;
extern lean_object* l_prec_x28___x29___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Std_PersistentArray_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3___rarg(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Std_PersistentArray_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs(lean_object*);
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__4___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_getAux___rarg___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__4(x_6, x_4);
lean_dec(x_6);
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
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = x_2 + x_7;
if (lean_obj_tag(x_6) == 0)
{
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_userName(x_10);
x_12 = l_Lean_Elab_Term_isAuxDiscrName(x_11);
if (x_12 == 0)
{
lean_dec(x_10);
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
x_2 = x_8;
x_4 = x_15;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__5(x_3, x_8, x_9, x_2);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
return x_2;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_12, x_12);
if (x_15 == 0)
{
lean_dec(x_12);
return x_2;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6(x_11, x_16, x_17, x_2);
return x_18;
}
}
}
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = x_2 >> x_3 % (sizeof(size_t) * 8);
x_7 = lean_usize_to_nat(x_6);
x_8 = l_Std_PersistentArray_getAux___rarg___closed__1;
x_9 = lean_array_get(x_8, x_5, x_7);
x_10 = 1;
x_11 = x_10 << x_3 % (sizeof(size_t) * 8);
x_12 = x_11 - x_10;
x_13 = x_2 & x_12;
x_14 = 5;
x_15 = x_3 - x_14;
x_16 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__3(x_9, x_13, x_15, x_4);
lean_dec(x_9);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_7, x_17);
lean_dec(x_7);
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__5(x_5, x_22, x_23, x_16);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_usize_to_nat(x_2);
x_27 = lean_array_get_size(x_25);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6(x_25, x_30, x_31, x_4);
return x_32;
}
}
}
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_nat_dec_le(x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_usize_of_nat(x_3);
x_10 = lean_ctor_get_usize(x_1, 4);
x_11 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__3(x_8, x_9, x_10, x_2);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_4, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
return x_11;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
return x_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6(x_12, x_16, x_17, x_11);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_nat_sub(x_3, x_6);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_2;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6(x_19, x_24, x_25, x_2);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__4(x_27, x_2);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_4, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
return x_28;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
return x_28;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_35 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6(x_29, x_33, x_34, x_28);
return x_35;
}
}
}
}
}
lean_object* l_Lean_LocalContext_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Std_PersistentArray_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__2(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Meta_tryClear(x_2, x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_1 = x_14;
x_2 = x_16;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
}
}
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_LocalContext_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__1(x_1, x_11, x_12);
x_14 = l_Lean_Elab_Tactic_getMainGoal(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_List_forIn_loop___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__7(x_13, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_11);
x_21 = l_Lean_Elab_Tactic_replaceMainGoal(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
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
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
static lean_object* _init_l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___lambda__1___boxed), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___closed__1;
x_2 = l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_focusAndDone___spec__1___rarg), 11, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___closed__2;
x_11 = l_Lean_Elab_Tactic_withMainContext___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__6(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__4(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Std_PersistentArray_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentArray_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_LocalContext_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_LocalContext_foldlM___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at_Lean_Elab_Tactic_evalEraseAuxDiscrs___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_evalEraseAuxDiscrs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalEraseAuxDiscrs(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalEraseAuxDiscrs___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_AuxMatchTermState_nextIdx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_AuxMatchTermState_cases___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 5);
x_5 = l_Lean_SourceInfo_fromRef(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rhs");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_4 < x_3;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_1);
x_10 = x_5;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_13 = lean_array_uget(x_5, x_4);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_5, x_4, x_14);
x_26 = x_13;
x_27 = l_myMacro____x40_Init_Notation___hyg_15342____closed__10;
x_28 = l_Lean_Syntax_setKind(x_26, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = l_Lean_Syntax_getArg(x_28, x_29);
x_31 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_20311____closed__5;
lean_inc(x_30);
x_32 = l_Lean_Syntax_isOfKind(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_myMacro____x40_Init_Notation___hyg_15342____closed__13;
lean_inc(x_30);
x_34 = l_Lean_Syntax_isOfKind(x_30, x_33);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_36, x_37);
lean_ctor_set(x_8, 0, x_38);
x_39 = lean_ctor_get(x_7, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_7, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_7, 4);
lean_inc(x_42);
x_43 = lean_ctor_get(x_7, 5);
lean_inc(x_43);
lean_inc(x_36);
lean_inc(x_40);
x_44 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_44, 2, x_36);
lean_ctor_set(x_44, 3, x_41);
lean_ctor_set(x_44, 4, x_42);
lean_ctor_set(x_44, 5, x_43);
x_45 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1(x_6, x_44, x_8);
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
x_50 = l_stx___x3f___closed__3;
lean_inc(x_48);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Array_empty___closed__1;
x_53 = lean_array_push(x_52, x_51);
x_54 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__4;
x_55 = l_Lean_addMacroScope(x_40, x_54, x_36);
x_56 = lean_box(0);
x_57 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__3;
x_58 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_58, 2, x_55);
lean_ctor_set(x_58, 3, x_56);
x_59 = lean_array_push(x_53, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_31);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Syntax_getArg(x_60, x_37);
x_62 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1(x_49, x_44, x_47);
lean_dec(x_44);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
x_68 = l_Lean_Parser_Tactic_case___closed__1;
lean_inc(x_66);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_array_push(x_52, x_69);
x_71 = lean_array_push(x_70, x_61);
x_72 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_73 = lean_array_push(x_71, x_72);
x_74 = lean_unsigned_to_nat(2u);
x_75 = l_Lean_Syntax_getArg(x_28, x_74);
x_76 = l_Lean_Syntax_getHeadInfo_x3f(x_75);
lean_dec(x_75);
x_77 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__5;
lean_inc(x_66);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_66);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_array_push(x_52, x_78);
x_80 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_array_push(x_52, x_81);
x_83 = l_myMacro____x40_Init_Notation___hyg_16821____closed__12;
lean_inc(x_66);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_66);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_array_push(x_52, x_84);
x_86 = l_Lean_nullKind___closed__2;
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_array_push(x_82, x_87);
x_89 = l_Lean_groupKind___closed__2;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_array_push(x_52, x_90);
x_92 = l_prec_x28___x29___closed__3;
lean_inc(x_66);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_66);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_array_push(x_52, x_93);
x_95 = lean_array_push(x_94, x_30);
x_96 = l_prec_x28___x29___closed__7;
lean_inc(x_66);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_66);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_array_push(x_95, x_97);
x_99 = l_Lean_Parser_Tactic_paren___closed__1;
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = lean_array_push(x_52, x_100);
x_102 = lean_array_push(x_101, x_72);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_89);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_array_push(x_91, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_86);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_array_push(x_52, x_105);
x_107 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_18139____closed__5;
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_array_push(x_52, x_108);
x_110 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_18139____closed__3;
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_112 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_113 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_113, 0, x_66);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_array_push(x_73, x_113);
x_115 = lean_array_push(x_114, x_111);
x_116 = l_Lean_Parser_Tactic_case___closed__2;
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = !lean_is_exclusive(x_67);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_67, 1);
x_120 = lean_array_push(x_119, x_117);
lean_ctor_set(x_67, 1, x_120);
x_121 = l_Lean_Syntax_setArg(x_28, x_29, x_60);
lean_ctor_set(x_63, 0, x_121);
x_16 = x_63;
x_17 = x_64;
goto block_25;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_67, 0);
x_123 = lean_ctor_get(x_67, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_67);
x_124 = lean_array_push(x_123, x_117);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_Syntax_setArg(x_28, x_29, x_60);
lean_ctor_set(x_63, 1, x_125);
lean_ctor_set(x_63, 0, x_126);
x_16 = x_63;
x_17 = x_64;
goto block_25;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
lean_dec(x_66);
x_127 = lean_ctor_get(x_76, 0);
lean_inc(x_127);
lean_dec(x_76);
x_128 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_array_push(x_73, x_129);
x_131 = lean_array_push(x_130, x_111);
x_132 = l_Lean_Parser_Tactic_case___closed__2;
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = !lean_is_exclusive(x_67);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_67, 1);
x_136 = lean_array_push(x_135, x_133);
lean_ctor_set(x_67, 1, x_136);
x_137 = l_Lean_Syntax_setArg(x_28, x_29, x_60);
lean_ctor_set(x_63, 0, x_137);
x_16 = x_63;
x_17 = x_64;
goto block_25;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_67, 0);
x_139 = lean_ctor_get(x_67, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_67);
x_140 = lean_array_push(x_139, x_133);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_Syntax_setArg(x_28, x_29, x_60);
lean_ctor_set(x_63, 1, x_141);
lean_ctor_set(x_63, 0, x_142);
x_16 = x_63;
x_17 = x_64;
goto block_25;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_143 = lean_ctor_get(x_63, 0);
x_144 = lean_ctor_get(x_63, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_63);
x_145 = l_Lean_Parser_Tactic_case___closed__1;
lean_inc(x_143);
x_146 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_array_push(x_52, x_146);
x_148 = lean_array_push(x_147, x_61);
x_149 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_150 = lean_array_push(x_148, x_149);
x_151 = lean_unsigned_to_nat(2u);
x_152 = l_Lean_Syntax_getArg(x_28, x_151);
x_153 = l_Lean_Syntax_getHeadInfo_x3f(x_152);
lean_dec(x_152);
x_154 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__5;
lean_inc(x_143);
x_155 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_155, 0, x_143);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_array_push(x_52, x_155);
x_157 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = lean_array_push(x_52, x_158);
x_160 = l_myMacro____x40_Init_Notation___hyg_16821____closed__12;
lean_inc(x_143);
x_161 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_161, 0, x_143);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_array_push(x_52, x_161);
x_163 = l_Lean_nullKind___closed__2;
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_165 = lean_array_push(x_159, x_164);
x_166 = l_Lean_groupKind___closed__2;
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
x_168 = lean_array_push(x_52, x_167);
x_169 = l_prec_x28___x29___closed__3;
lean_inc(x_143);
x_170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_170, 0, x_143);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_array_push(x_52, x_170);
x_172 = lean_array_push(x_171, x_30);
x_173 = l_prec_x28___x29___closed__7;
lean_inc(x_143);
x_174 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_174, 0, x_143);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_array_push(x_172, x_174);
x_176 = l_Lean_Parser_Tactic_paren___closed__1;
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
x_178 = lean_array_push(x_52, x_177);
x_179 = lean_array_push(x_178, x_149);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_166);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_array_push(x_168, x_180);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_163);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_array_push(x_52, x_182);
x_184 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_18139____closed__5;
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
x_186 = lean_array_push(x_52, x_185);
x_187 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_18139____closed__3;
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_186);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_189 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_190 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_190, 0, x_143);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_array_push(x_150, x_190);
x_192 = lean_array_push(x_191, x_188);
x_193 = l_Lean_Parser_Tactic_case___closed__2;
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = lean_ctor_get(x_144, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_144, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_197 = x_144;
} else {
 lean_dec_ref(x_144);
 x_197 = lean_box(0);
}
x_198 = lean_array_push(x_196, x_194);
if (lean_is_scalar(x_197)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_197;
}
lean_ctor_set(x_199, 0, x_195);
lean_ctor_set(x_199, 1, x_198);
x_200 = l_Lean_Syntax_setArg(x_28, x_29, x_60);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
x_16 = x_201;
x_17 = x_64;
goto block_25;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_143);
x_202 = lean_ctor_get(x_153, 0);
lean_inc(x_202);
lean_dec(x_153);
x_203 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_204 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_array_push(x_150, x_204);
x_206 = lean_array_push(x_205, x_188);
x_207 = l_Lean_Parser_Tactic_case___closed__2;
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
x_209 = lean_ctor_get(x_144, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_144, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_211 = x_144;
} else {
 lean_dec_ref(x_144);
 x_211 = lean_box(0);
}
x_212 = lean_array_push(x_210, x_208);
if (lean_is_scalar(x_211)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_211;
}
lean_ctor_set(x_213, 0, x_209);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_Lean_Syntax_setArg(x_28, x_29, x_60);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_213);
x_16 = x_215;
x_17 = x_64;
goto block_25;
}
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_216 = lean_ctor_get(x_8, 0);
x_217 = lean_ctor_get(x_8, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_8);
x_218 = lean_unsigned_to_nat(1u);
x_219 = lean_nat_add(x_216, x_218);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_217);
x_221 = lean_ctor_get(x_7, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_7, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_7, 3);
lean_inc(x_223);
x_224 = lean_ctor_get(x_7, 4);
lean_inc(x_224);
x_225 = lean_ctor_get(x_7, 5);
lean_inc(x_225);
lean_inc(x_216);
lean_inc(x_222);
x_226 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_226, 0, x_221);
lean_ctor_set(x_226, 1, x_222);
lean_ctor_set(x_226, 2, x_216);
lean_ctor_set(x_226, 3, x_223);
lean_ctor_set(x_226, 4, x_224);
lean_ctor_set(x_226, 5, x_225);
x_227 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1(x_6, x_226, x_220);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_ctor_get(x_228, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_228, 1);
lean_inc(x_231);
lean_dec(x_228);
x_232 = l_stx___x3f___closed__3;
lean_inc(x_230);
x_233 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_232);
x_234 = l_Array_empty___closed__1;
x_235 = lean_array_push(x_234, x_233);
x_236 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__4;
x_237 = l_Lean_addMacroScope(x_222, x_236, x_216);
x_238 = lean_box(0);
x_239 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__3;
x_240 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_240, 0, x_230);
lean_ctor_set(x_240, 1, x_239);
lean_ctor_set(x_240, 2, x_237);
lean_ctor_set(x_240, 3, x_238);
x_241 = lean_array_push(x_235, x_240);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_31);
lean_ctor_set(x_242, 1, x_241);
x_243 = l_Lean_Syntax_getArg(x_242, x_218);
x_244 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1(x_231, x_226, x_229);
lean_dec(x_226);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = lean_ctor_get(x_245, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_245, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_249 = x_245;
} else {
 lean_dec_ref(x_245);
 x_249 = lean_box(0);
}
x_250 = l_Lean_Parser_Tactic_case___closed__1;
lean_inc(x_247);
x_251 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_251, 0, x_247);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_array_push(x_234, x_251);
x_253 = lean_array_push(x_252, x_243);
x_254 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_255 = lean_array_push(x_253, x_254);
x_256 = lean_unsigned_to_nat(2u);
x_257 = l_Lean_Syntax_getArg(x_28, x_256);
x_258 = l_Lean_Syntax_getHeadInfo_x3f(x_257);
lean_dec(x_257);
x_259 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__5;
lean_inc(x_247);
x_260 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_260, 0, x_247);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_array_push(x_234, x_260);
x_262 = l_Lean_Parser_Tactic_eraseAuxDiscrs___elambda__1___closed__2;
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_261);
x_264 = lean_array_push(x_234, x_263);
x_265 = l_myMacro____x40_Init_Notation___hyg_16821____closed__12;
lean_inc(x_247);
x_266 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_266, 0, x_247);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_array_push(x_234, x_266);
x_268 = l_Lean_nullKind___closed__2;
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
x_270 = lean_array_push(x_264, x_269);
x_271 = l_Lean_groupKind___closed__2;
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_270);
x_273 = lean_array_push(x_234, x_272);
x_274 = l_prec_x28___x29___closed__3;
lean_inc(x_247);
x_275 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_275, 0, x_247);
lean_ctor_set(x_275, 1, x_274);
x_276 = lean_array_push(x_234, x_275);
x_277 = lean_array_push(x_276, x_30);
x_278 = l_prec_x28___x29___closed__7;
lean_inc(x_247);
x_279 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_279, 0, x_247);
lean_ctor_set(x_279, 1, x_278);
x_280 = lean_array_push(x_277, x_279);
x_281 = l_Lean_Parser_Tactic_paren___closed__1;
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_280);
x_283 = lean_array_push(x_234, x_282);
x_284 = lean_array_push(x_283, x_254);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_271);
lean_ctor_set(x_285, 1, x_284);
x_286 = lean_array_push(x_273, x_285);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_268);
lean_ctor_set(x_287, 1, x_286);
x_288 = lean_array_push(x_234, x_287);
x_289 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_18139____closed__5;
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_288);
x_291 = lean_array_push(x_234, x_290);
x_292 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_18139____closed__3;
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_294 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_295 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_295, 0, x_247);
lean_ctor_set(x_295, 1, x_294);
x_296 = lean_array_push(x_255, x_295);
x_297 = lean_array_push(x_296, x_293);
x_298 = l_Lean_Parser_Tactic_case___closed__2;
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_297);
x_300 = lean_ctor_get(x_248, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_248, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_302 = x_248;
} else {
 lean_dec_ref(x_248);
 x_302 = lean_box(0);
}
x_303 = lean_array_push(x_301, x_299);
if (lean_is_scalar(x_302)) {
 x_304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_304 = x_302;
}
lean_ctor_set(x_304, 0, x_300);
lean_ctor_set(x_304, 1, x_303);
x_305 = l_Lean_Syntax_setArg(x_28, x_29, x_242);
if (lean_is_scalar(x_249)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_249;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_304);
x_16 = x_306;
x_17 = x_246;
goto block_25;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_247);
x_307 = lean_ctor_get(x_258, 0);
lean_inc(x_307);
lean_dec(x_258);
x_308 = l_myMacro____x40_Init_Notation___hyg_14734____closed__13;
x_309 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_array_push(x_255, x_309);
x_311 = lean_array_push(x_310, x_293);
x_312 = l_Lean_Parser_Tactic_case___closed__2;
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_311);
x_314 = lean_ctor_get(x_248, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_248, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_316 = x_248;
} else {
 lean_dec_ref(x_248);
 x_316 = lean_box(0);
}
x_317 = lean_array_push(x_315, x_313);
if (lean_is_scalar(x_316)) {
 x_318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_318 = x_316;
}
lean_ctor_set(x_318, 0, x_314);
lean_ctor_set(x_318, 1, x_317);
x_319 = l_Lean_Syntax_setArg(x_28, x_29, x_242);
if (lean_is_scalar(x_249)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_249;
}
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_318);
x_16 = x_320;
x_17 = x_246;
goto block_25;
}
}
}
else
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; 
x_321 = lean_array_get_size(x_2);
x_322 = lean_unsigned_to_nat(1u);
x_323 = lean_nat_dec_lt(x_322, x_321);
lean_dec(x_321);
lean_inc(x_6);
x_324 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1(x_6, x_7, x_8);
if (x_323 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
lean_dec(x_6);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
lean_inc(x_1);
x_327 = l_Lean_mkIdentFrom(x_30, x_1);
lean_dec(x_30);
x_328 = !lean_is_exclusive(x_325);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_329 = lean_ctor_get(x_325, 0);
x_330 = lean_ctor_get(x_325, 1);
x_331 = l_stx___x3f___closed__3;
x_332 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_331);
x_333 = l_Array_empty___closed__1;
x_334 = lean_array_push(x_333, x_332);
x_335 = lean_array_push(x_334, x_327);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_31);
lean_ctor_set(x_336, 1, x_335);
x_337 = !lean_is_exclusive(x_330);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_330, 0);
x_339 = lean_nat_add(x_338, x_322);
lean_dec(x_338);
lean_ctor_set(x_330, 0, x_339);
x_340 = l_Lean_Syntax_setArg(x_28, x_29, x_336);
lean_ctor_set(x_325, 0, x_340);
x_16 = x_325;
x_17 = x_326;
goto block_25;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_341 = lean_ctor_get(x_330, 0);
x_342 = lean_ctor_get(x_330, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_330);
x_343 = lean_nat_add(x_341, x_322);
lean_dec(x_341);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_342);
x_345 = l_Lean_Syntax_setArg(x_28, x_29, x_336);
lean_ctor_set(x_325, 1, x_344);
lean_ctor_set(x_325, 0, x_345);
x_16 = x_325;
x_17 = x_326;
goto block_25;
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_346 = lean_ctor_get(x_325, 0);
x_347 = lean_ctor_get(x_325, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_325);
x_348 = l_stx___x3f___closed__3;
x_349 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_349, 0, x_346);
lean_ctor_set(x_349, 1, x_348);
x_350 = l_Array_empty___closed__1;
x_351 = lean_array_push(x_350, x_349);
x_352 = lean_array_push(x_351, x_327);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_31);
lean_ctor_set(x_353, 1, x_352);
x_354 = lean_ctor_get(x_347, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_347, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_356 = x_347;
} else {
 lean_dec_ref(x_347);
 x_356 = lean_box(0);
}
x_357 = lean_nat_add(x_354, x_322);
lean_dec(x_354);
if (lean_is_scalar(x_356)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_356;
}
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_355);
x_359 = l_Lean_Syntax_setArg(x_28, x_29, x_353);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_358);
x_16 = x_360;
x_17 = x_326;
goto block_25;
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_361 = lean_ctor_get(x_324, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_324, 1);
lean_inc(x_362);
lean_dec(x_324);
x_363 = lean_ctor_get(x_6, 0);
lean_inc(x_363);
lean_dec(x_6);
x_364 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_Match___hyg_9577____closed__1;
x_365 = lean_name_append_index_after(x_364, x_363);
x_366 = l_Lean_Name_append(x_1, x_365);
x_367 = l_Lean_mkIdentFrom(x_30, x_366);
lean_dec(x_30);
x_368 = !lean_is_exclusive(x_361);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; 
x_369 = lean_ctor_get(x_361, 0);
x_370 = lean_ctor_get(x_361, 1);
x_371 = l_stx___x3f___closed__3;
x_372 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_371);
x_373 = l_Array_empty___closed__1;
x_374 = lean_array_push(x_373, x_372);
x_375 = lean_array_push(x_374, x_367);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_31);
lean_ctor_set(x_376, 1, x_375);
x_377 = !lean_is_exclusive(x_370);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_370, 0);
x_379 = lean_nat_add(x_378, x_322);
lean_dec(x_378);
lean_ctor_set(x_370, 0, x_379);
x_380 = l_Lean_Syntax_setArg(x_28, x_29, x_376);
lean_ctor_set(x_361, 0, x_380);
x_16 = x_361;
x_17 = x_362;
goto block_25;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_381 = lean_ctor_get(x_370, 0);
x_382 = lean_ctor_get(x_370, 1);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_370);
x_383 = lean_nat_add(x_381, x_322);
lean_dec(x_381);
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_382);
x_385 = l_Lean_Syntax_setArg(x_28, x_29, x_376);
lean_ctor_set(x_361, 1, x_384);
lean_ctor_set(x_361, 0, x_385);
x_16 = x_361;
x_17 = x_362;
goto block_25;
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_386 = lean_ctor_get(x_361, 0);
x_387 = lean_ctor_get(x_361, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_361);
x_388 = l_stx___x3f___closed__3;
x_389 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_388);
x_390 = l_Array_empty___closed__1;
x_391 = lean_array_push(x_390, x_389);
x_392 = lean_array_push(x_391, x_367);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_31);
lean_ctor_set(x_393, 1, x_392);
x_394 = lean_ctor_get(x_387, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_387, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_396 = x_387;
} else {
 lean_dec_ref(x_387);
 x_396 = lean_box(0);
}
x_397 = lean_nat_add(x_394, x_322);
lean_dec(x_394);
if (lean_is_scalar(x_396)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_396;
}
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_395);
x_399 = l_Lean_Syntax_setArg(x_28, x_29, x_393);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_398);
x_16 = x_400;
x_17 = x_362;
goto block_25;
}
}
}
}
else
{
lean_object* x_401; 
lean_dec(x_30);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_28);
lean_ctor_set(x_401, 1, x_6);
x_16 = x_401;
x_17 = x_8;
goto block_25;
}
block_25:
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = 1;
x_21 = x_4 + x_20;
x_22 = x_18;
x_23 = lean_array_uset(x_15, x_4, x_22);
x_4 = x_21;
x_5 = x_23;
x_6 = x_19;
x_8 = x_17;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_unsigned_to_nat(5u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = lean_array_get_size(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
lean_inc(x_10);
x_13 = x_10;
x_14 = lean_box_usize(x_12);
x_15 = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___boxed__const__1;
x_16 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___boxed), 8, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_10);
lean_closure_set(x_16, 2, x_14);
lean_closure_set(x_16, 3, x_15);
lean_closure_set(x_16, 4, x_13);
x_17 = x_16;
x_18 = lean_apply_3(x_17, x_3, x_4, x_5);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_24 = l_Lean_Syntax_setKind(x_2, x_23);
x_25 = l_Lean_nullKind;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = l_Lean_mkOptionalNode___closed__2;
x_28 = lean_array_push(x_27, x_26);
x_29 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Syntax_setArg(x_24, x_6, x_30);
lean_ctor_set(x_20, 0, x_31);
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_34 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_35 = l_Lean_Syntax_setKind(x_2, x_34);
x_36 = l_Lean_nullKind;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
x_38 = l_Lean_mkOptionalNode___closed__2;
x_39 = lean_array_push(x_38, x_37);
x_40 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Syntax_setArg(x_35, x_6, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
lean_ctor_set(x_18, 0, x_43);
return x_18;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_18, 0);
x_45 = lean_ctor_get(x_18, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_18);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_48 = x_44;
} else {
 lean_dec_ref(x_44);
 x_48 = lean_box(0);
}
x_49 = l_myMacro____x40_Init_Notation___hyg_15342____closed__2;
x_50 = l_Lean_Syntax_setKind(x_2, x_49);
x_51 = l_Lean_nullKind;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_46);
x_53 = l_Lean_mkOptionalNode___closed__2;
x_54 = lean_array_push(x_53, x_52);
x_55 = l_myMacro____x40_Init_Notation___hyg_15342____closed__8;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Syntax_setArg(x_50, x_6, x_56);
if (lean_is_scalar(x_48)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_48;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_47);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_45);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_18);
if (x_60 == 0)
{
return x_18;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_18, 0);
x_62 = lean_ctor_get(x_18, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_18);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_match__1___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1;
x_6 = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux(x_1, x_2, x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
lean_ctor_set(x_7, 1, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_19 = x_7;
} else {
 lean_dec_ref(x_7);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
if (lean_is_scalar(x_19)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_19;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalMatch_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Tactic_evalMatch_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalMatch_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalMatch___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalMatch___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 3);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_ctor_set(x_9, 3, x_14);
x_15 = l_Lean_throwError___at_Lean_Elab_Tactic_evalMatch___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_24 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
x_26 = l_Lean_throwError___at_Lean_Elab_Tactic_evalMatch___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25, x_10, x_11);
lean_dec(x_25);
return x_26;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3___rarg), 1, 0);
return x_9;
}
}
lean_object* l_Lean_Elab_Tactic_evalMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_40 = lean_st_ref_get(x_9, x_13);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_8, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_8, 5);
lean_inc(x_45);
lean_inc(x_43);
x_46 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_46, 0, x_43);
lean_inc(x_44);
x_47 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_47, 0, x_44);
lean_inc(x_43);
x_48 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_48, 0, x_43);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
x_49 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__2___boxed), 6, 3);
lean_closure_set(x_49, 0, x_43);
lean_closure_set(x_49, 1, x_44);
lean_closure_set(x_49, 2, x_45);
lean_inc(x_43);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___rarg___lambda__3___boxed), 6, 3);
lean_closure_set(x_50, 0, x_43);
lean_closure_set(x_50, 1, x_44);
lean_closure_set(x_50, 2, x_45);
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set(x_51, 3, x_49);
lean_ctor_set(x_51, 4, x_50);
x_52 = x_51;
x_53 = lean_ctor_get(x_8, 3);
lean_inc(x_53);
x_54 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_42);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_8, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_8, 2);
lean_inc(x_58);
x_59 = lean_st_ref_get(x_9, x_56);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_environment_main_module(x_43);
x_64 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_55);
lean_ctor_set(x_64, 3, x_57);
lean_ctor_set(x_64, 4, x_58);
lean_ctor_set(x_64, 5, x_53);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_65);
lean_inc(x_1);
x_67 = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm(x_12, x_1, x_64, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_st_ref_take(x_9, x_61);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_72, 1);
lean_dec(x_75);
lean_ctor_set(x_72, 1, x_70);
x_76 = lean_st_ref_set(x_9, x_72, x_73);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_ctor_get(x_69, 1);
lean_inc(x_78);
lean_dec(x_69);
x_79 = l_List_reverse___rarg(x_78);
x_80 = l_List_forM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3(x_79, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_77);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_14 = x_68;
x_15 = x_81;
goto block_39;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_82 = lean_ctor_get(x_72, 0);
x_83 = lean_ctor_get(x_72, 2);
x_84 = lean_ctor_get(x_72, 3);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_72);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_70);
lean_ctor_set(x_85, 2, x_83);
lean_ctor_set(x_85, 3, x_84);
x_86 = lean_st_ref_set(x_9, x_85, x_73);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_ctor_get(x_69, 1);
lean_inc(x_88);
lean_dec(x_69);
x_89 = l_List_reverse___rarg(x_88);
x_90 = l_List_forM___at_Lean_Elab_Tactic_expandTacticMacroFns_loop___spec__3(x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_87);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_14 = x_68;
x_15 = x_91;
goto block_39;
}
}
else
{
lean_object* x_92; 
lean_dec(x_1);
x_92 = lean_ctor_get(x_67, 0);
lean_inc(x_92);
lean_dec(x_67);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalMatch___spec__1(x_93, x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_61);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_93);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
return x_97;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_97);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
else
{
lean_object* x_102; uint8_t x_103; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_102 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3___rarg(x_61);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
return x_102;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_102);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
block_39:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Tactic_evalIntro___spec__1___rarg(x_8, x_9, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Parser_Tactic_refine___closed__1;
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Array_empty___closed__1;
x_28 = lean_array_push(x_27, x_26);
x_29 = lean_array_push(x_28, x_16);
x_30 = l_Lean_Parser_Tactic_refine___closed__2;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_mkOptionalNode___closed__2;
x_33 = lean_array_push(x_32, x_31);
x_34 = l_Array_append___rarg(x_33, x_17);
lean_dec(x_17);
x_35 = l_Lean_nullKind;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_inc(x_36);
lean_inc(x_1);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_adaptExpander___lambda__1), 11, 2);
lean_closure_set(x_37, 0, x_1);
lean_closure_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_withMacroExpansionInfo___at_Lean_Elab_Tactic_adaptExpander___spec__1(x_1, x_36, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
return x_38;
}
}
else
{
uint8_t x_107; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_11);
if (x_107 == 0)
{
return x_11;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_11, 0);
x_109 = lean_ctor_get(x_11, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_11);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalMatch___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_evalMatch___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalMatch___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_evalMatch___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalMatch___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalMatch___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalMatch), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalMatch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_match___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalMatch___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Term(lean_object*);
lean_object* initialize_Lean_Elab_Match(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Induction(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Tactic_Match(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Match(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Induction(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___closed__1 = _init_l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___closed__1);
l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___closed__2 = _init_l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalEraseAuxDiscrs___rarg___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalEraseAuxDiscrs(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_AuxMatchTermState_nextIdx___default = _init_l_Lean_Elab_Tactic_AuxMatchTermState_nextIdx___default();
lean_mark_persistent(l_Lean_Elab_Tactic_AuxMatchTermState_nextIdx___default);
l_Lean_Elab_Tactic_AuxMatchTermState_cases___default = _init_l_Lean_Elab_Tactic_AuxMatchTermState_cases___default();
lean_mark_persistent(l_Lean_Elab_Tactic_AuxMatchTermState_cases___default);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__3 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__3);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__4 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___spec__2___closed__4);
l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___boxed__const__1 = _init_l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTermAux___boxed__const__1);
l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1 = _init_l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalMatch___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalMatch___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalMatch___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalMatch(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
