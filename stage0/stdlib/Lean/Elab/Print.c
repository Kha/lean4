// Lean compiler output
// Module: Lean.Elab.Print
// Imports: Init Lean.Elab.Command
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
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l___private_Lean_Elab_Print_9__printId(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_8__printIdCore___closed__1;
lean_object* l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__4;
lean_object* l___private_Lean_Elab_Print_8__printIdCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
lean_object* l___private_Lean_Elab_Print_8__printIdCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_2__lparamsToMessageData(lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Elab_Command_elabPrint___closed__6;
lean_object* l_List_forM___main___at___private_Lean_Elab_Print_9__printId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabPrint___closed__2;
lean_object* lean_environment_find(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_resolveName___closed__3;
extern lean_object* l_Lean_Parser_Command_private___elambda__1___closed__5;
lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1;
lean_object* l___private_Lean_Elab_Command_6__mkTermContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabPrint___closed__1;
lean_object* lean_private_to_user_name(lean_object*);
lean_object* l___private_Lean_Elab_Print_1__throwUnknownId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint(lean_object*);
lean_object* l___private_Lean_Elab_Command_3__setState(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_print___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__5;
lean_object* l_List_map___main___at___private_Lean_Elab_Print_9__printId___spec__2(lean_object*);
lean_object* l_Lean_Elab_Command_elabPrint___closed__4;
extern lean_object* l_Lean_Meta_Exception_Inhabited___closed__1;
lean_object* l___private_Lean_Elab_Print_5__printAxiomLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_4__printDefLike___closed__1;
lean_object* l___private_Lean_Elab_Print_4__printDefLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_5__printAxiomLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_4__printDefLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at___private_Lean_Elab_Print_9__printId___spec__1(lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_Print_9__printId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_Elab_Command_elabPrint(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_def___elambda__1___closed__1;
lean_object* l_Lean_Elab_Command_elabPrint___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_protected___elambda__1___closed__5;
extern lean_object* l_Std_PersistentArray_Stats_toString___closed__4;
lean_object* l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__2;
lean_object* l___private_Lean_Elab_Print_9__printId___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Command_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__1;
extern lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
extern lean_object* l_Lean_protectedExt;
lean_object* l___private_Lean_Elab_Print_2__lparamsToMessageData___boxed(lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__4;
extern lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
lean_object* l_List_forM___main___at___private_Lean_Elab_Print_9__printId___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Print_7__printInduct___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_inductive___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Print_3__mkHeader___closed__4;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
extern lean_object* l_Lean_Parser_Command_axiom___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Command_unsafe___elambda__1___closed__5;
lean_object* l___private_Lean_Elab_Command_2__getState(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_3__mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Print_7__printInduct___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_3__mkHeader___closed__5;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l___private_Lean_Elab_Print_6__printQuot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_3__mkHeader___closed__3;
lean_object* l___private_Lean_Elab_Command_7__mkTermState(lean_object*);
lean_object* l___private_Lean_Elab_Print_6__printQuot___closed__1;
lean_object* l___private_Lean_Elab_Print_3__mkHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_3__mkHeader___closed__1;
lean_object* l___private_Lean_Elab_Print_3__mkHeader___closed__2;
lean_object* l_List_foldl___main___at___private_Lean_Elab_Print_2__lparamsToMessageData___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_3__mkHeader___closed__6;
lean_object* l___private_Lean_Elab_Print_7__printInduct___closed__2;
lean_object* l_Lean_Elab_Command_getEnv(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_6__printQuot(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveGlobalName(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l___private_Lean_Elab_Print_1__throwUnknownId(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabPrint___closed__3;
extern lean_object* l_Lean_Parser_Command_theorem___elambda__1___closed__1;
lean_object* l_Lean_Elab_Command_elabPrint___closed__5;
lean_object* l___private_Lean_Elab_Print_7__printInduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_7__printInduct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_7__printInduct___closed__1;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__3;
lean_object* lean_task_get(lean_object*);
extern lean_object* l_Lean_Meta_mkRecursorAttr___closed__1;
lean_object* l_List_foldl___main___at___private_Lean_Elab_Print_2__lparamsToMessageData___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_constant___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Print_7__printInduct___closed__3;
lean_object* l_List_forM___main___at___private_Lean_Elab_Print_9__printId___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l___private_Lean_Elab_Print_1__throwUnknownId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lean_Name_toString___closed__1;
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_2);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_Elab_Term_resolveName___closed__3;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Elab_Command_throwError___rarg(x_1, x_12, x_3, x_4);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Print_1__throwUnknownId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Print_1__throwUnknownId(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_List_foldl___main___at___private_Lean_Elab_Print_2__lparamsToMessageData___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_6 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_inc(x_3);
x_7 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_7, 0, x_3);
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
lean_object* _init_l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PersistentArray_Stats_toString___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Print_2__lparamsToMessageData(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Exception_Inhabited___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_3);
x_6 = l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__2;
x_7 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_List_foldl___main___at___private_Lean_Elab_Print_2__lparamsToMessageData___spec__1(x_7, x_4);
x_9 = l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__4;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* l_List_foldl___main___at___private_Lean_Elab_Print_2__lparamsToMessageData___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___main___at___private_Lean_Elab_Print_2__lparamsToMessageData___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Print_2__lparamsToMessageData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Print_2__lparamsToMessageData(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Print_3__mkHeader___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_private___elambda__1___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Print_3__mkHeader___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_3__mkHeader___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Print_3__mkHeader___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_protected___elambda__1___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Print_3__mkHeader___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_3__mkHeader___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Print_3__mkHeader___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_unsafe___elambda__1___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Print_3__mkHeader___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_3__mkHeader___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Print_3__mkHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_79; 
x_79 = l_Lean_Elab_Command_getEnv(x_6, x_7);
if (x_5 == 0)
{
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Meta_Exception_Inhabited___closed__1;
x_8 = x_82;
x_9 = x_80;
x_10 = x_81;
goto block_78;
}
else
{
uint8_t x_83; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_79);
if (x_83 == 0)
{
return x_79;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_79, 0);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_79);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_79, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
lean_dec(x_79);
x_89 = l___private_Lean_Elab_Print_3__mkHeader___closed__6;
x_8 = x_89;
x_9 = x_87;
x_10 = x_88;
goto block_78;
}
else
{
uint8_t x_90; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_79);
if (x_90 == 0)
{
return x_79;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_79, 0);
x_92 = lean_ctor_get(x_79, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_79);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
block_78:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = l_Lean_protectedExt;
x_12 = l_Lean_TagDeclarationExtension_isTagged(x_11, x_9, x_2);
lean_dec(x_9);
lean_inc(x_2);
x_13 = lean_private_to_user_name(x_2);
if (x_12 == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_2);
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Lean_Elab_Print_2__lparamsToMessageData(x_3);
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_4);
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_10);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_2);
x_28 = lean_ctor_get(x_13, 0);
lean_inc(x_28);
lean_dec(x_13);
x_29 = l___private_Lean_Elab_Print_3__mkHeader___closed__2;
x_30 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_1);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_36, 0, x_28);
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Lean_Elab_Print_2__lparamsToMessageData(x_3);
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_4);
x_43 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_10);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l___private_Lean_Elab_Print_3__mkHeader___closed__4;
x_46 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_46, 0, x_8);
lean_ctor_set(x_46, 1, x_45);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_1);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_51 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_52, 0, x_2);
x_53 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l___private_Lean_Elab_Print_2__lparamsToMessageData(x_3);
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_58, 0, x_4);
x_59 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_10);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_2);
x_61 = lean_ctor_get(x_13, 0);
lean_inc(x_61);
lean_dec(x_13);
x_62 = l___private_Lean_Elab_Print_3__mkHeader___closed__2;
x_63 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_63, 0, x_46);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_1);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_68 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_69, 0, x_61);
x_70 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l___private_Lean_Elab_Print_2__lparamsToMessageData(x_3);
x_72 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_74 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_75, 0, x_4);
x_76 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_10);
return x_77;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Print_3__mkHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l___private_Lean_Elab_Print_3__mkHeader(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_3);
return x_9;
}
}
lean_object* _init_l___private_Lean_Elab_Print_4__printDefLike___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Print_4__printDefLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
x_10 = l___private_Lean_Elab_Print_3__mkHeader(x_2, x_3, x_4, x_5, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_Print_4__printDefLike___closed__1;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_MessageData_ofList___closed__3;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_6);
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = 0;
x_20 = l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(x_1, x_19, x_18, x_8, x_12);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Elab_Print_4__printDefLike___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l___private_Lean_Elab_Print_4__printDefLike(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Print_5__printAxiomLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
x_9 = l___private_Lean_Elab_Print_3__mkHeader(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 0;
x_13 = l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(x_1, x_12, x_10, x_7, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l___private_Lean_Elab_Print_5__printAxiomLike___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l___private_Lean_Elab_Print_5__printAxiomLike(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* _init_l___private_Lean_Elab_Print_6__printQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Quotient primitive");
return x_1;
}
}
lean_object* l___private_Lean_Elab_Print_6__printQuot(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = l___private_Lean_Elab_Print_6__printQuot___closed__1;
x_9 = 0;
x_10 = l___private_Lean_Elab_Print_5__printAxiomLike(x_1, x_8, x_3, x_4, x_5, x_9, x_6, x_7);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Print_6__printQuot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Elab_Print_6__printQuot(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Print_7__printInduct___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_1);
x_10 = lean_environment_find(x_1, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_2);
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_2);
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_8);
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_ConstantInfo_type(x_12);
lean_dec(x_12);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_3 = x_20;
x_4 = x_9;
goto _start;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Print_7__printInduct___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constructors:");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Print_7__printInduct___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_7__printInduct___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Print_7__printInduct___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Print_7__printInduct___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Print_7__printInduct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
x_11 = l_Lean_Elab_Command_getEnv(x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Parser_Command_inductive___elambda__1___closed__1;
lean_inc(x_9);
x_15 = l___private_Lean_Elab_Print_3__mkHeader(x_14, x_2, x_3, x_6, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_MessageData_ofList___closed__3;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lean_Elab_Print_7__printInduct___closed__3;
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_List_foldlM___main___at___private_Lean_Elab_Print_7__printInduct___spec__1(x_12, x_18, x_21, x_7, x_9, x_17);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 0;
x_26 = l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(x_1, x_25, x_23, x_9, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
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
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
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
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Print_7__printInduct___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldlM___main___at___private_Lean_Elab_Print_7__printInduct___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Print_7__printInduct___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_8);
lean_dec(x_8);
x_12 = l___private_Lean_Elab_Print_7__printInduct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
lean_object* _init_l___private_Lean_Elab_Print_8__printIdCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constructor");
return x_1;
}
}
lean_object* l___private_Lean_Elab_Print_8__printIdCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Elab_Command_getEnv(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_2);
x_8 = lean_environment_find(x_6, x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Print_1__throwUnknownId(x_1, x_2, x_3, x_7);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_11, sizeof(void*)*1);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Parser_Command_axiom___elambda__1___closed__1;
x_17 = l___private_Lean_Elab_Print_5__printAxiomLike(x_1, x_16, x_2, x_14, x_15, x_13, x_3, x_7);
lean_dec(x_14);
return x_17;
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 2);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l_Lean_Parser_Command_def___elambda__1___closed__1;
x_25 = l___private_Lean_Elab_Print_4__printDefLike(x_1, x_24, x_2, x_22, x_23, x_20, x_21, x_3, x_7);
lean_dec(x_22);
return x_25;
}
case 2:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 2);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_task_get(x_28);
lean_dec(x_28);
x_32 = l_Lean_Parser_Command_theorem___elambda__1___closed__1;
x_33 = 0;
x_34 = l___private_Lean_Elab_Print_4__printDefLike(x_1, x_32, x_2, x_29, x_30, x_31, x_33, x_3, x_7);
lean_dec(x_29);
return x_34;
}
case 3:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_10, 0);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_35, sizeof(void*)*2);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 2);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Parser_Command_constant___elambda__1___closed__1;
x_41 = l___private_Lean_Elab_Print_5__printAxiomLike(x_1, x_40, x_2, x_38, x_39, x_37, x_3, x_7);
lean_dec(x_38);
return x_41;
}
case 4:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_10, 0);
lean_inc(x_42);
lean_dec(x_10);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 2);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l___private_Lean_Elab_Print_6__printQuot___closed__1;
x_47 = 0;
x_48 = l___private_Lean_Elab_Print_5__printAxiomLike(x_1, x_46, x_2, x_44, x_45, x_47, x_3, x_7);
lean_dec(x_44);
return x_48;
}
case 5:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_10, 0);
lean_inc(x_49);
lean_dec(x_10);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 4);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_49, sizeof(void*)*5 + 1);
lean_dec(x_49);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 2);
lean_inc(x_56);
lean_dec(x_50);
x_57 = l___private_Lean_Elab_Print_7__printInduct(x_1, x_2, x_55, x_51, x_52, x_56, x_53, x_54, x_3, x_7);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_55);
return x_57;
}
case 6:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_10, 0);
lean_inc(x_58);
lean_dec(x_10);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_58, sizeof(void*)*5);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 2);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l___private_Lean_Elab_Print_8__printIdCore___closed__1;
x_64 = l___private_Lean_Elab_Print_5__printAxiomLike(x_1, x_63, x_2, x_61, x_62, x_60, x_3, x_7);
lean_dec(x_61);
return x_64;
}
default: 
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_10, 0);
lean_inc(x_65);
lean_dec(x_10);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_65, sizeof(void*)*7 + 1);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 2);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l_Lean_Meta_mkRecursorAttr___closed__1;
x_71 = l___private_Lean_Elab_Print_5__printAxiomLike(x_1, x_70, x_2, x_68, x_69, x_67, x_3, x_7);
lean_dec(x_68);
return x_71;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_3);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_5);
if (x_72 == 0)
{
return x_5;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_5, 0);
x_74 = lean_ctor_get(x_5, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_5);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
lean_object* l___private_Lean_Elab_Print_8__printIdCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Print_8__printIdCore(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_List_filterAux___main___at___private_Lean_Elab_Print_9__printId___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = l_List_isEmpty___rarg(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_free_object(x_1);
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
else
{
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = l_List_isEmpty___rarg(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_11);
x_1 = x_12;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_2);
x_1 = x_12;
x_2 = x_16;
goto _start;
}
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Print_9__printId___spec__2(lean_object* x_1) {
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
x_6 = l_List_map___main___at___private_Lean_Elab_Print_9__printId___spec__2(x_5);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_7);
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
x_10 = l_List_map___main___at___private_Lean_Elab_Print_9__printId___spec__2(x_9);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Print_9__printId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_3);
x_9 = l___private_Lean_Elab_Print_8__printIdCore(x_1, x_7, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_2 = x_8;
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_3);
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
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Print_9__printId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_3);
x_9 = l___private_Lean_Elab_Print_8__printIdCore(x_1, x_7, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_2 = x_8;
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_3);
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
}
lean_object* l___private_Lean_Elab_Print_9__printId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
lean_inc(x_3);
x_19 = l___private_Lean_Elab_Command_2__getState(x_3, x_4);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Elab_Command_6__mkTermContext(x_3, x_20, x_18);
x_23 = l___private_Lean_Elab_Command_7__mkTermState(x_20);
lean_dec(x_20);
lean_inc(x_2);
x_24 = l_Lean_Elab_Term_resolveGlobalName(x_2, x_22, x_23);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_3);
x_27 = l___private_Lean_Elab_Command_2__getState(x_3, x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 3);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_ctor_get(x_26, 2);
lean_inc(x_33);
lean_dec(x_26);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_29, 5);
lean_dec(x_35);
x_36 = lean_ctor_get(x_29, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_29, 0);
lean_dec(x_37);
lean_ctor_set(x_29, 5, x_32);
lean_ctor_set(x_29, 1, x_33);
lean_ctor_set(x_29, 0, x_31);
lean_inc(x_3);
x_38 = l___private_Lean_Elab_Command_3__setState(x_29, x_3, x_30);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_5 = x_25;
x_6 = x_39;
goto block_17;
}
else
{
uint8_t x_40; 
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_38);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_29, 2);
x_45 = lean_ctor_get(x_29, 3);
x_46 = lean_ctor_get(x_29, 4);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_29);
x_47 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_47, 0, x_31);
lean_ctor_set(x_47, 1, x_33);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_45);
lean_ctor_set(x_47, 4, x_46);
lean_ctor_set(x_47, 5, x_32);
lean_inc(x_3);
x_48 = l___private_Lean_Elab_Command_3__setState(x_47, x_3, x_30);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_5 = x_25;
x_6 = x_49;
goto block_17;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
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
}
else
{
uint8_t x_54; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_27);
if (x_54 == 0)
{
return x_27;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_27, 0);
x_56 = lean_ctor_get(x_27, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_27);
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
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_19);
if (x_58 == 0)
{
return x_19;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_19, 0);
x_60 = lean_ctor_get(x_19, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_19);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
block_17:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_box(0);
x_8 = l_List_filterAux___main___at___private_Lean_Elab_Print_9__printId___spec__1(x_5, x_7);
x_9 = l_List_map___main___at___private_Lean_Elab_Print_9__printId___spec__2(x_8);
x_10 = l_List_isEmpty___rarg(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = l_List_forM___main___at___private_Lean_Elab_Print_9__printId___spec__3(x_1, x_9, x_3, x_6);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_9);
x_12 = l___private_Lean_Elab_Print_1__throwUnknownId(x_1, x_2, x_3, x_6);
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
}
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Print_9__printId___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___main___at___private_Lean_Elab_Print_9__printId___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Print_9__printId___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___main___at___private_Lean_Elab_Print_9__printId___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Print_9__printId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Print_9__printId(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid #print command");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("WIP");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabPrint___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabPrint___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabPrint(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Syntax_getNumArgs(x_1);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Elab_Command_elabPrint___closed__3;
x_8 = l_Lean_Elab_Command_throwError___rarg(x_1, x_7, x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_isIdent(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Syntax_isStrLit_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Elab_Command_elabPrint___closed__6;
x_14 = l_Lean_Elab_Command_throwError___rarg(x_1, x_13, x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = 0;
x_19 = l_Lean_Elab_log___at_Lean_Elab_Command_logTrace___spec__1(x_1, x_18, x_17, x_2, x_3);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_Syntax_getId(x_10);
lean_dec(x_10);
x_21 = l___private_Lean_Elab_Print_9__printId(x_1, x_20, x_2, x_3);
return x_21;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabPrint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabPrint(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabPrint___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabPrint(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_print___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Print(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__1 = _init_l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__1);
l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__2 = _init_l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__2);
l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__3 = _init_l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__3);
l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__4 = _init_l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Print_2__lparamsToMessageData___closed__4);
l___private_Lean_Elab_Print_3__mkHeader___closed__1 = _init_l___private_Lean_Elab_Print_3__mkHeader___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_3__mkHeader___closed__1);
l___private_Lean_Elab_Print_3__mkHeader___closed__2 = _init_l___private_Lean_Elab_Print_3__mkHeader___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_3__mkHeader___closed__2);
l___private_Lean_Elab_Print_3__mkHeader___closed__3 = _init_l___private_Lean_Elab_Print_3__mkHeader___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_3__mkHeader___closed__3);
l___private_Lean_Elab_Print_3__mkHeader___closed__4 = _init_l___private_Lean_Elab_Print_3__mkHeader___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Print_3__mkHeader___closed__4);
l___private_Lean_Elab_Print_3__mkHeader___closed__5 = _init_l___private_Lean_Elab_Print_3__mkHeader___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Print_3__mkHeader___closed__5);
l___private_Lean_Elab_Print_3__mkHeader___closed__6 = _init_l___private_Lean_Elab_Print_3__mkHeader___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Print_3__mkHeader___closed__6);
l___private_Lean_Elab_Print_4__printDefLike___closed__1 = _init_l___private_Lean_Elab_Print_4__printDefLike___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_4__printDefLike___closed__1);
l___private_Lean_Elab_Print_6__printQuot___closed__1 = _init_l___private_Lean_Elab_Print_6__printQuot___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_6__printQuot___closed__1);
l___private_Lean_Elab_Print_7__printInduct___closed__1 = _init_l___private_Lean_Elab_Print_7__printInduct___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_7__printInduct___closed__1);
l___private_Lean_Elab_Print_7__printInduct___closed__2 = _init_l___private_Lean_Elab_Print_7__printInduct___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Print_7__printInduct___closed__2);
l___private_Lean_Elab_Print_7__printInduct___closed__3 = _init_l___private_Lean_Elab_Print_7__printInduct___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Print_7__printInduct___closed__3);
l___private_Lean_Elab_Print_8__printIdCore___closed__1 = _init_l___private_Lean_Elab_Print_8__printIdCore___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Print_8__printIdCore___closed__1);
l_Lean_Elab_Command_elabPrint___closed__1 = _init_l_Lean_Elab_Command_elabPrint___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__1);
l_Lean_Elab_Command_elabPrint___closed__2 = _init_l_Lean_Elab_Command_elabPrint___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__2);
l_Lean_Elab_Command_elabPrint___closed__3 = _init_l_Lean_Elab_Command_elabPrint___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__3);
l_Lean_Elab_Command_elabPrint___closed__4 = _init_l_Lean_Elab_Command_elabPrint___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__4);
l_Lean_Elab_Command_elabPrint___closed__5 = _init_l_Lean_Elab_Command_elabPrint___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__5);
l_Lean_Elab_Command_elabPrint___closed__6 = _init_l_Lean_Elab_Command_elabPrint___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabPrint___closed__6);
l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabPrint___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabPrint(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
