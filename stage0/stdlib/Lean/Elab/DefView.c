// Lean compiler output
// Module: Lean.Elab.DefView
// Imports: Init Std.ShareCommon Lean.Util.CollectLevelParams Lean.Util.FoldConsts Lean.Elab.CollectFVars Lean.Elab.Command Lean.Elab.SyntheticMVars Lean.Elab.Binders Lean.Elab.DeclUtil
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
lean_object* l_Lean_Elab_expandOptDeclSig(lean_object*);
lean_object* l_Lean_Elab_Command_mkDefView___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Elab_DefKind_isExample_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__19;
uint8_t l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque(uint8_t);
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant_match__2(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__2;
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses(lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__1;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_DefKind_isTheorem_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1;
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__6;
lean_object* l_Lean_Elab_DefKind_isExample_match__1(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfDef(lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isExample(uint8_t);
lean_object* l_Lean_Elab_Command_mkDefView___closed__3;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2;
lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfExample(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefView___closed__2;
lean_object* l_Lean_Elab_Command_isDefLike___closed__4;
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__3;
lean_object* l_Lean_Elab_Command_isDefLike___closed__8;
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__5;
lean_object* l_Lean_Elab_mkFreshInstanceName(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_isDefLike___closed__11;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_isDefLike___closed__2;
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__1;
lean_object* l_Lean_Elab_Command_isDefLike___closed__1;
extern lean_object* l_Lean_Meta_registerInstanceAttr___closed__1;
lean_object* l_Lean_Elab_DefKind_isExample_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__4;
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__8;
lean_object* l_Lean_Elab_Command_isDefLike___boxed(lean_object*);
extern lean_object* l_Lean_Meta_registerInstanceAttr___closed__2;
extern lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
lean_object* l_Lean_Elab_DefKind_isTheorem___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance_match__1(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfTheorem(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_isDefLike___closed__9;
uint8_t l_Lean_Elab_Command_isDefLike(lean_object*);
lean_object* l_Lean_Elab_Command_mkFreshInstanceName___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkFreshInstanceName___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* l_Lean_Elab_Command_mkFreshInstanceName(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfExample_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses___closed__2;
lean_object* l_Lean_Elab_DefKind_isTheorem_match__1(lean_object*);
extern lean_object* l_Lean_mkReducibilityAttrs___closed__4;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_mkInlineAttrs___closed__4;
lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses___closed__1;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__14;
lean_object* l_Lean_Elab_Command_mkDefViewOfTheorem_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance_match__2(lean_object*);
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant_match__1(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Command_mkFreshInstanceName___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_isDefLike___closed__6;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfDef_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfExample___closed__2;
lean_object* l_Lean_Elab_expandDeclSig(lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev_match__1___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__2;
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Modifiers_addAttribute(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfTheorem_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_isDefLike___closed__3;
lean_object* l_Lean_Elab_Command_isDefLike___closed__5;
lean_object* l_Lean_Elab_DefKind_isExample___boxed(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_DefKind_isTheorem_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefView___closed__1;
lean_object* l_Lean_Elab_Command_isDefLike___closed__10;
lean_object* l_Lean_Elab_Command_mkDefViewOfExample_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfDef_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___closed__3;
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_isDefLike___closed__7;
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__7;
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance_match__2___rarg(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_6__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_Command_mkDefViewOfExample___closed__1;
lean_object* l_Lean_Elab_DefKind_isTheorem_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(x_1);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Elab_DefKind_isTheorem_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_DefKind_isTheorem_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_DefKind_isTheorem_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Elab_DefKind_isTheorem_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
}
}
lean_object* l_Lean_Elab_DefKind_isTheorem___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_DefKind_isTheorem(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_box(x_1);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 3:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
case 4:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_4, x_11);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(x_1);
x_14 = lean_apply_1(x_5, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque_match__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque_match__1___rarg(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
uint8_t l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
switch (lean_obj_tag(x_2)) {
case 1:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
case 2:
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
default: 
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = 1;
return x_5;
}
}
}
}
lean_object* l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_DefKind_isDefOrAbbrevOrOpaque(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_DefKind_isExample_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(x_1);
if (lean_obj_tag(x_4) == 2)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Elab_DefKind_isExample_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_DefKind_isExample_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_DefKind_isExample_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Elab_DefKind_isExample_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
uint8_t l_Lean_Elab_DefKind_isExample(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 2)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
}
}
lean_object* l_Lean_Elab_DefKind_isExample___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_DefKind_isExample(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDefViewOfAbbrev_match__1___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkInlineAttrs___closed__4;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkReducibilityAttrs___closed__4;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfAbbrev(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
x_5 = l_Lean_Elab_expandOptDeclSig(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1;
x_9 = l_Lean_Elab_Modifiers_addAttribute(x_1, x_8);
x_10 = l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2;
x_11 = l_Lean_Elab_Modifiers_addAttribute(x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_2, x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_2, x_14);
x_16 = 4;
x_17 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_6);
lean_ctor_set(x_17, 4, x_7);
lean_ctor_set(x_17, 5, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*6, x_16);
return x_17;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfDef_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Command_mkDefViewOfDef_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDefViewOfDef_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfDef(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
x_5 = l_Lean_Elab_expandOptDeclSig(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_2, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_2, x_10);
x_12 = 0;
x_13 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_6);
lean_ctor_set(x_13, 4, x_7);
lean_ctor_set(x_13, 5, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*6, x_12);
return x_13;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfTheorem_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Command_mkDefViewOfTheorem_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDefViewOfTheorem_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfTheorem(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
x_5 = l_Lean_Elab_expandDeclSig(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_2, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_2, x_11);
x_13 = 1;
x_14 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_6);
lean_ctor_set(x_14, 4, x_10);
lean_ctor_set(x_14, 5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*6, x_13);
return x_14;
}
}
lean_object* l_Lean_Elab_Command_mkFreshInstanceName___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 5);
lean_inc(x_6);
x_7 = lean_st_ref_take(x_1, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_11, x_12);
lean_dec(x_11);
lean_ctor_set(x_8, 5, x_13);
x_14 = lean_st_ref_set(x_1, x_8, x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = l_Lean_Elab_mkFreshInstanceName(x_17, x_6);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
lean_dec(x_4);
x_21 = l_Lean_Elab_mkFreshInstanceName(x_20, x_6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
x_25 = lean_ctor_get(x_8, 2);
x_26 = lean_ctor_get(x_8, 3);
x_27 = lean_ctor_get(x_8, 4);
x_28 = lean_ctor_get(x_8, 5);
x_29 = lean_ctor_get(x_8, 6);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_28, x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_26);
lean_ctor_set(x_32, 4, x_27);
lean_ctor_set(x_32, 5, x_31);
lean_ctor_set(x_32, 6, x_29);
x_33 = lean_st_ref_set(x_1, x_32, x_9);
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
x_36 = lean_ctor_get(x_4, 0);
lean_inc(x_36);
lean_dec(x_4);
x_37 = l_Lean_Elab_mkFreshInstanceName(x_36, x_6);
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
}
lean_object* l_Lean_Elab_Command_mkFreshInstanceName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkFreshInstanceName___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_mkFreshInstanceName___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_mkFreshInstanceName___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_mkFreshInstanceName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_mkFreshInstanceName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDefViewOfConstant_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDefViewOfConstant_match__2___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("arbitrary");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declValSimple");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = l_Lean_Elab_expandDeclSig(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_2, x_11);
x_13 = l_Lean_Syntax_getOptional_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = l_Lean_Elab_Command_getCurrMacroScope(x_3, x_4, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Command_getMainModule___rarg(x_4, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__4;
x_21 = l_Lean_addMacroScope(x_19, x_20, x_15);
x_22 = l_Lean_SourceInfo_inhabited___closed__1;
x_23 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__3;
x_24 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__6;
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_24);
x_26 = l_Array_empty___closed__1;
x_27 = lean_array_push(x_26, x_25);
x_28 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__14;
x_29 = lean_array_push(x_27, x_28);
x_30 = l_Lean_mkAppStx___closed__8;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__19;
x_33 = l_Lean_mkAtomFrom(x_2, x_32);
x_34 = l_Lean_mkAppStx___closed__9;
x_35 = lean_array_push(x_34, x_33);
x_36 = lean_array_push(x_35, x_31);
x_37 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__8;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_unsigned_to_nat(1u);
x_40 = l_Lean_Syntax_getArg(x_2, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_10);
x_42 = 3;
x_43 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_1);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_9);
lean_ctor_set(x_43, 4, x_41);
lean_ctor_set(x_43, 5, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*6, x_42);
lean_ctor_set(x_17, 0, x_43);
return x_17;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_44 = lean_ctor_get(x_17, 0);
x_45 = lean_ctor_get(x_17, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_17);
x_46 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__4;
x_47 = l_Lean_addMacroScope(x_44, x_46, x_15);
x_48 = l_Lean_SourceInfo_inhabited___closed__1;
x_49 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__3;
x_50 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__6;
x_51 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_47);
lean_ctor_set(x_51, 3, x_50);
x_52 = l_Array_empty___closed__1;
x_53 = lean_array_push(x_52, x_51);
x_54 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__14;
x_55 = lean_array_push(x_53, x_54);
x_56 = l_Lean_mkAppStx___closed__8;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__19;
x_59 = l_Lean_mkAtomFrom(x_2, x_58);
x_60 = l_Lean_mkAppStx___closed__9;
x_61 = lean_array_push(x_60, x_59);
x_62 = lean_array_push(x_61, x_57);
x_63 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__8;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_unsigned_to_nat(1u);
x_66 = l_Lean_Syntax_getArg(x_2, x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_10);
x_68 = 3;
x_69 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_69, 0, x_2);
lean_ctor_set(x_69, 1, x_1);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_9);
lean_ctor_set(x_69, 4, x_67);
lean_ctor_set(x_69, 5, x_64);
lean_ctor_set_uint8(x_69, sizeof(void*)*6, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_45);
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_13);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_13, 0);
x_73 = lean_unsigned_to_nat(1u);
x_74 = l_Lean_Syntax_getArg(x_2, x_73);
lean_ctor_set(x_13, 0, x_10);
x_75 = 3;
x_76 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_76, 0, x_2);
lean_ctor_set(x_76, 1, x_1);
lean_ctor_set(x_76, 2, x_74);
lean_ctor_set(x_76, 3, x_9);
lean_ctor_set(x_76, 4, x_13);
lean_ctor_set(x_76, 5, x_72);
lean_ctor_set_uint8(x_76, sizeof(void*)*6, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_5);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_13, 0);
lean_inc(x_78);
lean_dec(x_13);
x_79 = lean_unsigned_to_nat(1u);
x_80 = l_Lean_Syntax_getArg(x_2, x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_10);
x_82 = 3;
x_83 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_83, 0, x_2);
lean_ctor_set(x_83, 1, x_1);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_9);
lean_ctor_set(x_83, 4, x_81);
lean_ctor_set(x_83, 5, x_78);
lean_ctor_set_uint8(x_83, sizeof(void*)*6, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_5);
return x_84;
}
}
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_mkDefViewOfConstant(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDefViewOfInstance_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDefViewOfInstance_match__2___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_registerInstanceAttr___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declId");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_mkDefViewOfInstance___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = l_Lean_Elab_expandDeclSig(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Command_mkDefViewOfInstance___closed__1;
x_12 = l_Lean_Elab_Modifiers_addAttribute(x_1, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = l_Lean_Syntax_getOptional_x3f(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Elab_Command_mkFreshInstanceName___rarg(x_4, x_5);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lean_mkIdentFrom(x_2, x_18);
x_20 = l_Lean_mkAppStx___closed__9;
x_21 = lean_array_push(x_20, x_19);
x_22 = l_Lean_mkOptionalNode___closed__1;
x_23 = lean_array_push(x_21, x_22);
x_24 = l_Lean_Elab_Command_mkDefViewOfInstance___closed__3;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_10);
x_27 = lean_unsigned_to_nat(3u);
x_28 = l_Lean_Syntax_getArg(x_2, x_27);
x_29 = 0;
x_30 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_9);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*6, x_29);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = l_Lean_mkIdentFrom(x_2, x_31);
x_34 = l_Lean_mkAppStx___closed__9;
x_35 = lean_array_push(x_34, x_33);
x_36 = l_Lean_mkOptionalNode___closed__1;
x_37 = lean_array_push(x_35, x_36);
x_38 = l_Lean_Elab_Command_mkDefViewOfInstance___closed__3;
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_10);
x_41 = lean_unsigned_to_nat(3u);
x_42 = l_Lean_Syntax_getArg(x_2, x_41);
x_43 = 0;
x_44 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_12);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_9);
lean_ctor_set(x_44, 4, x_40);
lean_ctor_set(x_44, 5, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*6, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_32);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_15);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_15, 0, x_10);
x_48 = lean_unsigned_to_nat(3u);
x_49 = l_Lean_Syntax_getArg(x_2, x_48);
x_50 = 0;
x_51 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_12);
lean_ctor_set(x_51, 2, x_47);
lean_ctor_set(x_51, 3, x_9);
lean_ctor_set(x_51, 4, x_15);
lean_ctor_set(x_51, 5, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*6, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_5);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_15, 0);
lean_inc(x_53);
lean_dec(x_15);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_10);
x_55 = lean_unsigned_to_nat(3u);
x_56 = l_Lean_Syntax_getArg(x_2, x_55);
x_57 = 0;
x_58 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_58, 0, x_2);
lean_ctor_set(x_58, 1, x_12);
lean_ctor_set(x_58, 2, x_53);
lean_ctor_set(x_58, 3, x_9);
lean_ctor_set(x_58, 4, x_54);
lean_ctor_set(x_58, 5, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*6, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_5);
return x_59;
}
}
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfInstance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_mkDefViewOfInstance(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfExample_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Command_mkDefViewOfExample_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_mkDefViewOfExample_match__1___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfExample___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_example");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefViewOfExample___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_mkDefViewOfExample___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_mkDefViewOfExample(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_2, x_3);
x_5 = l_Lean_Elab_expandDeclSig(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Command_mkDefViewOfExample___closed__2;
x_9 = l_Lean_mkIdentFrom(x_2, x_8);
x_10 = l_Lean_mkAppStx___closed__9;
x_11 = lean_array_push(x_10, x_9);
x_12 = l_Lean_mkOptionalNode___closed__1;
x_13 = lean_array_push(x_11, x_12);
x_14 = l_Lean_Elab_Command_mkDefViewOfInstance___closed__3;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_7);
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
x_19 = 2;
x_20 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_1);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_6);
lean_ctor_set(x_20, 4, x_16);
lean_ctor_set(x_20, 5, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*6, x_19);
return x_20;
}
}
static lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("abbrev");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_isDefLike___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("def");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_isDefLike___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("theorem");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_isDefLike___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constant");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_isDefLike___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Meta_registerInstanceAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("example");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_isDefLike___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_isDefLike___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_Elab_Command_isDefLike(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = l_Lean_Elab_Command_isDefLike___closed__2;
x_4 = lean_name_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_isDefLike___closed__4;
x_6 = lean_name_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Elab_Command_isDefLike___closed__6;
x_8 = lean_name_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Command_isDefLike___closed__8;
x_10 = lean_name_eq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Command_isDefLike___closed__9;
x_12 = lean_name_eq(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Command_isDefLike___closed__11;
x_14 = lean_name_eq(x_2, x_13);
lean_dec(x_2);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = 1;
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = 1;
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
x_18 = 1;
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_2);
x_19 = 1;
return x_19;
}
}
}
lean_object* l_Lean_Elab_Command_isDefLike___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_isDefLike(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefView___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected kind of definition");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefView___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkDefView___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_mkDefView___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_mkDefView___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_mkDefView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_2);
x_6 = l_Lean_Syntax_getKind(x_2);
x_7 = l_Lean_Elab_Command_isDefLike___closed__2;
x_8 = lean_name_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Command_isDefLike___closed__4;
x_10 = lean_name_eq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Command_isDefLike___closed__6;
x_12 = lean_name_eq(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Command_isDefLike___closed__8;
x_14 = lean_name_eq(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Elab_Command_isDefLike___closed__9;
x_16 = lean_name_eq(x_6, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Elab_Command_isDefLike___closed__11;
x_18 = lean_name_eq(x_6, x_17);
lean_dec(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Elab_Command_mkDefView___closed__3;
x_20 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_19, x_3, x_4, x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_21 = l_Lean_Elab_Command_mkDefViewOfExample(x_1, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_6);
x_23 = l_Lean_Elab_Command_mkDefViewOfInstance(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_6);
x_24 = l_Lean_Elab_Command_mkDefViewOfConstant(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_3);
x_25 = l_Lean_Elab_Command_mkDefViewOfTheorem(x_1, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
lean_dec(x_3);
x_27 = l_Lean_Elab_Command_mkDefViewOfDef(x_1, x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_3);
x_29 = l_Lean_Elab_Command_mkDefViewOfAbbrev(x_1, x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
return x_30;
}
}
}
lean_object* l_Lean_Elab_Command_mkDefView___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_mkDefView(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("definition");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_6__regTraceClasses___closed__1;
x_2 = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Std_ShareCommon(lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(lean_object*);
lean_object* initialize_Lean_Elab_CollectFVars(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
lean_object* initialize_Lean_Elab_DeclUtil(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_DefView(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_ShareCommon(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_CollectFVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1 = _init_l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__1);
l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2 = _init_l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfAbbrev___closed__2);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__1 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__1);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__2 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__2);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__3 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__3);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__4 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__4);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__5 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__5);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__6 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__6);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__7 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__7);
l_Lean_Elab_Command_mkDefViewOfConstant___closed__8 = _init_l_Lean_Elab_Command_mkDefViewOfConstant___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfConstant___closed__8);
l_Lean_Elab_Command_mkDefViewOfInstance___closed__1 = _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfInstance___closed__1);
l_Lean_Elab_Command_mkDefViewOfInstance___closed__2 = _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfInstance___closed__2);
l_Lean_Elab_Command_mkDefViewOfInstance___closed__3 = _init_l_Lean_Elab_Command_mkDefViewOfInstance___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfInstance___closed__3);
l_Lean_Elab_Command_mkDefViewOfExample___closed__1 = _init_l_Lean_Elab_Command_mkDefViewOfExample___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfExample___closed__1);
l_Lean_Elab_Command_mkDefViewOfExample___closed__2 = _init_l_Lean_Elab_Command_mkDefViewOfExample___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkDefViewOfExample___closed__2);
l_Lean_Elab_Command_isDefLike___closed__1 = _init_l_Lean_Elab_Command_isDefLike___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__1);
l_Lean_Elab_Command_isDefLike___closed__2 = _init_l_Lean_Elab_Command_isDefLike___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__2);
l_Lean_Elab_Command_isDefLike___closed__3 = _init_l_Lean_Elab_Command_isDefLike___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__3);
l_Lean_Elab_Command_isDefLike___closed__4 = _init_l_Lean_Elab_Command_isDefLike___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__4);
l_Lean_Elab_Command_isDefLike___closed__5 = _init_l_Lean_Elab_Command_isDefLike___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__5);
l_Lean_Elab_Command_isDefLike___closed__6 = _init_l_Lean_Elab_Command_isDefLike___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__6);
l_Lean_Elab_Command_isDefLike___closed__7 = _init_l_Lean_Elab_Command_isDefLike___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__7);
l_Lean_Elab_Command_isDefLike___closed__8 = _init_l_Lean_Elab_Command_isDefLike___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__8);
l_Lean_Elab_Command_isDefLike___closed__9 = _init_l_Lean_Elab_Command_isDefLike___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__9);
l_Lean_Elab_Command_isDefLike___closed__10 = _init_l_Lean_Elab_Command_isDefLike___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__10);
l_Lean_Elab_Command_isDefLike___closed__11 = _init_l_Lean_Elab_Command_isDefLike___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_isDefLike___closed__11);
l_Lean_Elab_Command_mkDefView___closed__1 = _init_l_Lean_Elab_Command_mkDefView___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_mkDefView___closed__1);
l_Lean_Elab_Command_mkDefView___closed__2 = _init_l_Lean_Elab_Command_mkDefView___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_mkDefView___closed__2);
l_Lean_Elab_Command_mkDefView___closed__3 = _init_l_Lean_Elab_Command_mkDefView___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_mkDefView___closed__3);
l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses___closed__1 = _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses___closed__1();
lean_mark_persistent(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses___closed__1);
l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses___closed__2 = _init_l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses___closed__2();
lean_mark_persistent(l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses___closed__2);
res = l___private_Lean_Elab_DefView_0__Lean_Elab_Command_regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
