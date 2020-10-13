// Lean compiler output
// Module: Lean.Elab.Attributes
// Imports: Init Lean.Parser.Basic Lean.Attributes Lean.MonadEnv
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
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Attribute_inhabited;
lean_object* l_Lean_withRef___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttrs___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1(lean_object*);
lean_object* l_Lean_Elab_elabAttrs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Attribute_hasFormat___closed__1;
extern lean_object* l_Lean_Format_join___closed__1;
lean_object* l_Lean_Elab_elabAttrs(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr(lean_object*);
lean_object* l_Lean_Elab_Attribute_hasFormat(lean_object*);
lean_object* l_Lean_Elab_Attribute_hasFormat___closed__2;
lean_object* l_Lean_Elab_elabAttr___rarg___closed__2;
lean_object* l_Lean_Elab_Attribute_hasFormat___closed__4;
lean_object* l_Lean_Elab_elabAttr___rarg___closed__1;
lean_object* l_Lean_Elab_elabDeclAttrs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___closed__3;
lean_object* l_Lean_Elab_elabDeclAttrs(lean_object*);
uint8_t l_Lean_isAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__4;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Attribute_inhabited___closed__1;
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2___closed__1;
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2___closed__2;
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3;
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Attribute_hasFormat___closed__3;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabDeclAttrs___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Attribute_hasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("@[");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Attribute_hasFormat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Attribute_hasFormat___closed__1;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Attribute_hasFormat___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Attribute_hasFormat___closed__2;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Attribute_hasFormat___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Attribute_hasFormat___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Attribute_hasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_System_FilePath_dirName___closed__1;
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_2);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Syntax_isMissing(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_formatStxAux___main(x_8, x_9, x_10, x_6);
x_12 = lean_box(0);
x_13 = l_Lean_Format_pretty(x_11, x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_Attribute_hasFormat___closed__4;
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Format_sbracket___closed__4;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Attribute_hasFormat___closed__3;
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = 0;
x_23 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
lean_dec(x_6);
x_24 = l_Lean_Format_join___closed__1;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_Attribute_hasFormat___closed__4;
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Format_sbracket___closed__4;
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Elab_Attribute_hasFormat___closed__3;
x_31 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = 0;
x_33 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
return x_33;
}
}
}
static lean_object* _init_l_Lean_Elab_Attribute_inhabited___closed__1() {
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
static lean_object* _init_l_Lean_Elab_Attribute_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Attribute_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getNumArgs(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_apply_2(x_15, lean_box(0), x_17);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown attribute [");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabAttr___rarg___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabAttr___rarg___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = l_Lean_isAttribute(x_8, x_1);
lean_inc(x_1);
lean_inc(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_1);
if (x_9 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___rarg(x_3, x_4, x_5, x_6, lean_box(0), x_15);
x_17 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_16, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
x_22 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_21, x_10);
return x_22;
}
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___rarg___lambda__2___boxed), 8, 7);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_5);
lean_closure_set(x_10, 5, x_6);
lean_closure_set(x_10, 6, x_7);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("identifier expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabAttr___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabAttr___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabAttr___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_getArg(x_6, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Lean_Syntax_isIdOrAtom_x3f(x_8);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___rarg___lambda__3), 8, 7);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_6);
lean_closure_set(x_11, 2, x_1);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
lean_closure_set(x_11, 5, x_5);
lean_closure_set(x_11, 6, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = l_Lean_Elab_elabAttr___rarg___closed__3;
lean_inc(x_4);
x_13 = l_Lean_throwError___rarg(x_1, x_3, x_4, x_5, lean_box(0), x_12);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_withRef___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_15, 0, x_8);
lean_closure_set(x_15, 1, x_4);
lean_closure_set(x_15, 2, x_13);
lean_inc(x_9);
x_16 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_14, x_15);
x_17 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_16, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_name_mk_string(x_21, x_18);
x_23 = lean_apply_2(x_20, lean_box(0), x_22);
x_24 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_23, x_11);
return x_24;
}
}
}
lean_object* l_Lean_Elab_elabAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttr___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_elabAttr___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_elabAttr___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_nat_add(x_1, x_2);
x_11 = l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg(x_3, x_4, x_5, x_6, x_7, x_2, x_8, x_10, x_9);
return x_11;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_7);
x_11 = lean_nat_dec_lt(x_8, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_array_fget(x_7, x_8);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_Elab_elabAttr___rarg(x_1, x_2, x_3, x_4, x_5, x_15);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Array_mapM___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_9);
lean_inc(x_16);
x_19 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_17, x_18);
x_20 = lean_alloc_closure((void*)(l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__1___boxed), 9, 8);
lean_closure_set(x_20, 0, x_8);
lean_closure_set(x_20, 1, x_6);
lean_closure_set(x_20, 2, x_1);
lean_closure_set(x_20, 3, x_2);
lean_closure_set(x_20, 4, x_3);
lean_closure_set(x_20, 5, x_4);
lean_closure_set(x_20, 6, x_5);
lean_closure_set(x_20, 7, x_7);
x_21 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_19, x_20);
return x_21;
}
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttrs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Syntax_getArgs(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_empty___closed__1;
x_11 = l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_8, x_7, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_elabAttrs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabAttrs___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_foldlStepMAux___main___at_Lean_Elab_elabAttrs___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_elabAttrs___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_elabAttrs___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_elabDeclAttrs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_6, x_7);
x_9 = l_Lean_Elab_elabAttrs___rarg(x_1, x_2, x_3, x_4, x_5, x_8);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_elabDeclAttrs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabDeclAttrs___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabDeclAttrs___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_elabDeclAttrs___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Basic(lean_object*);
lean_object* initialize_Lean_Attributes(lean_object*);
lean_object* initialize_Lean_MonadEnv(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Attributes(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MonadEnv(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Attribute_hasFormat___closed__1 = _init_l_Lean_Elab_Attribute_hasFormat___closed__1();
lean_mark_persistent(l_Lean_Elab_Attribute_hasFormat___closed__1);
l_Lean_Elab_Attribute_hasFormat___closed__2 = _init_l_Lean_Elab_Attribute_hasFormat___closed__2();
lean_mark_persistent(l_Lean_Elab_Attribute_hasFormat___closed__2);
l_Lean_Elab_Attribute_hasFormat___closed__3 = _init_l_Lean_Elab_Attribute_hasFormat___closed__3();
lean_mark_persistent(l_Lean_Elab_Attribute_hasFormat___closed__3);
l_Lean_Elab_Attribute_hasFormat___closed__4 = _init_l_Lean_Elab_Attribute_hasFormat___closed__4();
lean_mark_persistent(l_Lean_Elab_Attribute_hasFormat___closed__4);
l_Lean_Elab_Attribute_inhabited___closed__1 = _init_l_Lean_Elab_Attribute_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Attribute_inhabited___closed__1);
l_Lean_Elab_Attribute_inhabited = _init_l_Lean_Elab_Attribute_inhabited();
lean_mark_persistent(l_Lean_Elab_Attribute_inhabited);
l_Lean_Elab_elabAttr___rarg___lambda__2___closed__1 = _init_l_Lean_Elab_elabAttr___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___lambda__2___closed__1);
l_Lean_Elab_elabAttr___rarg___lambda__2___closed__2 = _init_l_Lean_Elab_elabAttr___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___lambda__2___closed__2);
l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3 = _init_l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3);
l_Lean_Elab_elabAttr___rarg___closed__1 = _init_l_Lean_Elab_elabAttr___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___closed__1);
l_Lean_Elab_elabAttr___rarg___closed__2 = _init_l_Lean_Elab_elabAttr___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___closed__2);
l_Lean_Elab_elabAttr___rarg___closed__3 = _init_l_Lean_Elab_elabAttr___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_elabAttr___rarg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
