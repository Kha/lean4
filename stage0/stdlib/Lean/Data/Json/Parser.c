// Lean compiler output
// Module: Lean.Data.Json.Parser
// Imports: Init Lean.Data.Json.Basic
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
lean_object* l_Lean_Json_Parser_objectCore(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Std_RBNode_insert___at_Lean_Json_mkObj___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Quickparse_expect___closed__1;
lean_object* l_Lean_JsonNumber_shiftl(lean_object*, lean_object*);
lean_object* l_Lean_Quickparse_Monad___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_anyCore___main___rarg___closed__4;
lean_object* l_Lean_Json_Parser_escapedChar(lean_object*);
lean_object* l_Lean_Json_Parser_anyCore___main___rarg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Json_Parser_num___closed__2___boxed__const__1;
lean_object* l_Lean_Json_Parser_natNumDigits___closed__1;
lean_object* l_Std_RBNode_singleton___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_str(lean_object*);
lean_object* l_Lean_Json_Parser_anyCore___main___rarg___closed__2;
lean_object* l_Lean_Json_Parser_anyCore___main___rarg___closed__1;
lean_object* l_Lean_Json_Parser_num___closed__5___boxed__const__1;
lean_object* l_Lean_Quickparse_Monad___closed__6;
lean_object* l_Lean_Json_Parser_num___closed__7;
lean_object* l_Lean_Json_Parser_strCore___main___closed__1;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Json_Parser_anyCore___boxed(lean_object*);
lean_object* l_Lean_Json_Parser_anyCore___main___boxed(lean_object*);
lean_object* l_Lean_Json_Parser_objectCore___main___closed__3;
lean_object* l_Lean_Json_Parser_num___closed__4___boxed__const__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Quickparse_unexpectedEndOfInput;
extern lean_object* l_String_splitAux___main___closed__1;
extern lean_object* l_String_quote___closed__1;
lean_object* l_Lean_Quickparse_Monad___closed__1;
lean_object* l_Lean_Quickparse_Monad___closed__2;
lean_object* l_Lean_Quickparse_pure(lean_object*);
lean_object* l_Lean_Quickparse_Monad___closed__9;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_anyCore(lean_object*);
lean_object* l_Lean_Json_Parser_num___closed__6;
lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__6;
lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__2;
lean_object* l_Lean_Quickparse_expect(lean_object*, lean_object*);
lean_object* l_Lean_Quickparse_expect___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_anyCore___rarg(lean_object*);
lean_object* l_Lean_Quickparse_Monad;
lean_object* l_Lean_Json_Parser_lookahead___rarg___closed__1;
lean_object* l_Lean_Json_Parser_lookahead___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_natNumDigits(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_num(lean_object*);
lean_object* l_String_Iterator_extract(lean_object*, lean_object*);
lean_object* l_Lean_Quickparse_skipWs___main(lean_object*);
lean_object* l_Lean_Quickparse_expectedEndOfInput;
lean_object* l_Lean_Json_Parser_num___closed__3;
lean_object* l_String_Iterator_forward___main(lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_num___closed__5;
lean_object* l_Lean_Json_Parser_anyCore___main___rarg___closed__3;
lean_object* l_Lean_Quickparse_Monad___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Quickparse_inhabited___rarg(lean_object*);
lean_object* l_Lean_Json_Parser_any(lean_object*);
lean_object* l_Lean_Json_Parser_arrayCore___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Quickparse_Monad___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Quickparse_Monad___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Quickparse_fail___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Quickparse_skipWs(lean_object*);
lean_object* l_String_Iterator_next(lean_object*);
lean_object* l_Lean_Quickparse_eoi(lean_object*);
lean_object* l_Lean_Quickparse_inhabited(lean_object*);
lean_object* l_Lean_Quickparse_ws(lean_object*);
extern lean_object* l_Lean_nullKind___closed__1;
uint8_t l_String_Iterator_hasNext(lean_object*);
lean_object* l_Lean_Quickparse_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Quickparse_expectedEndOfInput___closed__1;
lean_object* l_Lean_Json_Parser_natCore___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__7;
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Quickparse_fail(lean_object*);
lean_object* l_Lean_Json_Parser_strCore___main(lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_arrayCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_anyCore___main___rarg___closed__5;
lean_object* l_Lean_Json_Parser_strCore(lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
extern lean_object* l_Bool_HasRepr___closed__1;
lean_object* l_Lean_Quickparse_skip(lean_object*);
lean_object* l_Lean_Quickparse_Monad___closed__4;
lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__3;
extern lean_object* l_Int_one;
lean_object* l_Lean_Json_Parser_lookahead___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Quickparse_Monad___closed__8;
extern lean_object* l_Bool_HasRepr___closed__2;
uint32_t l_String_Iterator_curr(lean_object*);
lean_object* l_Lean_Json_Parser_num___closed__1;
lean_object* l_Lean_Json_Parser_objectCore___main___closed__1;
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l_Lean_Json_Parser_anyCore___main___rarg___closed__6;
lean_object* l_Lean_Quickparse_peek_x3f(lean_object*);
lean_object* l_Lean_Json_parse___closed__1;
lean_object* l_Lean_Json_Parser_objectCore___main___closed__2;
lean_object* l_Lean_Json_Parser_lookahead(lean_object*);
lean_object* l_Lean_Quickparse_Monad___closed__10;
lean_object* l_Lean_Json_Parser_hexChar(lean_object*);
lean_object* l_Lean_Json_Parser_anyCore___main___rarg___closed__7;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__8;
lean_object* l_UInt32_decEq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_num___closed__4;
lean_object* l_Lean_Quickparse_bind(lean_object*, lean_object*);
lean_object* l_Lean_Quickparse_Monad___closed__3;
lean_object* l_Lean_Json_Parser_escapedChar___closed__1;
lean_object* l_Lean_Json_Parser_natNonZero___closed__2;
lean_object* l_Lean_Json_Parser_natNonZero___closed__1;
lean_object* l_Lean_Json_Parser_objectCore___main(lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__5;
lean_object* l_Lean_Quickparse_Monad___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_JsonNumber_shiftr(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
extern lean_object* l_usizeSz;
lean_object* l_Lean_Quickparse_Monad___closed__7;
lean_object* l_Lean_Json_Parser_natCore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Quickparse_peek_x21(lean_object*);
lean_object* l_Lean_Quickparse_Monad___closed__5;
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__3;
lean_object* l_Option_DecidableEq___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Quickparse_unexpectedEndOfInput___closed__1;
lean_object* l_Lean_Json_Parser_num___closed__2;
lean_object* l_Lean_Json_Parser_natNumDigits___closed__2;
uint8_t l_UInt32_decLe(uint32_t, uint32_t);
lean_object* l_Lean_Json_Parser_natMaybeZero(lean_object*);
lean_object* l_Lean_Quickparse_next(lean_object*);
lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__4;
lean_object* l_Lean_Json_Parser_escapedChar___boxed__const__1;
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Json_Parser_hexChar___closed__1;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Json_Parser_natNonZero(lean_object*);
lean_object* l_Lean_Json_Parser_arrayCore___main___closed__1;
lean_object* l_Lean_Quickparse_pure___rarg(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Json_Parser_anyCore___main(lean_object*);
lean_object* l_Lean_Quickparse_inhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Quickparse_inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Quickparse_inhabited___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Quickparse_skipWs___main(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_3 = l_String_Iterator_curr(x_1);
x_4 = 9;
x_5 = x_3 == x_4;
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 10;
x_7 = x_3 == x_6;
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 13;
x_9 = x_3 == x_8;
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 32;
x_11 = x_3 == x_10;
if (x_11 == 0)
{
return x_1;
}
else
{
lean_object* x_12; 
x_12 = l_String_Iterator_next(x_1);
x_1 = x_12;
goto _start;
}
}
else
{
lean_object* x_14; 
x_14 = l_String_Iterator_next(x_1);
x_1 = x_14;
goto _start;
}
}
else
{
lean_object* x_16; 
x_16 = l_String_Iterator_next(x_1);
x_1 = x_16;
goto _start;
}
}
else
{
lean_object* x_18; 
x_18 = l_String_Iterator_next(x_1);
x_1 = x_18;
goto _start;
}
}
}
}
lean_object* l_Lean_Quickparse_skipWs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Quickparse_skipWs___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Quickparse_pure___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Quickparse_pure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Quickparse_pure___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Quickparse_bind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_2, x_6, x_5);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* l_Lean_Quickparse_bind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Quickparse_bind___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_Quickparse_fail___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Quickparse_fail(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Quickparse_fail___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Quickparse_Monad___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_apply_1(x_3, x_8);
lean_ctor_set(x_6, 1, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_apply_1(x_3, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_Quickparse_Monad___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 1);
lean_dec(x_8);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_3);
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
lean_object* l_Lean_Quickparse_Monad___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_1(x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_1(x_4, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_apply_1(x_8, x_11);
lean_ctor_set(x_9, 1, x_12);
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
x_15 = lean_apply_1(x_8, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Quickparse_Monad___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_1(x_3, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 1);
lean_dec(x_10);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_7);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Quickparse_Monad___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_Quickparse_Monad___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Quickparse_Monad___lambda__1), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Quickparse_Monad___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Quickparse_Monad___lambda__2), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Quickparse_Monad___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Quickparse_Monad___closed__1;
x_2 = l_Lean_Quickparse_Monad___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Quickparse_Monad___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Quickparse_pure), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Quickparse_Monad___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Quickparse_Monad___lambda__3), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Quickparse_Monad___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Quickparse_Monad___lambda__4), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Quickparse_Monad___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Quickparse_Monad___lambda__5), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Quickparse_Monad___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Quickparse_Monad___closed__3;
x_2 = l_Lean_Quickparse_Monad___closed__4;
x_3 = l_Lean_Quickparse_Monad___closed__5;
x_4 = l_Lean_Quickparse_Monad___closed__6;
x_5 = l_Lean_Quickparse_Monad___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Quickparse_Monad___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Quickparse_bind), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Quickparse_Monad___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Quickparse_Monad___closed__8;
x_2 = l_Lean_Quickparse_Monad___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Quickparse_Monad() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Quickparse_Monad___closed__10;
return x_1;
}
}
static lean_object* _init_l_Lean_Quickparse_unexpectedEndOfInput___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected end of input");
return x_1;
}
}
static lean_object* _init_l_Lean_Quickparse_unexpectedEndOfInput() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Quickparse_unexpectedEndOfInput___closed__1;
return x_1;
}
}
lean_object* l_Lean_Quickparse_peek_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_String_Iterator_curr(x_1);
x_6 = lean_box_uint32(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Quickparse_peek_x21(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Quickparse_unexpectedEndOfInput;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_String_Iterator_curr(x_1);
x_6 = lean_box_uint32(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Quickparse_skip(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_String_Iterator_next(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_Quickparse_next(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Quickparse_unexpectedEndOfInput;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_String_Iterator_curr(x_1);
x_6 = l_String_Iterator_next(x_1);
x_7 = lean_box_uint32(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Quickparse_expect___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected: ");
return x_1;
}
}
lean_object* l_Lean_Quickparse_expect(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_string_length(x_1);
lean_inc(x_2);
x_4 = l_String_Iterator_forward___main(x_2, x_3);
x_5 = l_String_Iterator_extract(x_2, x_4);
x_6 = lean_string_dec_eq(x_5, x_1);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = l_Lean_Quickparse_expect___closed__1;
x_8 = lean_string_append(x_7, x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Quickparse_expect___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Quickparse_expect(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Quickparse_ws(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Quickparse_skipWs___main(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Quickparse_expectedEndOfInput___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected end of input");
return x_1;
}
}
static lean_object* _init_l_Lean_Quickparse_expectedEndOfInput() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Quickparse_expectedEndOfInput___closed__1;
return x_1;
}
}
lean_object* l_Lean_Quickparse_eoi(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Quickparse_expectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lean_Json_Parser_hexChar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid hex character");
return x_1;
}
}
lean_object* l_Lean_Json_Parser_hexChar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Quickparse_unexpectedEndOfInput;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_21; uint32_t x_33; uint8_t x_34; 
x_5 = l_String_Iterator_curr(x_1);
x_6 = l_String_Iterator_next(x_1);
x_33 = 48;
x_34 = x_33 <= x_5;
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_box(0);
x_21 = x_35;
goto block_32;
}
else
{
uint32_t x_36; uint8_t x_37; 
x_36 = 57;
x_37 = x_5 <= x_36;
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_box(0);
x_21 = x_38;
goto block_32;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_uint32_to_nat(x_5);
x_40 = lean_unsigned_to_nat(48u);
x_41 = lean_nat_sub(x_39, x_40);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_6);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
block_20:
{
uint32_t x_8; uint8_t x_9; 
lean_dec(x_7);
x_8 = 65;
x_9 = x_8 <= x_5;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Json_Parser_hexChar___closed__1;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
uint32_t x_12; uint8_t x_13; 
x_12 = 70;
x_13 = x_5 <= x_12;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Json_Parser_hexChar___closed__1;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_uint32_to_nat(x_5);
x_17 = lean_unsigned_to_nat(65u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
block_32:
{
uint32_t x_22; uint8_t x_23; 
lean_dec(x_21);
x_22 = 97;
x_23 = x_22 <= x_5;
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_box(0);
x_7 = x_24;
goto block_20;
}
else
{
uint32_t x_25; uint8_t x_26; 
x_25 = 102;
x_26 = x_5 <= x_25;
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_box(0);
x_7 = x_27;
goto block_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_uint32_to_nat(x_5);
x_29 = lean_unsigned_to_nat(97u);
x_30 = lean_nat_sub(x_28, x_29);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("illegal \\u escape");
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 9;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 13;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__3() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 10;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__4() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 12;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__5() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 8;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__6() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__7() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 34;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_escapedChar___boxed__const__8() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 92;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_Parser_escapedChar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_140; 
x_140 = l_String_Iterator_hasNext(x_1);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = l_Lean_Quickparse_unexpectedEndOfInput;
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_1);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
else
{
uint32_t x_143; lean_object* x_144; uint32_t x_145; uint8_t x_146; 
x_143 = l_String_Iterator_curr(x_1);
x_144 = l_String_Iterator_next(x_1);
x_145 = 92;
x_146 = x_143 == x_145;
if (x_146 == 0)
{
uint32_t x_147; uint8_t x_148; 
x_147 = 34;
x_148 = x_143 == x_147;
if (x_148 == 0)
{
uint32_t x_149; uint8_t x_150; 
x_149 = 47;
x_150 = x_143 == x_149;
if (x_150 == 0)
{
uint32_t x_151; uint8_t x_152; 
x_151 = 98;
x_152 = x_143 == x_151;
if (x_152 == 0)
{
uint32_t x_153; uint8_t x_154; 
x_153 = 102;
x_154 = x_143 == x_153;
if (x_154 == 0)
{
uint32_t x_155; uint8_t x_156; 
x_155 = 110;
x_156 = x_143 == x_155;
if (x_156 == 0)
{
uint32_t x_157; uint8_t x_158; 
x_157 = 114;
x_158 = x_143 == x_157;
if (x_158 == 0)
{
uint32_t x_159; uint8_t x_160; 
x_159 = 116;
x_160 = x_143 == x_159;
if (x_160 == 0)
{
uint32_t x_161; uint8_t x_162; 
x_161 = 117;
x_162 = x_143 == x_161;
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Lean_Json_Parser_escapedChar___closed__1;
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_144);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
else
{
uint8_t x_165; 
x_165 = l_String_Iterator_hasNext(x_144);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = l_Lean_Quickparse_unexpectedEndOfInput;
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_144);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
else
{
uint32_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_183; uint32_t x_193; uint8_t x_194; 
x_168 = l_String_Iterator_curr(x_144);
x_169 = l_String_Iterator_next(x_144);
x_193 = 48;
x_194 = x_193 <= x_168;
if (x_194 == 0)
{
lean_object* x_195; 
x_195 = lean_box(0);
x_183 = x_195;
goto block_192;
}
else
{
uint32_t x_196; uint8_t x_197; 
x_196 = 57;
x_197 = x_168 <= x_196;
if (x_197 == 0)
{
lean_object* x_198; 
x_198 = lean_box(0);
x_183 = x_198;
goto block_192;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_uint32_to_nat(x_168);
x_200 = lean_unsigned_to_nat(48u);
x_201 = lean_nat_sub(x_199, x_200);
lean_dec(x_199);
x_2 = x_169;
x_3 = x_201;
goto block_139;
}
}
block_182:
{
uint32_t x_171; uint8_t x_172; 
lean_dec(x_170);
x_171 = 65;
x_172 = x_171 <= x_168;
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = l_Lean_Json_Parser_hexChar___closed__1;
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_169);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
else
{
uint32_t x_175; uint8_t x_176; 
x_175 = 70;
x_176 = x_168 <= x_175;
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = l_Lean_Json_Parser_hexChar___closed__1;
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_169);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_uint32_to_nat(x_168);
x_180 = lean_unsigned_to_nat(65u);
x_181 = lean_nat_sub(x_179, x_180);
lean_dec(x_179);
x_2 = x_169;
x_3 = x_181;
goto block_139;
}
}
}
block_192:
{
uint32_t x_184; uint8_t x_185; 
lean_dec(x_183);
x_184 = 97;
x_185 = x_184 <= x_168;
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_box(0);
x_170 = x_186;
goto block_182;
}
else
{
uint8_t x_187; 
x_187 = x_168 <= x_153;
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_box(0);
x_170 = x_188;
goto block_182;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_uint32_to_nat(x_168);
x_190 = lean_unsigned_to_nat(97u);
x_191 = lean_nat_sub(x_189, x_190);
lean_dec(x_189);
x_2 = x_169;
x_3 = x_191;
goto block_139;
}
}
}
}
}
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = l_Lean_Json_Parser_escapedChar___boxed__const__1;
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_144);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Lean_Json_Parser_escapedChar___boxed__const__2;
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_144);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = l_Lean_Json_Parser_escapedChar___boxed__const__3;
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_144);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = l_Lean_Json_Parser_escapedChar___boxed__const__4;
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_144);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = l_Lean_Json_Parser_escapedChar___boxed__const__5;
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_144);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = l_Lean_Json_Parser_escapedChar___boxed__const__6;
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_144);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = l_Lean_Json_Parser_escapedChar___boxed__const__7;
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_144);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; 
x_216 = l_Lean_Json_Parser_escapedChar___boxed__const__8;
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_144);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
block_139:
{
lean_object* x_4; lean_object* x_5; uint8_t x_101; 
x_101 = l_String_Iterator_hasNext(x_2);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_3);
x_102 = l_Lean_Quickparse_unexpectedEndOfInput;
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_2);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
else
{
uint32_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_119; uint32_t x_130; uint8_t x_131; 
x_104 = l_String_Iterator_curr(x_2);
x_105 = l_String_Iterator_next(x_2);
x_130 = 48;
x_131 = x_130 <= x_104;
if (x_131 == 0)
{
lean_object* x_132; 
x_132 = lean_box(0);
x_119 = x_132;
goto block_129;
}
else
{
uint32_t x_133; uint8_t x_134; 
x_133 = 57;
x_134 = x_104 <= x_133;
if (x_134 == 0)
{
lean_object* x_135; 
x_135 = lean_box(0);
x_119 = x_135;
goto block_129;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_uint32_to_nat(x_104);
x_137 = lean_unsigned_to_nat(48u);
x_138 = lean_nat_sub(x_136, x_137);
lean_dec(x_136);
x_4 = x_105;
x_5 = x_138;
goto block_100;
}
}
block_118:
{
uint32_t x_107; uint8_t x_108; 
lean_dec(x_106);
x_107 = 65;
x_108 = x_107 <= x_104;
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_3);
x_109 = l_Lean_Json_Parser_hexChar___closed__1;
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
else
{
uint32_t x_111; uint8_t x_112; 
x_111 = 70;
x_112 = x_104 <= x_111;
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_3);
x_113 = l_Lean_Json_Parser_hexChar___closed__1;
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_105);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_uint32_to_nat(x_104);
x_116 = lean_unsigned_to_nat(65u);
x_117 = lean_nat_sub(x_115, x_116);
lean_dec(x_115);
x_4 = x_105;
x_5 = x_117;
goto block_100;
}
}
}
block_129:
{
uint32_t x_120; uint8_t x_121; 
lean_dec(x_119);
x_120 = 97;
x_121 = x_120 <= x_104;
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = lean_box(0);
x_106 = x_122;
goto block_118;
}
else
{
uint32_t x_123; uint8_t x_124; 
x_123 = 102;
x_124 = x_104 <= x_123;
if (x_124 == 0)
{
lean_object* x_125; 
x_125 = lean_box(0);
x_106 = x_125;
goto block_118;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_uint32_to_nat(x_104);
x_127 = lean_unsigned_to_nat(97u);
x_128 = lean_nat_sub(x_126, x_127);
lean_dec(x_126);
x_4 = x_105;
x_5 = x_128;
goto block_100;
}
}
}
}
block_100:
{
lean_object* x_6; lean_object* x_7; uint8_t x_62; 
x_62 = l_String_Iterator_hasNext(x_4);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_5);
lean_dec(x_3);
x_63 = l_Lean_Quickparse_unexpectedEndOfInput;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_4);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
else
{
uint32_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_80; uint32_t x_91; uint8_t x_92; 
x_65 = l_String_Iterator_curr(x_4);
x_66 = l_String_Iterator_next(x_4);
x_91 = 48;
x_92 = x_91 <= x_65;
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_box(0);
x_80 = x_93;
goto block_90;
}
else
{
uint32_t x_94; uint8_t x_95; 
x_94 = 57;
x_95 = x_65 <= x_94;
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_box(0);
x_80 = x_96;
goto block_90;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_uint32_to_nat(x_65);
x_98 = lean_unsigned_to_nat(48u);
x_99 = lean_nat_sub(x_97, x_98);
lean_dec(x_97);
x_6 = x_66;
x_7 = x_99;
goto block_61;
}
}
block_79:
{
uint32_t x_68; uint8_t x_69; 
lean_dec(x_67);
x_68 = 65;
x_69 = x_68 <= x_65;
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_5);
lean_dec(x_3);
x_70 = l_Lean_Json_Parser_hexChar___closed__1;
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
else
{
uint32_t x_72; uint8_t x_73; 
x_72 = 70;
x_73 = x_65 <= x_72;
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_5);
lean_dec(x_3);
x_74 = l_Lean_Json_Parser_hexChar___closed__1;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_66);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_uint32_to_nat(x_65);
x_77 = lean_unsigned_to_nat(65u);
x_78 = lean_nat_sub(x_76, x_77);
lean_dec(x_76);
x_6 = x_66;
x_7 = x_78;
goto block_61;
}
}
}
block_90:
{
uint32_t x_81; uint8_t x_82; 
lean_dec(x_80);
x_81 = 97;
x_82 = x_81 <= x_65;
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_box(0);
x_67 = x_83;
goto block_79;
}
else
{
uint32_t x_84; uint8_t x_85; 
x_84 = 102;
x_85 = x_65 <= x_84;
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_box(0);
x_67 = x_86;
goto block_79;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_uint32_to_nat(x_65);
x_88 = lean_unsigned_to_nat(97u);
x_89 = lean_nat_sub(x_87, x_88);
lean_dec(x_87);
x_6 = x_66;
x_7 = x_89;
goto block_61;
}
}
}
}
block_61:
{
lean_object* x_8; lean_object* x_9; uint8_t x_23; 
x_23 = l_String_Iterator_hasNext(x_6);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_24 = l_Lean_Quickparse_unexpectedEndOfInput;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
uint32_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_41; uint32_t x_52; uint8_t x_53; 
x_26 = l_String_Iterator_curr(x_6);
x_27 = l_String_Iterator_next(x_6);
x_52 = 48;
x_53 = x_52 <= x_26;
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_41 = x_54;
goto block_51;
}
else
{
uint32_t x_55; uint8_t x_56; 
x_55 = 57;
x_56 = x_26 <= x_55;
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_box(0);
x_41 = x_57;
goto block_51;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_uint32_to_nat(x_26);
x_59 = lean_unsigned_to_nat(48u);
x_60 = lean_nat_sub(x_58, x_59);
lean_dec(x_58);
x_8 = x_27;
x_9 = x_60;
goto block_22;
}
}
block_40:
{
uint32_t x_29; uint8_t x_30; 
lean_dec(x_28);
x_29 = 65;
x_30 = x_29 <= x_26;
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_31 = l_Lean_Json_Parser_hexChar___closed__1;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
uint32_t x_33; uint8_t x_34; 
x_33 = 70;
x_34 = x_26 <= x_33;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_35 = l_Lean_Json_Parser_hexChar___closed__1;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_uint32_to_nat(x_26);
x_38 = lean_unsigned_to_nat(65u);
x_39 = lean_nat_sub(x_37, x_38);
lean_dec(x_37);
x_8 = x_27;
x_9 = x_39;
goto block_22;
}
}
}
block_51:
{
uint32_t x_42; uint8_t x_43; 
lean_dec(x_41);
x_42 = 97;
x_43 = x_42 <= x_26;
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_box(0);
x_28 = x_44;
goto block_40;
}
else
{
uint32_t x_45; uint8_t x_46; 
x_45 = 102;
x_46 = x_26 <= x_45;
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_box(0);
x_28 = x_47;
goto block_40;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_uint32_to_nat(x_26);
x_49 = lean_unsigned_to_nat(97u);
x_50 = lean_nat_sub(x_48, x_49);
lean_dec(x_48);
x_8 = x_27;
x_9 = x_50;
goto block_22;
}
}
}
}
block_22:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_unsigned_to_nat(4096u);
x_11 = lean_nat_mul(x_10, x_3);
lean_dec(x_3);
x_12 = lean_unsigned_to_nat(256u);
x_13 = lean_nat_mul(x_12, x_5);
lean_dec(x_5);
x_14 = lean_nat_add(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
x_15 = lean_unsigned_to_nat(16u);
x_16 = lean_nat_mul(x_15, x_7);
lean_dec(x_7);
x_17 = lean_nat_add(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_18 = lean_nat_add(x_17, x_9);
lean_dec(x_9);
lean_dec(x_17);
x_19 = l_Char_ofNat(x_18);
x_20 = lean_box_uint32(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_strCore___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected character in string");
return x_1;
}
}
lean_object* l_Lean_Json_Parser_strCore___main(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_String_Iterator_hasNext(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_4 = l_Lean_Quickparse_unexpectedEndOfInput;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = l_String_Iterator_curr(x_2);
x_7 = 34;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_9 = l_String_Iterator_next(x_2);
x_10 = 92;
x_11 = x_6 == x_10;
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 32;
x_13 = x_12 <= x_6;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = l_Lean_Json_Parser_strCore___main___closed__1;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
uint32_t x_16; uint8_t x_17; 
x_16 = 1114111;
x_17 = x_6 <= x_16;
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = l_Lean_Json_Parser_strCore___main___closed__1;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_string_push(x_1, x_6);
x_1 = x_20;
x_2 = x_9;
goto _start;
}
}
}
else
{
lean_object* x_22; 
x_22 = l_Lean_Json_Parser_escapedChar(x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint32_t x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unbox_uint32(x_24);
lean_dec(x_24);
x_26 = lean_string_push(x_1, x_25);
x_1 = x_26;
x_2 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_String_Iterator_next(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_1);
return x_33;
}
}
}
}
lean_object* l_Lean_Json_Parser_strCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_Parser_strCore___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Json_Parser_str(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = l_Lean_Json_Parser_strCore___main(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Json_Parser_natCore___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_31; 
x_31 = l_String_Iterator_hasNext(x_3);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_box(0);
x_4 = x_3;
x_5 = x_32;
goto block_30;
}
else
{
uint32_t x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_String_Iterator_curr(x_3);
x_34 = lean_box_uint32(x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_4 = x_3;
x_5 = x_35;
goto block_30;
}
block_30:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 48;
x_10 = lean_unbox_uint32(x_8);
x_11 = x_9 <= x_10;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint32_t x_14; uint32_t x_15; uint8_t x_16; 
x_14 = 57;
x_15 = lean_unbox_uint32(x_8);
x_16 = x_15 <= x_14;
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint32_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = l_String_Iterator_next(x_4);
x_20 = lean_unsigned_to_nat(10u);
x_21 = lean_nat_mul(x_20, x_1);
lean_dec(x_1);
x_22 = lean_unbox_uint32(x_8);
lean_dec(x_8);
x_23 = lean_uint32_to_nat(x_22);
x_24 = lean_unsigned_to_nat(48u);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_23);
x_26 = lean_nat_add(x_21, x_25);
lean_dec(x_25);
lean_dec(x_21);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_2, x_27);
lean_dec(x_2);
x_1 = x_26;
x_2 = x_28;
x_3 = x_19;
goto _start;
}
}
}
}
}
}
lean_object* l_Lean_Json_Parser_natCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Json_Parser_natCore___main(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Json_Parser_lookahead___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected ");
return x_1;
}
}
lean_object* l_Lean_Json_Parser_lookahead___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_String_Iterator_hasNext(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = l_Lean_Quickparse_unexpectedEndOfInput;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_String_Iterator_curr(x_3);
x_8 = lean_box_uint32(x_7);
x_9 = lean_apply_1(x_2, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Json_Parser_lookahead___rarg___closed__1;
x_12 = lean_string_append(x_11, x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Json_Parser_lookahead(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Json_Parser_lookahead___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Json_Parser_lookahead___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Json_Parser_lookahead___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Json_Parser_natNonZero___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("1-9");
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_natNonZero___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Json_Parser_lookahead___rarg___closed__1;
x_2 = l_Lean_Json_Parser_natNonZero___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Json_Parser_natNonZero(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Quickparse_unexpectedEndOfInput;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = l_String_Iterator_curr(x_1);
x_6 = 49;
x_7 = x_6 <= x_5;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Json_Parser_natNonZero___closed__2;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint32_t x_10; uint8_t x_11; 
x_10 = 57;
x_11 = x_5 <= x_10;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Json_Parser_natNonZero___closed__2;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Json_Parser_natCore___main(x_14, x_14, x_1);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_ctor_set(x_15, 1, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_natNumDigits___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("digit");
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_natNumDigits___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Json_Parser_lookahead___rarg___closed__1;
x_2 = l_Lean_Json_Parser_natNumDigits___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Json_Parser_natNumDigits(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Quickparse_unexpectedEndOfInput;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = l_String_Iterator_curr(x_1);
x_6 = 48;
x_7 = x_6 <= x_5;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint32_t x_10; uint8_t x_11; 
x_10 = 57;
x_11 = x_5 <= x_10;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Json_Parser_natCore___main(x_14, x_14, x_1);
return x_15;
}
}
}
}
}
lean_object* l_Lean_Json_Parser_natMaybeZero(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Quickparse_unexpectedEndOfInput;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = l_String_Iterator_curr(x_1);
x_6 = 48;
x_7 = x_6 <= x_5;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint32_t x_10; uint8_t x_11; 
x_10 = 57;
x_11 = x_5 <= x_10;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Json_Parser_natCore___main(x_14, x_14, x_1);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_ctor_set(x_15, 1, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_num___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("exp too large");
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_num___closed__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 101;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_num___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_Parser_num___closed__2___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_num___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_decEq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_num___closed__4___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 69;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_num___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_Parser_num___closed__4___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_num___closed__5___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 46;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_num___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_Parser_num___closed__5___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_num___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many decimals");
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_num___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_one;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_Parser_num(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Quickparse_unexpectedEndOfInput;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint32_t x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_213; 
x_5 = l_String_Iterator_curr(x_1);
x_6 = 45;
x_213 = x_5 == x_6;
if (x_213 == 0)
{
lean_object* x_214; 
x_214 = l_Int_one;
x_7 = x_1;
x_8 = x_214;
goto block_212;
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = l_String_Iterator_next(x_1);
x_216 = l_Lean_Json_Parser_num___closed__7;
x_7 = x_215;
x_8 = x_216;
goto block_212;
}
block_212:
{
lean_object* x_9; lean_object* x_10; uint8_t x_191; 
x_191 = l_String_Iterator_hasNext(x_7);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_8);
x_192 = l_Lean_Quickparse_unexpectedEndOfInput;
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_7);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
else
{
uint32_t x_194; uint32_t x_195; uint8_t x_196; 
x_194 = l_String_Iterator_curr(x_7);
x_195 = 48;
x_196 = x_194 == x_195;
if (x_196 == 0)
{
uint32_t x_197; uint8_t x_198; 
x_197 = 49;
x_198 = x_197 <= x_194;
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_8);
x_199 = l_Lean_Json_Parser_natNonZero___closed__2;
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_7);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
else
{
uint32_t x_201; uint8_t x_202; 
x_201 = 57;
x_202 = x_194 <= x_201;
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_8);
x_203 = l_Lean_Json_Parser_natNonZero___closed__2;
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_7);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_unsigned_to_nat(0u);
x_206 = l_Lean_Json_Parser_natCore___main(x_205, x_205, x_7);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 0);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_ctor_get(x_207, 0);
lean_inc(x_209);
lean_dec(x_207);
x_9 = x_208;
x_10 = x_209;
goto block_190;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = l_String_Iterator_next(x_7);
x_211 = lean_unsigned_to_nat(0u);
x_9 = x_210;
x_10 = x_211;
goto block_190;
}
}
block_190:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_185; 
x_11 = lean_nat_to_int(x_10);
x_12 = lean_int_mul(x_8, x_11);
lean_dec(x_11);
lean_dec(x_8);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_185 = l_String_Iterator_hasNext(x_9);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_box(0);
x_15 = x_9;
x_16 = x_186;
goto block_184;
}
else
{
uint32_t x_187; lean_object* x_188; lean_object* x_189; 
x_187 = l_String_Iterator_curr(x_9);
x_188 = lean_box_uint32(x_187);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_15 = x_9;
x_16 = x_189;
goto block_184;
}
block_184:
{
lean_object* x_17; lean_object* x_18; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_134 = l_Lean_Json_Parser_num___closed__3;
x_135 = l_Lean_Json_Parser_num___closed__5;
x_136 = l_Option_DecidableEq___rarg(x_134, x_16, x_135);
x_137 = lean_unbox(x_136);
lean_dec(x_136);
if (x_137 == 0)
{
lean_dec(x_12);
x_17 = x_15;
x_18 = x_14;
goto block_133;
}
else
{
lean_object* x_138; uint8_t x_139; 
lean_dec(x_14);
x_138 = l_String_Iterator_next(x_15);
x_139 = l_String_Iterator_hasNext(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_12);
x_140 = l_Lean_Quickparse_unexpectedEndOfInput;
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
else
{
uint32_t x_142; uint32_t x_143; uint8_t x_144; 
x_142 = l_String_Iterator_curr(x_138);
x_143 = 48;
x_144 = x_143 <= x_142;
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_12);
x_145 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_138);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
else
{
uint32_t x_147; uint8_t x_148; 
x_147 = 57;
x_148 = x_142 <= x_147;
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_12);
x_149 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_138);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
else
{
lean_object* x_151; uint8_t x_152; 
x_151 = l_Lean_Json_Parser_natCore___main(x_13, x_13, x_138);
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_153 = lean_ctor_get(x_151, 1);
x_154 = lean_ctor_get(x_151, 0);
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
x_157 = l_usizeSz;
x_158 = lean_nat_dec_lt(x_157, x_156);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_free_object(x_151);
x_159 = lean_unsigned_to_nat(10u);
x_160 = lean_nat_pow(x_159, x_156);
x_161 = lean_nat_to_int(x_160);
x_162 = lean_int_mul(x_12, x_161);
lean_dec(x_161);
lean_dec(x_12);
x_163 = lean_nat_to_int(x_155);
x_164 = lean_int_add(x_162, x_163);
lean_dec(x_163);
lean_dec(x_162);
x_165 = lean_nat_add(x_13, x_156);
lean_dec(x_156);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_17 = x_154;
x_18 = x_166;
goto block_133;
}
else
{
lean_object* x_167; 
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_12);
x_167 = l_Lean_Json_Parser_num___closed__6;
lean_ctor_set_tag(x_151, 1);
lean_ctor_set(x_151, 1, x_167);
return x_151;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_168 = lean_ctor_get(x_151, 1);
x_169 = lean_ctor_get(x_151, 0);
lean_inc(x_168);
lean_inc(x_169);
lean_dec(x_151);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec(x_168);
x_172 = l_usizeSz;
x_173 = lean_nat_dec_lt(x_172, x_171);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_174 = lean_unsigned_to_nat(10u);
x_175 = lean_nat_pow(x_174, x_171);
x_176 = lean_nat_to_int(x_175);
x_177 = lean_int_mul(x_12, x_176);
lean_dec(x_176);
lean_dec(x_12);
x_178 = lean_nat_to_int(x_170);
x_179 = lean_int_add(x_177, x_178);
lean_dec(x_178);
lean_dec(x_177);
x_180 = lean_nat_add(x_13, x_171);
lean_dec(x_171);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_17 = x_169;
x_18 = x_181;
goto block_133;
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_12);
x_182 = l_Lean_Json_Parser_num___closed__6;
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_169);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
}
}
}
block_133:
{
lean_object* x_19; uint32_t x_20; lean_object* x_107; lean_object* x_108; uint8_t x_128; 
x_128 = l_String_Iterator_hasNext(x_17);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_box(0);
x_107 = x_17;
x_108 = x_129;
goto block_127;
}
else
{
uint32_t x_130; lean_object* x_131; lean_object* x_132; 
x_130 = l_String_Iterator_curr(x_17);
x_131 = lean_box_uint32(x_130);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_107 = x_17;
x_108 = x_132;
goto block_127;
}
block_106:
{
uint8_t x_21; 
x_21 = x_20 == x_6;
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 43;
x_23 = x_20 == x_22;
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_String_Iterator_hasNext(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_18);
x_25 = l_Lean_Quickparse_unexpectedEndOfInput;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
uint32_t x_27; uint32_t x_28; uint8_t x_29; 
x_27 = l_String_Iterator_curr(x_19);
x_28 = 48;
x_29 = x_28 <= x_27;
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
x_30 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
uint32_t x_32; uint8_t x_33; 
x_32 = 57;
x_33 = x_27 <= x_32;
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_18);
x_34 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Json_Parser_natCore___main(x_13, x_13, x_19);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_36, 1);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_usizeSz;
x_41 = lean_nat_dec_lt(x_40, x_39);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_Lean_JsonNumber_shiftl(x_18, x_39);
lean_dec(x_39);
lean_ctor_set(x_36, 1, x_42);
return x_36;
}
else
{
lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_18);
x_43 = l_Lean_Json_Parser_num___closed__1;
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_43);
return x_36;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_36, 1);
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_44);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_usizeSz;
x_48 = lean_nat_dec_lt(x_47, x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_JsonNumber_shiftl(x_18, x_46);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_46);
lean_dec(x_18);
x_51 = l_Lean_Json_Parser_num___closed__1;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = l_String_Iterator_next(x_19);
x_54 = l_String_Iterator_hasNext(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_18);
x_55 = l_Lean_Quickparse_unexpectedEndOfInput;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
else
{
uint32_t x_57; uint32_t x_58; uint8_t x_59; 
x_57 = l_String_Iterator_curr(x_53);
x_58 = 48;
x_59 = x_58 <= x_57;
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_18);
x_60 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
else
{
uint32_t x_62; uint8_t x_63; 
x_62 = 57;
x_63 = x_57 <= x_62;
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_18);
x_64 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; uint8_t x_67; 
x_66 = l_Lean_Json_Parser_natCore___main(x_13, x_13, x_53);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_66, 1);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_usizeSz;
x_71 = lean_nat_dec_lt(x_70, x_69);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = l_Lean_JsonNumber_shiftl(x_18, x_69);
lean_dec(x_69);
lean_ctor_set(x_66, 1, x_72);
return x_66;
}
else
{
lean_object* x_73; 
lean_dec(x_69);
lean_dec(x_18);
x_73 = l_Lean_Json_Parser_num___closed__1;
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 1, x_73);
return x_66;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_66, 1);
x_75 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
lean_inc(x_75);
lean_dec(x_66);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_usizeSz;
x_78 = lean_nat_dec_lt(x_77, x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Lean_JsonNumber_shiftl(x_18, x_76);
lean_dec(x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_76);
lean_dec(x_18);
x_81 = l_Lean_Json_Parser_num___closed__1;
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
}
}
}
else
{
lean_object* x_83; uint8_t x_84; 
x_83 = l_String_Iterator_next(x_19);
x_84 = l_String_Iterator_hasNext(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_18);
x_85 = l_Lean_Quickparse_unexpectedEndOfInput;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
else
{
uint32_t x_87; uint32_t x_88; uint8_t x_89; 
x_87 = l_String_Iterator_curr(x_83);
x_88 = 48;
x_89 = x_88 <= x_87;
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_18);
x_90 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_83);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
else
{
uint32_t x_92; uint8_t x_93; 
x_92 = 57;
x_93 = x_87 <= x_92;
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_18);
x_94 = l_Lean_Json_Parser_natNumDigits___closed__2;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_83);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
else
{
lean_object* x_96; uint8_t x_97; 
x_96 = l_Lean_Json_Parser_natCore___main(x_13, x_13, x_83);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 1);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec(x_98);
x_100 = l_Lean_JsonNumber_shiftr(x_18, x_99);
lean_dec(x_99);
lean_ctor_set(x_96, 1, x_100);
return x_96;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_96, 1);
x_102 = lean_ctor_get(x_96, 0);
lean_inc(x_101);
lean_inc(x_102);
lean_dec(x_96);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_JsonNumber_shiftr(x_18, x_103);
lean_dec(x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
}
block_127:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = l_Lean_Json_Parser_num___closed__3;
x_110 = l_Lean_Json_Parser_num___closed__2;
lean_inc(x_108);
x_111 = l_Option_DecidableEq___rarg(x_109, x_108, x_110);
x_112 = lean_unbox(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = l_Lean_Json_Parser_num___closed__4;
x_114 = l_Option_DecidableEq___rarg(x_109, x_108, x_113);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_107);
lean_ctor_set(x_116, 1, x_18);
return x_116;
}
else
{
lean_object* x_117; uint8_t x_118; 
x_117 = l_String_Iterator_next(x_107);
x_118 = l_String_Iterator_hasNext(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_18);
x_119 = l_Lean_Quickparse_unexpectedEndOfInput;
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
else
{
uint32_t x_121; 
x_121 = l_String_Iterator_curr(x_117);
x_19 = x_117;
x_20 = x_121;
goto block_106;
}
}
}
else
{
lean_object* x_122; uint8_t x_123; 
lean_dec(x_108);
x_122 = l_String_Iterator_next(x_107);
x_123 = l_String_Iterator_hasNext(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_18);
x_124 = l_Lean_Quickparse_unexpectedEndOfInput;
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
else
{
uint32_t x_126; 
x_126 = l_String_Iterator_curr(x_122);
x_19 = x_122;
x_20 = x_126;
goto block_106;
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Json_Parser_arrayCore___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected character in array");
return x_1;
}
}
lean_object* l_Lean_Json_Parser_arrayCore___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
lean_inc(x_1);
x_5 = lean_apply_2(x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_array_push(x_2, x_8);
x_10 = l_String_Iterator_hasNext(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_1);
x_11 = l_Lean_Quickparse_unexpectedEndOfInput;
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_11);
return x_5;
}
else
{
uint32_t x_12; lean_object* x_13; uint32_t x_14; uint8_t x_15; 
x_12 = l_String_Iterator_curr(x_7);
x_13 = l_String_Iterator_next(x_7);
x_14 = 93;
x_15 = x_12 == x_14;
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 44;
x_17 = x_12 == x_16;
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_1);
x_18 = l_Lean_Json_Parser_arrayCore___main___closed__1;
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_18);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_19; 
lean_free_object(x_5);
x_19 = l_Lean_Quickparse_skipWs___main(x_13);
x_2 = x_9;
x_3 = x_19;
goto _start;
}
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = l_Lean_Quickparse_skipWs___main(x_13);
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_21);
return x_5;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_24 = lean_array_push(x_2, x_23);
x_25 = l_String_Iterator_hasNext(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_1);
x_26 = l_Lean_Quickparse_unexpectedEndOfInput;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
uint32_t x_28; lean_object* x_29; uint32_t x_30; uint8_t x_31; 
x_28 = l_String_Iterator_curr(x_22);
x_29 = l_String_Iterator_next(x_22);
x_30 = 93;
x_31 = x_28 == x_30;
if (x_31 == 0)
{
uint32_t x_32; uint8_t x_33; 
x_32 = 44;
x_33 = x_28 == x_32;
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_24);
lean_dec(x_1);
x_34 = l_Lean_Json_Parser_arrayCore___main___closed__1;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_Quickparse_skipWs___main(x_29);
x_2 = x_24;
x_3 = x_36;
goto _start;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_38 = l_Lean_Quickparse_skipWs___main(x_29);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_24);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
return x_5;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_5, 0);
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_5);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
lean_object* l_Lean_Json_Parser_arrayCore(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Json_Parser_arrayCore___main(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Json_Parser_objectCore___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Json_Parser_lookahead___rarg___closed__1;
x_2 = l_String_quote___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_Parser_objectCore___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Json_Parser_lookahead___rarg___closed__1;
x_2 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_Parser_objectCore___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected character in object");
return x_1;
}
}
lean_object* l_Lean_Json_Parser_objectCore___main(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_String_Iterator_hasNext(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_4 = l_Lean_Quickparse_unexpectedEndOfInput;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = l_String_Iterator_curr(x_2);
x_7 = 34;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = l_Lean_Json_Parser_objectCore___main___closed__1;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_String_Iterator_next(x_2);
x_12 = l_String_splitAux___main___closed__1;
x_13 = l_Lean_Json_Parser_strCore___main(x_12, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Quickparse_skipWs___main(x_15);
x_18 = l_String_Iterator_hasNext(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_1);
x_19 = l_Lean_Quickparse_unexpectedEndOfInput;
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_19);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
uint32_t x_20; uint32_t x_21; uint8_t x_22; 
x_20 = l_String_Iterator_curr(x_17);
x_21 = 58;
x_22 = x_20 == x_21;
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_16);
lean_dec(x_1);
x_23 = l_Lean_Json_Parser_objectCore___main___closed__2;
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_23);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_13);
x_24 = l_String_Iterator_next(x_17);
x_25 = l_Lean_Quickparse_skipWs___main(x_24);
x_26 = lean_box(0);
lean_inc(x_1);
x_27 = lean_apply_2(x_1, x_26, x_25);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = l_String_Iterator_hasNext(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_1);
x_32 = l_Lean_Quickparse_unexpectedEndOfInput;
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_32);
return x_27;
}
else
{
uint32_t x_33; lean_object* x_34; uint32_t x_35; uint8_t x_36; 
x_33 = l_String_Iterator_curr(x_29);
x_34 = l_String_Iterator_next(x_29);
x_35 = 125;
x_36 = x_33 == x_35;
if (x_36 == 0)
{
uint32_t x_37; uint8_t x_38; 
x_37 = 44;
x_38 = x_33 == x_37;
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_30);
lean_dec(x_16);
lean_dec(x_1);
x_39 = l_Lean_Json_Parser_objectCore___main___closed__3;
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_39);
lean_ctor_set(x_27, 0, x_34);
return x_27;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_free_object(x_27);
x_40 = l_Lean_Quickparse_skipWs___main(x_34);
x_41 = l_Lean_Json_Parser_objectCore___main(x_1, x_40);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 1);
x_44 = l_Std_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_43, x_16, x_30);
lean_ctor_set(x_41, 1, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
x_47 = l_Std_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_46, x_16, x_30);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_30);
lean_dec(x_16);
x_49 = !lean_is_exclusive(x_41);
if (x_49 == 0)
{
return x_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_41, 0);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_41);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_53 = l_Lean_Quickparse_skipWs___main(x_34);
x_54 = l_Std_RBNode_singleton___rarg(x_16, x_30);
lean_ctor_set(x_27, 1, x_54);
lean_ctor_set(x_27, 0, x_53);
return x_27;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_27, 0);
x_56 = lean_ctor_get(x_27, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_27);
x_57 = l_String_Iterator_hasNext(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_56);
lean_dec(x_16);
lean_dec(x_1);
x_58 = l_Lean_Quickparse_unexpectedEndOfInput;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
else
{
uint32_t x_60; lean_object* x_61; uint32_t x_62; uint8_t x_63; 
x_60 = l_String_Iterator_curr(x_55);
x_61 = l_String_Iterator_next(x_55);
x_62 = 125;
x_63 = x_60 == x_62;
if (x_63 == 0)
{
uint32_t x_64; uint8_t x_65; 
x_64 = 44;
x_65 = x_60 == x_64;
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_56);
lean_dec(x_16);
lean_dec(x_1);
x_66 = l_Lean_Json_Parser_objectCore___main___closed__3;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = l_Lean_Quickparse_skipWs___main(x_61);
x_69 = l_Lean_Json_Parser_objectCore___main(x_1, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = l_Std_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_71, x_16, x_56);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_56);
lean_dec(x_16);
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_1);
x_79 = l_Lean_Quickparse_skipWs___main(x_61);
x_80 = l_Std_RBNode_singleton___rarg(x_16, x_56);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_16);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_27);
if (x_82 == 0)
{
return x_27;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_27, 0);
x_84 = lean_ctor_get(x_27, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_27);
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
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_13, 0);
x_87 = lean_ctor_get(x_13, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_13);
x_88 = l_Lean_Quickparse_skipWs___main(x_86);
x_89 = l_String_Iterator_hasNext(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_87);
lean_dec(x_1);
x_90 = l_Lean_Quickparse_unexpectedEndOfInput;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
else
{
uint32_t x_92; uint32_t x_93; uint8_t x_94; 
x_92 = l_String_Iterator_curr(x_88);
x_93 = 58;
x_94 = x_92 == x_93;
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_87);
lean_dec(x_1);
x_95 = l_Lean_Json_Parser_objectCore___main___closed__2;
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_88);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = l_String_Iterator_next(x_88);
x_98 = l_Lean_Quickparse_skipWs___main(x_97);
x_99 = lean_box(0);
lean_inc(x_1);
x_100 = lean_apply_2(x_1, x_99, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = l_String_Iterator_hasNext(x_101);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_102);
lean_dec(x_87);
lean_dec(x_1);
x_105 = l_Lean_Quickparse_unexpectedEndOfInput;
if (lean_is_scalar(x_103)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_103;
 lean_ctor_set_tag(x_106, 1);
}
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
else
{
uint32_t x_107; lean_object* x_108; uint32_t x_109; uint8_t x_110; 
x_107 = l_String_Iterator_curr(x_101);
x_108 = l_String_Iterator_next(x_101);
x_109 = 125;
x_110 = x_107 == x_109;
if (x_110 == 0)
{
uint32_t x_111; uint8_t x_112; 
x_111 = 44;
x_112 = x_107 == x_111;
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_102);
lean_dec(x_87);
lean_dec(x_1);
x_113 = l_Lean_Json_Parser_objectCore___main___closed__3;
if (lean_is_scalar(x_103)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_103;
 lean_ctor_set_tag(x_114, 1);
}
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_103);
x_115 = l_Lean_Quickparse_skipWs___main(x_108);
x_116 = l_Lean_Json_Parser_objectCore___main(x_1, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = l_Std_RBNode_insert___at_Lean_Json_mkObj___spec__1(x_118, x_87, x_102);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_117);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_102);
lean_dec(x_87);
x_122 = lean_ctor_get(x_116, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_116, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_124 = x_116;
} else {
 lean_dec_ref(x_116);
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
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_1);
x_126 = l_Lean_Quickparse_skipWs___main(x_108);
x_127 = l_Std_RBNode_singleton___rarg(x_87, x_102);
if (lean_is_scalar(x_103)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_103;
}
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_87);
lean_dec(x_1);
x_129 = lean_ctor_get(x_100, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_100, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_131 = x_100;
} else {
 lean_dec_ref(x_100);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_13);
if (x_133 == 0)
{
return x_13;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_13, 0);
x_135 = lean_ctor_get(x_13, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_13);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
}
}
lean_object* l_Lean_Json_Parser_objectCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_Parser_objectCore___main(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected input");
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___main___rarg___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___main___rarg___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___main___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Parser_anyCore___main___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___main___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___main___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Json_Parser_anyCore___main___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Json_Parser_anyCore___main___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_String_Iterator_hasNext(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Quickparse_unexpectedEndOfInput;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; 
x_5 = l_String_Iterator_curr(x_1);
x_6 = 91;
x_7 = x_5 == x_6;
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 123;
x_9 = x_5 == x_8;
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 34;
x_11 = x_5 == x_10;
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 102;
x_13 = x_5 == x_12;
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 116;
x_15 = x_5 == x_14;
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 110;
x_17 = x_5 == x_16;
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = 45;
x_19 = x_5 == x_18;
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
x_20 = 48;
x_21 = x_20 <= x_5;
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Json_Parser_anyCore___main___rarg___closed__1;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
uint32_t x_24; uint8_t x_25; 
x_24 = 57;
x_25 = x_5 <= x_24;
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Json_Parser_anyCore___main___rarg___closed__1;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = l_Lean_Json_Parser_num(x_1);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = l_Lean_Quickparse_skipWs___main(x_30);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_28, 1, x_33);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = l_Lean_Quickparse_skipWs___main(x_34);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_28);
if (x_39 == 0)
{
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_28);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Json_Parser_num(x_1);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
x_47 = l_Lean_Quickparse_skipWs___main(x_45);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_43, 1, x_48);
lean_ctor_set(x_43, 0, x_47);
return x_43;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_43, 0);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_43);
x_51 = l_Lean_Quickparse_skipWs___main(x_49);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_43);
if (x_54 == 0)
{
return x_43;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_43, 0);
x_56 = lean_ctor_get(x_43, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_43);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_nullKind___closed__1;
x_59 = l_Lean_Quickparse_expect(x_58, x_1);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
lean_dec(x_62);
x_63 = l_Lean_Quickparse_skipWs___main(x_61);
x_64 = lean_box(0);
lean_ctor_set(x_59, 1, x_64);
lean_ctor_set(x_59, 0, x_63);
return x_59;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
lean_dec(x_59);
x_66 = l_Lean_Quickparse_skipWs___main(x_65);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_59);
if (x_69 == 0)
{
return x_59;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_59, 0);
x_71 = lean_ctor_get(x_59, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_59);
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
lean_object* x_73; lean_object* x_74; 
x_73 = l_Bool_HasRepr___closed__2;
x_74 = l_Lean_Quickparse_expect(x_73, x_1);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_74, 1);
lean_dec(x_77);
x_78 = l_Lean_Quickparse_skipWs___main(x_76);
x_79 = l_Lean_Json_Parser_anyCore___main___rarg___closed__2;
lean_ctor_set(x_74, 1, x_79);
lean_ctor_set(x_74, 0, x_78);
return x_74;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_74, 0);
lean_inc(x_80);
lean_dec(x_74);
x_81 = l_Lean_Quickparse_skipWs___main(x_80);
x_82 = l_Lean_Json_Parser_anyCore___main___rarg___closed__2;
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_74);
if (x_84 == 0)
{
return x_74;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_74, 0);
x_86 = lean_ctor_get(x_74, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_74);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Bool_HasRepr___closed__1;
x_89 = l_Lean_Quickparse_expect(x_88, x_1);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_ctor_get(x_89, 1);
lean_dec(x_92);
x_93 = l_Lean_Quickparse_skipWs___main(x_91);
x_94 = l_Lean_Json_Parser_anyCore___main___rarg___closed__3;
lean_ctor_set(x_89, 1, x_94);
lean_ctor_set(x_89, 0, x_93);
return x_89;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_89, 0);
lean_inc(x_95);
lean_dec(x_89);
x_96 = l_Lean_Quickparse_skipWs___main(x_95);
x_97 = l_Lean_Json_Parser_anyCore___main___rarg___closed__3;
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_89);
if (x_99 == 0)
{
return x_89;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_89, 0);
x_101 = lean_ctor_get(x_89, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_89);
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
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = l_String_Iterator_next(x_1);
x_104 = l_String_splitAux___main___closed__1;
x_105 = l_Lean_Json_Parser_strCore___main(x_104, x_103);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_ctor_get(x_105, 1);
x_109 = l_Lean_Quickparse_skipWs___main(x_107);
x_110 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_105, 1, x_110);
lean_ctor_set(x_105, 0, x_109);
return x_105;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_105, 0);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_105);
x_113 = l_Lean_Quickparse_skipWs___main(x_111);
x_114 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_114, 0, x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_105);
if (x_116 == 0)
{
return x_105;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_105, 0);
x_118 = lean_ctor_get(x_105, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_105);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = l_String_Iterator_next(x_1);
x_121 = l_Lean_Quickparse_skipWs___main(x_120);
x_122 = l_String_Iterator_hasNext(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = l_Lean_Quickparse_unexpectedEndOfInput;
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
else
{
uint32_t x_125; uint32_t x_126; uint8_t x_127; 
x_125 = l_String_Iterator_curr(x_121);
x_126 = 125;
x_127 = x_125 == x_126;
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = l_Lean_Json_Parser_anyCore___main___rarg___closed__4;
x_129 = l_Lean_Json_Parser_objectCore___main(x_128, x_121);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_129, 1);
x_132 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_129, 1, x_132);
return x_129;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_129, 0);
x_134 = lean_ctor_get(x_129, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_129);
x_135 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
else
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_129);
if (x_137 == 0)
{
return x_129;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_129, 0);
x_139 = lean_ctor_get(x_129, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_129);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = l_String_Iterator_next(x_121);
x_142 = l_Lean_Quickparse_skipWs___main(x_141);
x_143 = l_Lean_Json_Parser_anyCore___main___rarg___closed__5;
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = l_String_Iterator_next(x_1);
x_146 = l_Lean_Quickparse_skipWs___main(x_145);
x_147 = l_String_Iterator_hasNext(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = l_Lean_Quickparse_unexpectedEndOfInput;
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
else
{
uint32_t x_150; uint32_t x_151; uint8_t x_152; 
x_150 = l_String_Iterator_curr(x_146);
x_151 = 93;
x_152 = x_150 == x_151;
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = l_Lean_Json_Parser_anyCore___main___rarg___closed__4;
x_154 = l_Lean_Json_Parser_anyCore___main___rarg___closed__6;
x_155 = l_Lean_Json_Parser_arrayCore___main(x_153, x_154, x_146);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_155, 1);
x_158 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_155, 1, x_158);
return x_155;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_155, 0);
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_155);
x_161 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
else
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_155);
if (x_163 == 0)
{
return x_155;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_155, 0);
x_165 = lean_ctor_get(x_155, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_155);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = l_String_Iterator_next(x_146);
x_168 = l_Lean_Quickparse_skipWs___main(x_167);
x_169 = l_Lean_Json_Parser_anyCore___main___rarg___closed__7;
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
}
}
}
lean_object* l_Lean_Json_Parser_anyCore___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Json_Parser_anyCore___main___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Json_Parser_anyCore___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_Parser_anyCore___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_Parser_anyCore___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_Parser_anyCore___main___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_Parser_anyCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Json_Parser_anyCore___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Json_Parser_anyCore___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_Parser_anyCore(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Json_Parser_any(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Quickparse_skipWs___main(x_1);
x_3 = l_Lean_Json_Parser_anyCore___main___rarg(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_String_Iterator_hasNext(x_5);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = l_Lean_Quickparse_expectedEndOfInput;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_8);
return x_3;
}
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = l_String_Iterator_hasNext(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_13 = l_Lean_Quickparse_expectedEndOfInput;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Json_parse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("offset ");
return x_1;
}
}
lean_object* l_Lean_Json_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = l_Lean_Json_Parser_any(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Nat_repr(x_9);
x_11 = l_Lean_Json_parse___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l___private_Init_Util_1__mkPanicMessage___closed__3;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_14, x_8);
lean_dec(x_8);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Json_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_Json_Parser(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Quickparse_Monad___closed__1 = _init_l_Lean_Quickparse_Monad___closed__1();
lean_mark_persistent(l_Lean_Quickparse_Monad___closed__1);
l_Lean_Quickparse_Monad___closed__2 = _init_l_Lean_Quickparse_Monad___closed__2();
lean_mark_persistent(l_Lean_Quickparse_Monad___closed__2);
l_Lean_Quickparse_Monad___closed__3 = _init_l_Lean_Quickparse_Monad___closed__3();
lean_mark_persistent(l_Lean_Quickparse_Monad___closed__3);
l_Lean_Quickparse_Monad___closed__4 = _init_l_Lean_Quickparse_Monad___closed__4();
lean_mark_persistent(l_Lean_Quickparse_Monad___closed__4);
l_Lean_Quickparse_Monad___closed__5 = _init_l_Lean_Quickparse_Monad___closed__5();
lean_mark_persistent(l_Lean_Quickparse_Monad___closed__5);
l_Lean_Quickparse_Monad___closed__6 = _init_l_Lean_Quickparse_Monad___closed__6();
lean_mark_persistent(l_Lean_Quickparse_Monad___closed__6);
l_Lean_Quickparse_Monad___closed__7 = _init_l_Lean_Quickparse_Monad___closed__7();
lean_mark_persistent(l_Lean_Quickparse_Monad___closed__7);
l_Lean_Quickparse_Monad___closed__8 = _init_l_Lean_Quickparse_Monad___closed__8();
lean_mark_persistent(l_Lean_Quickparse_Monad___closed__8);
l_Lean_Quickparse_Monad___closed__9 = _init_l_Lean_Quickparse_Monad___closed__9();
lean_mark_persistent(l_Lean_Quickparse_Monad___closed__9);
l_Lean_Quickparse_Monad___closed__10 = _init_l_Lean_Quickparse_Monad___closed__10();
lean_mark_persistent(l_Lean_Quickparse_Monad___closed__10);
l_Lean_Quickparse_Monad = _init_l_Lean_Quickparse_Monad();
lean_mark_persistent(l_Lean_Quickparse_Monad);
l_Lean_Quickparse_unexpectedEndOfInput___closed__1 = _init_l_Lean_Quickparse_unexpectedEndOfInput___closed__1();
lean_mark_persistent(l_Lean_Quickparse_unexpectedEndOfInput___closed__1);
l_Lean_Quickparse_unexpectedEndOfInput = _init_l_Lean_Quickparse_unexpectedEndOfInput();
lean_mark_persistent(l_Lean_Quickparse_unexpectedEndOfInput);
l_Lean_Quickparse_expect___closed__1 = _init_l_Lean_Quickparse_expect___closed__1();
lean_mark_persistent(l_Lean_Quickparse_expect___closed__1);
l_Lean_Quickparse_expectedEndOfInput___closed__1 = _init_l_Lean_Quickparse_expectedEndOfInput___closed__1();
lean_mark_persistent(l_Lean_Quickparse_expectedEndOfInput___closed__1);
l_Lean_Quickparse_expectedEndOfInput = _init_l_Lean_Quickparse_expectedEndOfInput();
lean_mark_persistent(l_Lean_Quickparse_expectedEndOfInput);
l_Lean_Json_Parser_hexChar___closed__1 = _init_l_Lean_Json_Parser_hexChar___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_hexChar___closed__1);
l_Lean_Json_Parser_escapedChar___closed__1 = _init_l_Lean_Json_Parser_escapedChar___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___closed__1);
l_Lean_Json_Parser_escapedChar___boxed__const__1 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__1();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__1);
l_Lean_Json_Parser_escapedChar___boxed__const__2 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__2();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__2);
l_Lean_Json_Parser_escapedChar___boxed__const__3 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__3();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__3);
l_Lean_Json_Parser_escapedChar___boxed__const__4 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__4();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__4);
l_Lean_Json_Parser_escapedChar___boxed__const__5 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__5();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__5);
l_Lean_Json_Parser_escapedChar___boxed__const__6 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__6();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__6);
l_Lean_Json_Parser_escapedChar___boxed__const__7 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__7();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__7);
l_Lean_Json_Parser_escapedChar___boxed__const__8 = _init_l_Lean_Json_Parser_escapedChar___boxed__const__8();
lean_mark_persistent(l_Lean_Json_Parser_escapedChar___boxed__const__8);
l_Lean_Json_Parser_strCore___main___closed__1 = _init_l_Lean_Json_Parser_strCore___main___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_strCore___main___closed__1);
l_Lean_Json_Parser_lookahead___rarg___closed__1 = _init_l_Lean_Json_Parser_lookahead___rarg___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_lookahead___rarg___closed__1);
l_Lean_Json_Parser_natNonZero___closed__1 = _init_l_Lean_Json_Parser_natNonZero___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_natNonZero___closed__1);
l_Lean_Json_Parser_natNonZero___closed__2 = _init_l_Lean_Json_Parser_natNonZero___closed__2();
lean_mark_persistent(l_Lean_Json_Parser_natNonZero___closed__2);
l_Lean_Json_Parser_natNumDigits___closed__1 = _init_l_Lean_Json_Parser_natNumDigits___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_natNumDigits___closed__1);
l_Lean_Json_Parser_natNumDigits___closed__2 = _init_l_Lean_Json_Parser_natNumDigits___closed__2();
lean_mark_persistent(l_Lean_Json_Parser_natNumDigits___closed__2);
l_Lean_Json_Parser_num___closed__1 = _init_l_Lean_Json_Parser_num___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_num___closed__1);
l_Lean_Json_Parser_num___closed__2___boxed__const__1 = _init_l_Lean_Json_Parser_num___closed__2___boxed__const__1();
lean_mark_persistent(l_Lean_Json_Parser_num___closed__2___boxed__const__1);
l_Lean_Json_Parser_num___closed__2 = _init_l_Lean_Json_Parser_num___closed__2();
lean_mark_persistent(l_Lean_Json_Parser_num___closed__2);
l_Lean_Json_Parser_num___closed__3 = _init_l_Lean_Json_Parser_num___closed__3();
lean_mark_persistent(l_Lean_Json_Parser_num___closed__3);
l_Lean_Json_Parser_num___closed__4___boxed__const__1 = _init_l_Lean_Json_Parser_num___closed__4___boxed__const__1();
lean_mark_persistent(l_Lean_Json_Parser_num___closed__4___boxed__const__1);
l_Lean_Json_Parser_num___closed__4 = _init_l_Lean_Json_Parser_num___closed__4();
lean_mark_persistent(l_Lean_Json_Parser_num___closed__4);
l_Lean_Json_Parser_num___closed__5___boxed__const__1 = _init_l_Lean_Json_Parser_num___closed__5___boxed__const__1();
lean_mark_persistent(l_Lean_Json_Parser_num___closed__5___boxed__const__1);
l_Lean_Json_Parser_num___closed__5 = _init_l_Lean_Json_Parser_num___closed__5();
lean_mark_persistent(l_Lean_Json_Parser_num___closed__5);
l_Lean_Json_Parser_num___closed__6 = _init_l_Lean_Json_Parser_num___closed__6();
lean_mark_persistent(l_Lean_Json_Parser_num___closed__6);
l_Lean_Json_Parser_num___closed__7 = _init_l_Lean_Json_Parser_num___closed__7();
lean_mark_persistent(l_Lean_Json_Parser_num___closed__7);
l_Lean_Json_Parser_arrayCore___main___closed__1 = _init_l_Lean_Json_Parser_arrayCore___main___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_arrayCore___main___closed__1);
l_Lean_Json_Parser_objectCore___main___closed__1 = _init_l_Lean_Json_Parser_objectCore___main___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_objectCore___main___closed__1);
l_Lean_Json_Parser_objectCore___main___closed__2 = _init_l_Lean_Json_Parser_objectCore___main___closed__2();
lean_mark_persistent(l_Lean_Json_Parser_objectCore___main___closed__2);
l_Lean_Json_Parser_objectCore___main___closed__3 = _init_l_Lean_Json_Parser_objectCore___main___closed__3();
lean_mark_persistent(l_Lean_Json_Parser_objectCore___main___closed__3);
l_Lean_Json_Parser_anyCore___main___rarg___closed__1 = _init_l_Lean_Json_Parser_anyCore___main___rarg___closed__1();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___main___rarg___closed__1);
l_Lean_Json_Parser_anyCore___main___rarg___closed__2 = _init_l_Lean_Json_Parser_anyCore___main___rarg___closed__2();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___main___rarg___closed__2);
l_Lean_Json_Parser_anyCore___main___rarg___closed__3 = _init_l_Lean_Json_Parser_anyCore___main___rarg___closed__3();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___main___rarg___closed__3);
l_Lean_Json_Parser_anyCore___main___rarg___closed__4 = _init_l_Lean_Json_Parser_anyCore___main___rarg___closed__4();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___main___rarg___closed__4);
l_Lean_Json_Parser_anyCore___main___rarg___closed__5 = _init_l_Lean_Json_Parser_anyCore___main___rarg___closed__5();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___main___rarg___closed__5);
l_Lean_Json_Parser_anyCore___main___rarg___closed__6 = _init_l_Lean_Json_Parser_anyCore___main___rarg___closed__6();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___main___rarg___closed__6);
l_Lean_Json_Parser_anyCore___main___rarg___closed__7 = _init_l_Lean_Json_Parser_anyCore___main___rarg___closed__7();
lean_mark_persistent(l_Lean_Json_Parser_anyCore___main___rarg___closed__7);
l_Lean_Json_parse___closed__1 = _init_l_Lean_Json_parse___closed__1();
lean_mark_persistent(l_Lean_Json_parse___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
