// Lean compiler output
// Module: Lean.Elab.Exception
// Imports: Init Lean.InternalExceptionId Lean.Meta.Exception
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
lean_object* l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3;
lean_object* l_Lean_Elab_throwPostpone___rarg(lean_object*);
lean_object* l_Lean_Elab_registerUnsupportedSyntaxId(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l_Lean_Elab_registerAbortElabId___closed__2;
lean_object* l_Lean_Elab_throwAbort___rarg___closed__1;
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
lean_object* l_Lean_Elab_registerUnsupportedSyntaxId___closed__2;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
lean_object* l_Lean_Elab_registerUnsupportedSyntaxId___closed__1;
lean_object* l_Lean_Elab_throwIllFormedSyntax___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Elab_throwPostpone(lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerPostponeId(lean_object*);
lean_object* l_Lean_Elab_mkMessageCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax___rarg___closed__1;
lean_object* l_Lean_Elab_throwAbort___rarg(lean_object*);
lean_object* l_Lean_Elab_throwAbort(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax___rarg___closed__2;
lean_object* l_Lean_Elab_postponeExceptionId;
lean_object* l_Lean_Elab_throwPostpone___rarg___closed__1;
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__2;
lean_object* l_Lean_Elab_registerAbortElabId___closed__1;
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__4;
lean_object* l_Lean_Elab_abortExceptionId;
lean_object* l_Lean_Elab_registerAbortElabId(lean_object*);
lean_object* l_Lean_Elab_registerPostponeId___closed__2;
lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel(lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerPostponeId___closed__1;
static lean_object* _init_l_Lean_Elab_registerPostponeId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("postpone");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_registerPostponeId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_registerPostponeId___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_registerPostponeId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_registerPostponeId___closed__2;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_registerUnsupportedSyntaxId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unsupportedSyntax");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_registerUnsupportedSyntaxId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_registerUnsupportedSyntaxId___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_registerUnsupportedSyntaxId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_registerUnsupportedSyntaxId___closed__2;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_registerAbortElabId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("abortElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_registerAbortElabId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_registerAbortElabId___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_registerAbortElabId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_registerAbortElabId___closed__2;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_throwPostpone___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_postponeExceptionId;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_throwPostpone___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Elab_throwPostpone___rarg___closed__1;
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_throwPostpone(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwPostpone___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed syntax");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwIllFormedSyntax___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwIllFormedSyntax___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_throwIllFormedSyntax___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3;
x_6 = l_Lean_throwError___rarg(x_1, x_2, x_3, x_4, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_throwIllFormedSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwIllFormedSyntax___rarg), 4, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a universe level named '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already been declared");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_System_FilePath_dirName___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_5);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___rarg(x_1, x_2, x_3, x_4, lean_box(0), x_13);
return x_14;
}
}
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg), 5, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_throwAbort___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_abortExceptionId;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_throwAbort___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Elab_throwAbort___rarg___closed__1;
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_throwAbort(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwAbort___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_mkMessageCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_FileMap_toPosition(x_2, x_5);
x_7 = lean_box(0);
x_8 = l_String_splitAux___main___closed__1;
x_9 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set(x_9, 4, x_3);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_4);
return x_9;
}
}
lean_object* l_Lean_Elab_mkMessageCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Elab_mkMessageCore(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_2);
return x_7;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_InternalExceptionId(lean_object*);
lean_object* initialize_Lean_Meta_Exception(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Exception(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_InternalExceptionId(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Exception(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_registerPostponeId___closed__1 = _init_l_Lean_Elab_registerPostponeId___closed__1();
lean_mark_persistent(l_Lean_Elab_registerPostponeId___closed__1);
l_Lean_Elab_registerPostponeId___closed__2 = _init_l_Lean_Elab_registerPostponeId___closed__2();
lean_mark_persistent(l_Lean_Elab_registerPostponeId___closed__2);
res = l_Lean_Elab_registerPostponeId(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_postponeExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_postponeExceptionId);
lean_dec_ref(res);
l_Lean_Elab_registerUnsupportedSyntaxId___closed__1 = _init_l_Lean_Elab_registerUnsupportedSyntaxId___closed__1();
lean_mark_persistent(l_Lean_Elab_registerUnsupportedSyntaxId___closed__1);
l_Lean_Elab_registerUnsupportedSyntaxId___closed__2 = _init_l_Lean_Elab_registerUnsupportedSyntaxId___closed__2();
lean_mark_persistent(l_Lean_Elab_registerUnsupportedSyntaxId___closed__2);
res = l_Lean_Elab_registerUnsupportedSyntaxId(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_unsupportedSyntaxExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_unsupportedSyntaxExceptionId);
lean_dec_ref(res);
l_Lean_Elab_registerAbortElabId___closed__1 = _init_l_Lean_Elab_registerAbortElabId___closed__1();
lean_mark_persistent(l_Lean_Elab_registerAbortElabId___closed__1);
l_Lean_Elab_registerAbortElabId___closed__2 = _init_l_Lean_Elab_registerAbortElabId___closed__2();
lean_mark_persistent(l_Lean_Elab_registerAbortElabId___closed__2);
res = l_Lean_Elab_registerAbortElabId(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_abortExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_abortExceptionId);
lean_dec_ref(res);
l_Lean_Elab_throwPostpone___rarg___closed__1 = _init_l_Lean_Elab_throwPostpone___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwPostpone___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1);
l_Lean_Elab_throwIllFormedSyntax___rarg___closed__1 = _init_l_Lean_Elab_throwIllFormedSyntax___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwIllFormedSyntax___rarg___closed__1);
l_Lean_Elab_throwIllFormedSyntax___rarg___closed__2 = _init_l_Lean_Elab_throwIllFormedSyntax___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwIllFormedSyntax___rarg___closed__2);
l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3 = _init_l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3);
l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__1 = _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__1);
l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__2 = _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__2);
l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3 = _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__3);
l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__4 = _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__4);
l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__5 = _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__5);
l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6 = _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6();
lean_mark_persistent(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6);
l_Lean_Elab_throwAbort___rarg___closed__1 = _init_l_Lean_Elab_throwAbort___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAbort___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
