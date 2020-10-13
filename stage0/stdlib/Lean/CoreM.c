// Lean compiler output
// Module: Lean.CoreM
// Imports: Init Lean.Util.RecDepth Lean.Util.Trace Lean.Environment Lean.Exception Lean.InternalExceptionId Lean.Eval Lean.MonadEnv
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
lean_object* l_Lean_Core_Lean_MonadTrace___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadRecDepth___closed__3;
lean_object* l_Lean_Core_Lean_MonadEnv___closed__6;
extern lean_object* l_Lean_InternalExceptionId_toString___closed__1;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Core_Lean_MonadNameGenerator;
lean_object* l_Lean_Core_Lean_MonadOptions;
lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_inhabited___closed__1;
lean_object* l_Lean_Core_Lean_Ref;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Core_Lean_MonadOptions___closed__1;
extern lean_object* l_Lean_Environment_Inhabited___closed__4;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Core_hasEval___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_Ref___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_StateRefT_x27_get___at_Lean_Core_Lean_MonadEnv___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadRecDepth___closed__5;
lean_object* l_Lean_Core_Lean_Ref___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_printTraces___at_Lean_Core_hasEval___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadNameGenerator___closed__4;
lean_object* l_Std_PersistentArray_forM___at_Lean_Core_hasEval___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_AddMessageContext;
lean_object* l_Lean_catchInternalIds___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Core_hasEval___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadTrace___closed__3;
lean_object* l_Lean_catchInternalIds___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l_Lean_Core_Lean_MonadNameGenerator___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_catchInternalIds___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
lean_object* l_Lean_Core_CoreM_inhabited(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Exception_inhabited___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Core_CoreM_run_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_catchInternalIds(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forMAux___main___at_Lean_Core_hasEval___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkEmptyEnvironment___closed__1;
lean_object* l_Lean_Core_Lean_MonadTrace___closed__4;
lean_object* l_Lean_Core_Lean_MonadEnv___closed__1;
lean_object* l_Lean_Core_Lean_MonadNameGenerator___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_Ref___closed__3;
lean_object* l_Lean_Core_Lean_MonadEnv___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadEnv___closed__2;
lean_object* l_Lean_Core_Lean_MonadOptions___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_1__mkFreshNameImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_Ref___closed__5;
lean_object* l_Lean_Core_CoreM_run(lean_object*);
lean_object* l_ReaderT_read___at_Lean_Core_Lean_Ref___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_catchInternalId___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Core_hasEval___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadOptions___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadRecDepth___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadEnv___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___at_Lean_Core_Lean_MonadEnv___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadTrace___closed__1;
lean_object* l_Lean_Core_Lean_MonadRecDepth___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Core_hasEval___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_1__mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadTrace___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Core_Lean_Ref___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_CoreM_inhabited___rarg(lean_object*);
lean_object* l_Lean_Core_Lean_Ref___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName___rarg(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_Lean_AddMessageContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadRecDepth___closed__4;
lean_object* l_Lean_Core_State_inhabited___closed__1;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_liftIOCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forM___at_Lean_Core_hasEval___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Core_Lean_Ref___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_catchInternalIds___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadRecDepth___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_printTraces___at_Lean_Core_hasEval___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_hasEval___rarg(lean_object*);
lean_object* l_Lean_Core_Lean_Ref___closed__1;
lean_object* l_Lean_Core_Lean_MonadNameGenerator___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadNameGenerator___closed__2;
lean_object* l_Lean_Core_State_inhabited___closed__2;
lean_object* l_Lean_Core_CoreM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l_IO_println___at_Lean_printTraces___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_Lean_AddMessageContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMaxRecDepth(lean_object*);
lean_object* l_Lean_Core_Lean_MonadTrace___closed__2;
lean_object* l_Lean_Core_Lean_MonadRecDepth;
lean_object* l_Lean_Core_Lean_Ref___closed__4;
lean_object* l_Lean_Core_Lean_MonadEnv___closed__5;
lean_object* l_ReaderT_bind___at_Lean_Core_Lean_Ref___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_MonadIO;
lean_object* l_Lean_Core_Lean_Ref___closed__2;
lean_object* l_Lean_Core_State_inhabited;
lean_object* l_Lean_Core_Lean_MonadEnv___closed__3;
lean_object* l_Lean_Core_Lean_MonadRecDepth___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadEnv___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_CoreM_toIO(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_hasEval(lean_object*);
lean_object* l_Lean_Core_Lean_AddMessageContext___closed__1;
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_catchInternalId(lean_object*, lean_object*);
lean_object* l_Lean_Core_hasEval___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Core_Lean_MonadRecDepth___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_catchInternalId___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadNameGenerator___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadEnv___closed__4;
lean_object* l_Lean_Core_Lean_MonadTrace___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadTrace;
lean_object* l_Lean_Core_liftIOCore(lean_object*);
lean_object* l_Lean_Core_Lean_MonadRecDepth___closed__6;
lean_object* l_Lean_Core_Lean_MonadOptions___closed__2;
lean_object* l_List_elem___main___at_Lean_catchInternalIds___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
lean_object* l_Lean_Core_Lean_MonadEnv___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadTrace___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Unhygienic_run___rarg___closed__1;
lean_object* l_Lean_Core_CoreM_run_x27(lean_object*);
lean_object* l_Std_PersistentArray_forMAux___main___at_Lean_Core_hasEval___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Core_hasEval___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadNameGenerator___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_MonadIO___closed__1;
lean_object* l_Lean_catchInternalId___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadEnv;
lean_object* l_Lean_Core_Lean_MonadNameGenerator___closed__3;
lean_object* l_Lean_Core_Lean_MonadRecDepth___closed__2;
lean_object* l_Lean_Core_CoreM_toIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_liftIOCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_CoreM_inhabited___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Core_Lean_MonadRecDepth___closed__1;
static lean_object* _init_l_Lean_Core_State_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_HashMap_inhabited___closed__1;
x_2 = l_Lean_mkEmptyEnvironment___closed__1;
x_3 = l_Array_empty___closed__1;
x_4 = l_Lean_Environment_Inhabited___closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_State_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Core_State_inhabited___closed__1;
x_2 = l_Lean_Unhygienic_run___rarg___closed__1;
x_3 = l_Lean_NameGenerator_Inhabited___closed__3;
x_4 = l_Lean_TraceState_Inhabited___closed__1;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_State_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_State_inhabited___closed__2;
return x_1;
}
}
lean_object* l_Lean_Core_CoreM_inhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Exception_inhabited___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Core_CoreM_inhabited(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Core_CoreM_inhabited___rarg), 1, 0);
return x_4;
}
}
lean_object* l_Lean_Core_CoreM_inhabited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Core_CoreM_inhabited(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_ReaderT_read___at_Lean_Core_Lean_Ref___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_ReaderT_bind___at_Lean_Core_Lean_Ref___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_ReaderT_bind___at_Lean_Core_Lean_Ref___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_Lean_Ref___spec__2___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Lean_Core_Lean_Ref___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Core_Lean_Ref___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 3);
lean_dec(x_8);
lean_ctor_set(x_4, 3, x_2);
x_9 = lean_apply_3(x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_2);
x_14 = lean_apply_3(x_3, x_13, x_5, x_6);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Core_Lean_Ref___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Core_Lean_Ref___spec__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Lean_Ref___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_Lean_Ref___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Lean_Ref___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_Lean_Ref___closed__1;
x_2 = l_Lean_Core_Lean_Ref___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_Lean_Ref___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_Lean_Ref___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_Lean_Ref___lambda__2), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Lean_Ref___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_Lean_Ref___closed__3;
x_2 = l_Lean_Core_Lean_Ref___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_Lean_Ref() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_Lean_Ref___closed__5;
return x_1;
}
}
lean_object* l_ReaderT_read___at_Lean_Core_Lean_Ref___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_read___at_Lean_Core_Lean_Ref___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Core_Lean_Ref___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_Lean_Ref___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_StateRefT_x27_get___at_Lean_Core_Lean_MonadEnv___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
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
lean_object* l_Lean_Core_Lean_MonadEnv___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Core_Lean_MonadEnv___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_22 = lean_apply_1(x_1, x_18);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_21);
x_24 = lean_st_ref_set(x_3, x_23, x_7);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadEnv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_get___at_Lean_Core_Lean_MonadEnv___spec__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadEnv___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_Lean_MonadEnv___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadEnv___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_Lean_MonadEnv___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadEnv___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_Lean_MonadEnv___closed__2;
x_2 = l_Lean_Core_Lean_MonadEnv___closed__3;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_Lean_Ref___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadEnv___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_Lean_MonadEnv___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadEnv___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_Lean_MonadEnv___closed__4;
x_2 = l_Lean_Core_Lean_MonadEnv___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadEnv() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_Lean_MonadEnv___closed__6;
return x_1;
}
}
lean_object* l_StateRefT_x27_get___at_Lean_Core_Lean_MonadEnv___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_StateRefT_x27_get___at_Lean_Core_Lean_MonadEnv___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Core_Lean_MonadEnv___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_Lean_MonadEnv___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Core_Lean_MonadEnv___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_Lean_MonadEnv___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Core_Lean_MonadOptions___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_Core_Lean_MonadOptions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_Lean_MonadOptions___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadOptions___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_Lean_Ref___closed__1;
x_2 = l_Lean_Core_Lean_MonadOptions___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_Lean_Ref___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadOptions() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_Lean_MonadOptions___closed__2;
return x_1;
}
}
lean_object* l_Lean_Core_Lean_MonadOptions___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_Lean_MonadOptions___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_Lean_AddMessageContext___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 0);
x_10 = l_Lean_MetavarContext_Inhabited___closed__1;
x_11 = l_Lean_LocalContext_Inhabited___closed__2;
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
lean_ctor_set(x_12, 3, x_9);
x_13 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_2, 0);
x_18 = l_Lean_MetavarContext_Inhabited___closed__1;
x_19 = l_Lean_LocalContext_Inhabited___closed__2;
lean_inc(x_17);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_17);
x_21 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
}
static lean_object* _init_l_Lean_Core_Lean_AddMessageContext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_addMessageContextPartial___at_Lean_Core_Lean_AddMessageContext___spec__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Lean_AddMessageContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_Lean_AddMessageContext___closed__1;
return x_1;
}
}
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_Lean_AddMessageContext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at_Lean_Core_Lean_AddMessageContext___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Core_Lean_MonadNameGenerator___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Core_Lean_MonadNameGenerator___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = lean_ctor_get(x_6, 2);
lean_dec(x_9);
lean_ctor_set(x_6, 2, x_1);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_1);
lean_ctor_set(x_20, 3, x_19);
x_21 = lean_st_ref_set(x_3, x_20, x_7);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = lean_box(0);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadNameGenerator___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_Lean_MonadNameGenerator___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadNameGenerator___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_Lean_MonadEnv___closed__2;
x_2 = l_Lean_Core_Lean_MonadNameGenerator___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_Lean_Ref___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadNameGenerator___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_Lean_MonadNameGenerator___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadNameGenerator___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_Lean_MonadNameGenerator___closed__2;
x_2 = l_Lean_Core_Lean_MonadNameGenerator___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadNameGenerator() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_Lean_MonadNameGenerator___closed__4;
return x_1;
}
}
lean_object* l_Lean_Core_Lean_MonadNameGenerator___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_Lean_MonadNameGenerator___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Core_Lean_MonadNameGenerator___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_Lean_MonadNameGenerator___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Core_Lean_MonadRecDepth___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 1);
lean_dec(x_8);
lean_ctor_set(x_4, 1, x_2);
x_9 = lean_apply_3(x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_ctor_get(x_4, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_apply_3(x_3, x_13, x_5, x_6);
return x_14;
}
}
}
lean_object* l_Lean_Core_Lean_MonadRecDepth___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Core_Lean_MonadRecDepth___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_Core_Lean_MonadRecDepth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_Lean_MonadRecDepth___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadRecDepth___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_Lean_Ref___closed__1;
x_2 = l_Lean_Core_Lean_MonadRecDepth___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_Lean_Ref___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadRecDepth___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_Lean_MonadRecDepth___lambda__3___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadRecDepth___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_Lean_Ref___closed__1;
x_2 = l_Lean_Core_Lean_MonadRecDepth___closed__3;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_Lean_Ref___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadRecDepth___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_Lean_MonadRecDepth___lambda__1), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadRecDepth___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Core_Lean_MonadRecDepth___closed__5;
x_2 = l_Lean_Core_Lean_MonadRecDepth___closed__2;
x_3 = l_Lean_Core_Lean_MonadRecDepth___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadRecDepth() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_Lean_MonadRecDepth___closed__6;
return x_1;
}
}
lean_object* l_Lean_Core_Lean_MonadRecDepth___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_Lean_MonadRecDepth___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Core_Lean_MonadRecDepth___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_Lean_MonadRecDepth___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Core_liftIOCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
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
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_io_error_to_string(x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_io_error_to_string(x_17);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
}
}
lean_object* l_Lean_Core_liftIOCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Core_liftIOCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_liftIOCore___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Core_MonadIO___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_MonadIO() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_MonadIO___closed__1;
return x_1;
}
}
lean_object* l_Lean_Core_Lean_MonadTrace___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_apply_1(x_1, x_9);
lean_ctor_set(x_6, 3, x_10);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_22 = lean_apply_1(x_1, x_21);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_22);
x_24 = lean_st_ref_set(x_3, x_23, x_7);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
x_27 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
}
lean_object* l_Lean_Core_Lean_MonadTrace___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_Core_Lean_MonadTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_Lean_MonadTrace___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadTrace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_Lean_MonadEnv___closed__2;
x_2 = l_Lean_Core_Lean_MonadTrace___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Core_Lean_Ref___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadTrace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_Lean_MonadTrace___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadTrace___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_Lean_MonadTrace___closed__3;
x_2 = l_Lean_Core_Lean_MonadTrace___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Core_Lean_MonadTrace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Core_Lean_MonadTrace___closed__4;
return x_1;
}
}
lean_object* l_Lean_Core_Lean_MonadTrace___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_Lean_MonadTrace___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Core_Lean_MonadTrace___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_Lean_MonadTrace___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_CoreM_1__mkFreshNameImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_ctor_set(x_6, 1, x_11);
x_12 = lean_st_ref_set(x_3, x_6, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_3, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_environment_main_module(x_17);
x_19 = l_Lean_addMacroScope(x_18, x_1, x_9);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_environment_main_module(x_22);
x_24 = l_Lean_addMacroScope(x_23, x_1, x_9);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
x_28 = lean_ctor_get(x_6, 2);
x_29 = lean_ctor_get(x_6, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_27, x_30);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_29);
x_33 = lean_st_ref_set(x_3, x_32, x_7);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_st_ref_get(x_3, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_environment_main_module(x_39);
x_41 = l_Lean_addMacroScope(x_40, x_1, x_27);
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_38;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
}
}
lean_object* l___private_Lean_CoreM_1__mkFreshNameImp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_CoreM_1__mkFreshNameImp(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Core_mkFreshUserName___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_CoreM_1__mkFreshNameImp___boxed), 4, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_Lean_Core_mkFreshUserName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_mkFreshUserName___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Core_CoreM_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_st_mk_ref(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_6);
x_8 = lean_apply_3(x_1, x_2, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_6, x_10);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
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
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_6);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_Core_CoreM_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_CoreM_run___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Core_CoreM_run_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_st_mk_ref(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_6);
x_8 = lean_apply_3(x_1, x_2, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_6, x_10);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_6);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Core_CoreM_run_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_CoreM_run_x27___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Core_CoreM_toIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_st_mk_ref(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_6);
x_8 = lean_apply_3(x_1, x_2, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_6, x_10);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
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
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_6);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_MessageData_toString(x_21, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
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
x_34 = !lean_is_exclusive(x_8);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_8, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_19, 0);
lean_inc(x_36);
lean_dec(x_19);
x_37 = l_Nat_repr(x_36);
x_38 = l_Lean_InternalExceptionId_toString___closed__1;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_8, 0, x_40);
return x_8;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_dec(x_8);
x_42 = lean_ctor_get(x_19, 0);
lean_inc(x_42);
lean_dec(x_19);
x_43 = l_Nat_repr(x_42);
x_44 = l_Lean_InternalExceptionId_toString___closed__1;
x_45 = lean_string_append(x_44, x_43);
lean_dec(x_43);
x_46 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
}
}
}
}
lean_object* l_Lean_Core_CoreM_toIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_CoreM_toIO___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Core_hasEval___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget(x_1, x_2);
x_11 = l_Std_PersistentArray_forMAux___main___at_Lean_Core_hasEval___spec__3(x_10, x_3, x_4, x_5);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
lean_dec(x_2);
x_2 = x_14;
x_5 = x_12;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Core_hasEval___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_1, x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_3, 3);
x_13 = l_Lean_MessageData_format(x_11, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_IO_println___at_Lean_printTraces___spec__1(x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_2);
x_2 = x_19;
x_5 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_io_error_to_string(x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_inc(x_12);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_16, 0, x_26);
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_io_error_to_string(x_27);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_inc(x_12);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
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
}
lean_object* l_Std_PersistentArray_forMAux___main___at_Lean_Core_hasEval___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_forMAux___main___at_Lean_Core_hasEval___spec__4(x_5, x_6, x_2, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_forMAux___main___at_Lean_Core_hasEval___spec__5(x_8, x_9, x_2, x_3, x_4);
return x_10;
}
}
}
lean_object* l_Std_PersistentArray_forM___at_Lean_Core_hasEval___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Std_PersistentArray_forMAux___main___at_Lean_Core_hasEval___spec__3(x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_forMAux___main___at_Lean_Core_hasEval___spec__5(x_6, x_9, x_2, x_3, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_printTraces___at_Lean_Core_hasEval___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 3);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Std_PersistentArray_forM___at_Lean_Core_hasEval___spec__2(x_8, x_1, x_2, x_6);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_Lean_Core_hasEval___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = l_Lean_getMaxRecDepth(x_3);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_box(0);
lean_inc(x_3);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_31);
x_33 = l_Lean_Unhygienic_run___rarg___closed__1;
x_34 = l_Lean_NameGenerator_Inhabited___closed__3;
x_35 = l_Lean_TraceState_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_st_mk_ref(x_36, x_6);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_38);
lean_inc(x_32);
x_40 = lean_apply_3(x_4, x_32, x_38, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_printTraces___at_Lean_Core_hasEval___spec__1(x_32, x_38, x_42);
lean_dec(x_32);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_st_ref_get(x_38, x_44);
lean_dec(x_38);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = 1;
x_50 = lean_box(x_49);
x_51 = lean_apply_5(x_1, x_48, x_3, x_41, x_50, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_3);
lean_dec(x_1);
x_52 = lean_ctor_get(x_43, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_dec(x_43);
x_7 = x_52;
x_8 = x_53;
goto block_28;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_3);
lean_dec(x_1);
x_54 = lean_ctor_get(x_40, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_dec(x_40);
x_56 = l_Lean_printTraces___at_Lean_Core_hasEval___spec__1(x_32, x_38, x_55);
lean_dec(x_38);
lean_dec(x_32);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_7 = x_54;
x_8 = x_57;
goto block_28;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_54);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_7 = x_58;
x_8 = x_59;
goto block_28;
}
}
block_28:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_MessageData_toString(x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_13);
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
x_16 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec(x_7);
x_23 = l_Nat_repr(x_22);
x_24 = l_Lean_InternalExceptionId_toString___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_8);
return x_27;
}
}
}
}
lean_object* l_Lean_Core_hasEval___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_hasEval___rarg___lambda__1___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Core_hasEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Core_hasEval___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Core_hasEval___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Core_hasEval___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Core_hasEval___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Core_hasEval___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentArray_forMAux___main___at_Lean_Core_hasEval___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PersistentArray_forMAux___main___at_Lean_Core_hasEval___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Std_PersistentArray_forM___at_Lean_Core_hasEval___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PersistentArray_forM___at_Lean_Core_hasEval___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_printTraces___at_Lean_Core_hasEval___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_printTraces___at_Lean_Core_hasEval___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Core_hasEval___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lean_Core_hasEval___rarg___lambda__1(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_catchInternalId___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, lean_box(0), x_4);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_nat_dec_eq(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_2(x_9, lean_box(0), x_4);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_apply_1(x_3, x_4);
return x_11;
}
}
}
}
lean_object* l_Lean_catchInternalId___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_catchInternalId___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
x_7 = lean_apply_3(x_5, lean_box(0), x_3, x_6);
return x_7;
}
}
lean_object* l_Lean_catchInternalId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_catchInternalId___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_catchInternalId___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_catchInternalId___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
uint8_t l_List_elem___main___at_Lean_catchInternalIds___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_nat_dec_eq(x_1, x_4);
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
lean_object* l_Lean_catchInternalIds___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, lean_box(0), x_4);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = l_List_elem___main___at_Lean_catchInternalIds___spec__1(x_7, x_2);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_2(x_9, lean_box(0), x_4);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_apply_1(x_3, x_4);
return x_11;
}
}
}
}
lean_object* l_Lean_catchInternalIds___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_catchInternalIds___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
x_7 = lean_apply_3(x_5, lean_box(0), x_3, x_6);
return x_7;
}
}
lean_object* l_Lean_catchInternalIds(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_catchInternalIds___rarg), 4, 0);
return x_3;
}
}
lean_object* l_List_elem___main___at_Lean_catchInternalIds___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___main___at_Lean_catchInternalIds___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_catchInternalIds___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_catchInternalIds___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_RecDepth(lean_object*);
lean_object* initialize_Lean_Util_Trace(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Exception(lean_object*);
lean_object* initialize_Lean_InternalExceptionId(lean_object*);
lean_object* initialize_Lean_Eval(lean_object*);
lean_object* initialize_Lean_MonadEnv(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_CoreM(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_RecDepth(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Trace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_InternalExceptionId(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Eval(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MonadEnv(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Core_State_inhabited___closed__1 = _init_l_Lean_Core_State_inhabited___closed__1();
lean_mark_persistent(l_Lean_Core_State_inhabited___closed__1);
l_Lean_Core_State_inhabited___closed__2 = _init_l_Lean_Core_State_inhabited___closed__2();
lean_mark_persistent(l_Lean_Core_State_inhabited___closed__2);
l_Lean_Core_State_inhabited = _init_l_Lean_Core_State_inhabited();
lean_mark_persistent(l_Lean_Core_State_inhabited);
l_Lean_Core_Lean_Ref___closed__1 = _init_l_Lean_Core_Lean_Ref___closed__1();
lean_mark_persistent(l_Lean_Core_Lean_Ref___closed__1);
l_Lean_Core_Lean_Ref___closed__2 = _init_l_Lean_Core_Lean_Ref___closed__2();
lean_mark_persistent(l_Lean_Core_Lean_Ref___closed__2);
l_Lean_Core_Lean_Ref___closed__3 = _init_l_Lean_Core_Lean_Ref___closed__3();
lean_mark_persistent(l_Lean_Core_Lean_Ref___closed__3);
l_Lean_Core_Lean_Ref___closed__4 = _init_l_Lean_Core_Lean_Ref___closed__4();
lean_mark_persistent(l_Lean_Core_Lean_Ref___closed__4);
l_Lean_Core_Lean_Ref___closed__5 = _init_l_Lean_Core_Lean_Ref___closed__5();
lean_mark_persistent(l_Lean_Core_Lean_Ref___closed__5);
l_Lean_Core_Lean_Ref = _init_l_Lean_Core_Lean_Ref();
lean_mark_persistent(l_Lean_Core_Lean_Ref);
l_Lean_Core_Lean_MonadEnv___closed__1 = _init_l_Lean_Core_Lean_MonadEnv___closed__1();
lean_mark_persistent(l_Lean_Core_Lean_MonadEnv___closed__1);
l_Lean_Core_Lean_MonadEnv___closed__2 = _init_l_Lean_Core_Lean_MonadEnv___closed__2();
lean_mark_persistent(l_Lean_Core_Lean_MonadEnv___closed__2);
l_Lean_Core_Lean_MonadEnv___closed__3 = _init_l_Lean_Core_Lean_MonadEnv___closed__3();
lean_mark_persistent(l_Lean_Core_Lean_MonadEnv___closed__3);
l_Lean_Core_Lean_MonadEnv___closed__4 = _init_l_Lean_Core_Lean_MonadEnv___closed__4();
lean_mark_persistent(l_Lean_Core_Lean_MonadEnv___closed__4);
l_Lean_Core_Lean_MonadEnv___closed__5 = _init_l_Lean_Core_Lean_MonadEnv___closed__5();
lean_mark_persistent(l_Lean_Core_Lean_MonadEnv___closed__5);
l_Lean_Core_Lean_MonadEnv___closed__6 = _init_l_Lean_Core_Lean_MonadEnv___closed__6();
lean_mark_persistent(l_Lean_Core_Lean_MonadEnv___closed__6);
l_Lean_Core_Lean_MonadEnv = _init_l_Lean_Core_Lean_MonadEnv();
lean_mark_persistent(l_Lean_Core_Lean_MonadEnv);
l_Lean_Core_Lean_MonadOptions___closed__1 = _init_l_Lean_Core_Lean_MonadOptions___closed__1();
lean_mark_persistent(l_Lean_Core_Lean_MonadOptions___closed__1);
l_Lean_Core_Lean_MonadOptions___closed__2 = _init_l_Lean_Core_Lean_MonadOptions___closed__2();
lean_mark_persistent(l_Lean_Core_Lean_MonadOptions___closed__2);
l_Lean_Core_Lean_MonadOptions = _init_l_Lean_Core_Lean_MonadOptions();
lean_mark_persistent(l_Lean_Core_Lean_MonadOptions);
l_Lean_Core_Lean_AddMessageContext___closed__1 = _init_l_Lean_Core_Lean_AddMessageContext___closed__1();
lean_mark_persistent(l_Lean_Core_Lean_AddMessageContext___closed__1);
l_Lean_Core_Lean_AddMessageContext = _init_l_Lean_Core_Lean_AddMessageContext();
lean_mark_persistent(l_Lean_Core_Lean_AddMessageContext);
l_Lean_Core_Lean_MonadNameGenerator___closed__1 = _init_l_Lean_Core_Lean_MonadNameGenerator___closed__1();
lean_mark_persistent(l_Lean_Core_Lean_MonadNameGenerator___closed__1);
l_Lean_Core_Lean_MonadNameGenerator___closed__2 = _init_l_Lean_Core_Lean_MonadNameGenerator___closed__2();
lean_mark_persistent(l_Lean_Core_Lean_MonadNameGenerator___closed__2);
l_Lean_Core_Lean_MonadNameGenerator___closed__3 = _init_l_Lean_Core_Lean_MonadNameGenerator___closed__3();
lean_mark_persistent(l_Lean_Core_Lean_MonadNameGenerator___closed__3);
l_Lean_Core_Lean_MonadNameGenerator___closed__4 = _init_l_Lean_Core_Lean_MonadNameGenerator___closed__4();
lean_mark_persistent(l_Lean_Core_Lean_MonadNameGenerator___closed__4);
l_Lean_Core_Lean_MonadNameGenerator = _init_l_Lean_Core_Lean_MonadNameGenerator();
lean_mark_persistent(l_Lean_Core_Lean_MonadNameGenerator);
l_Lean_Core_Lean_MonadRecDepth___closed__1 = _init_l_Lean_Core_Lean_MonadRecDepth___closed__1();
lean_mark_persistent(l_Lean_Core_Lean_MonadRecDepth___closed__1);
l_Lean_Core_Lean_MonadRecDepth___closed__2 = _init_l_Lean_Core_Lean_MonadRecDepth___closed__2();
lean_mark_persistent(l_Lean_Core_Lean_MonadRecDepth___closed__2);
l_Lean_Core_Lean_MonadRecDepth___closed__3 = _init_l_Lean_Core_Lean_MonadRecDepth___closed__3();
lean_mark_persistent(l_Lean_Core_Lean_MonadRecDepth___closed__3);
l_Lean_Core_Lean_MonadRecDepth___closed__4 = _init_l_Lean_Core_Lean_MonadRecDepth___closed__4();
lean_mark_persistent(l_Lean_Core_Lean_MonadRecDepth___closed__4);
l_Lean_Core_Lean_MonadRecDepth___closed__5 = _init_l_Lean_Core_Lean_MonadRecDepth___closed__5();
lean_mark_persistent(l_Lean_Core_Lean_MonadRecDepth___closed__5);
l_Lean_Core_Lean_MonadRecDepth___closed__6 = _init_l_Lean_Core_Lean_MonadRecDepth___closed__6();
lean_mark_persistent(l_Lean_Core_Lean_MonadRecDepth___closed__6);
l_Lean_Core_Lean_MonadRecDepth = _init_l_Lean_Core_Lean_MonadRecDepth();
lean_mark_persistent(l_Lean_Core_Lean_MonadRecDepth);
l_Lean_Core_MonadIO___closed__1 = _init_l_Lean_Core_MonadIO___closed__1();
lean_mark_persistent(l_Lean_Core_MonadIO___closed__1);
l_Lean_Core_MonadIO = _init_l_Lean_Core_MonadIO();
lean_mark_persistent(l_Lean_Core_MonadIO);
l_Lean_Core_Lean_MonadTrace___closed__1 = _init_l_Lean_Core_Lean_MonadTrace___closed__1();
lean_mark_persistent(l_Lean_Core_Lean_MonadTrace___closed__1);
l_Lean_Core_Lean_MonadTrace___closed__2 = _init_l_Lean_Core_Lean_MonadTrace___closed__2();
lean_mark_persistent(l_Lean_Core_Lean_MonadTrace___closed__2);
l_Lean_Core_Lean_MonadTrace___closed__3 = _init_l_Lean_Core_Lean_MonadTrace___closed__3();
lean_mark_persistent(l_Lean_Core_Lean_MonadTrace___closed__3);
l_Lean_Core_Lean_MonadTrace___closed__4 = _init_l_Lean_Core_Lean_MonadTrace___closed__4();
lean_mark_persistent(l_Lean_Core_Lean_MonadTrace___closed__4);
l_Lean_Core_Lean_MonadTrace = _init_l_Lean_Core_Lean_MonadTrace();
lean_mark_persistent(l_Lean_Core_Lean_MonadTrace);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
