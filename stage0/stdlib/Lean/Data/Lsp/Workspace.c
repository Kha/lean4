// Lean compiler output
// Module: Lean.Data.Lsp.Workspace
// Imports: Init Lean.Data.Lsp.Basic Lean.Data.Json
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
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_Location_hasFromJson___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_WorkspaceFolder_hasFromJson(lean_object*);
lean_object* l_Lean_Lsp_WorkspaceFolder_hasToJson___boxed(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_Command_hasFromJson___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_WorkspaceFolder_hasToJson(lean_object*);
lean_object* l_Lean_Lsp_WorkspaceFolder_hasFromJson___boxed(lean_object*);
lean_object* l_Lean_Lsp_WorkspaceFolder_hasFromJson___closed__1;
lean_object* l_Lean_Json_mkObj(lean_object*);
extern lean_object* l_Lean_Lsp_Location_hasFromJson___closed__1;
static lean_object* _init_l_Lean_Lsp_WorkspaceFolder_hasFromJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("name");
return x_1;
}
}
lean_object* l_Lean_Lsp_WorkspaceFolder_hasFromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Lsp_Location_hasFromJson___closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_Location_hasFromJson___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Lsp_WorkspaceFolder_hasFromJson___closed__1;
x_7 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_Command_hasFromJson___spec__1(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
}
lean_object* l_Lean_Lsp_WorkspaceFolder_hasFromJson___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_WorkspaceFolder_hasFromJson(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Lsp_WorkspaceFolder_hasToJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_2);
x_5 = l_Lean_Lsp_Location_hasFromJson___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_inc(x_3);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_3);
x_8 = l_Lean_Lsp_WorkspaceFolder_hasFromJson___closed__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Json_mkObj(x_12);
return x_13;
}
}
lean_object* l_Lean_Lsp_WorkspaceFolder_hasToJson___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_WorkspaceFolder_hasToJson(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Basic(lean_object*);
lean_object* initialize_Lean_Data_Json(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Data_Lsp_Workspace(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Lsp_WorkspaceFolder_hasFromJson___closed__1 = _init_l_Lean_Lsp_WorkspaceFolder_hasFromJson___closed__1();
lean_mark_persistent(l_Lean_Lsp_WorkspaceFolder_hasFromJson___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
