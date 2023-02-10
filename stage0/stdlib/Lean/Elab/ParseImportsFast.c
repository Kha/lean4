// Lean compiler output
// Module: Lean.Elab.ParseImportsFast
// Imports: Init Lean.Parser.Module
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_List_join___rarg(lean_object*);
static lean_object* l_Lean_ParseImports_State_imports___default___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdCont___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_andthen(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_finishCommentBlock_eoi___closed__2;
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2;
static lean_object* l_Lean_ParseImports_instInhabitedState___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent_parse(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestFast___boxed(lean_object*);
extern uint32_t l_Lean_idBeginEscape;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1878_(lean_object*);
static lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1693____closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pos___default;
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_error_x3f___default;
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_takeWhile___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushModule___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_privateOpt___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_parseImports_x27___closed__1;
static lean_object* l_Lean_ParseImports_moduleIdent_parse___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil(lean_object*, lean_object*, lean_object*);
uint8_t l_Char_isAlphanum(uint32_t);
uint8_t l_Char_isWhitespace(uint32_t);
static lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__2;
static lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____closed__2;
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___rarg(lean_object*);
static lean_object* l_Lean_ParseImports_whitespace___closed__2;
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_preludeOpt(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1;
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__2;
static lean_object* l_Lean_ParseImports_moduleIdent_parse___closed__4;
static lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1;
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_privateOpt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdCont(lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1;
static lean_object* l_Lean_ParseImports_main___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_many(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_State_nextPriv___default;
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_State_mkEOIError___closed__2;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkEOIError(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____spec__3(size_t, size_t, lean_object*);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
uint8_t l_Lean_isLetterLike(uint32_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1878____spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent_parse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instAndThenParser(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____spec__3___boxed(lean_object*, lean_object*, lean_object*);
extern uint32_t l_Lean_idEndEscape;
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestCold___boxed(lean_object*);
static lean_object* l_Lean_ParseImports_State_mkEOIError___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_privateOpt___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_parseImports_x27___closed__2;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkError(lean_object*, lean_object*);
static lean_object* l_Lean_instToJsonImport___closed__1;
static lean_object* l_Lean_ParseImports_moduleIdent_parse___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1693_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isSubScriptAlnum(uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock_eoi(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseImports_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrintImportResult_imports_x3f___default;
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_parseImports_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrintImportResult_errors___default;
static lean_object* l_Lean_ParseImports_whitespace___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_main(lean_object*, lean_object*);
static lean_object* l_Lean_instToJsonPrintImportResult___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent(uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__1;
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportsResult;
LEAN_EXPORT lean_object* l_Lean_ParseImports_preludeOpt___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____closed__1;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushModule(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_takeWhile___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestCold(uint32_t);
static lean_object* l_Lean_ParseImports_finishCommentBlock_eoi___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_privateOpt___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedState;
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_setPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToJsonPrintImportsResult___closed__1;
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_imports___default;
LEAN_EXPORT lean_object* l_Lean_instToJsonImport;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1;
uint8_t l_Lean_isIdFirst(uint32_t);
LEAN_EXPORT lean_object* lean_print_imports_json(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1878____spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ParseImports_moduleIdent_parse___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestFast(uint32_t);
static lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1693____closed__2;
LEAN_EXPORT lean_object* l_Lean_instToJsonPrintImportResult;
static lean_object* _init_l_Lean_ParseImports_State_imports___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ParseImports_State_imports___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ParseImports_State_imports___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_State_pos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_State_error_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint8_t _init_l_Lean_ParseImports_State_nextPriv___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_ParseImports_State_imports___default___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = 0;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_ParseImports_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ParseImports_instInhabitedState___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ParseImports_instInhabitedParser___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ParseImports_instInhabitedParser___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instInhabitedParser___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ParseImports_instInhabitedParser(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_setPos(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkError(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
lean_dec(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_1, 2, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_8);
return x_10;
}
}
}
static lean_object* _init_l_Lean_ParseImports_State_mkEOIError___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected end of input", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_State_mkEOIError___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParseImports_State_mkEOIError___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_mkEOIError(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_dec(x_3);
x_4 = l_Lean_ParseImports_State_mkEOIError___closed__2;
lean_ctor_set(x_1, 2, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_8 = l_Lean_ParseImports_State_mkEOIError___closed__2;
x_9 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = lean_string_utf8_next(x_2, x_3);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_10 = lean_string_utf8_next(x_2, x_3);
x_11 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_State_next(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
lean_dec(x_6);
x_7 = lean_string_utf8_next_fast(x_2, x_3);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_11 = lean_string_utf8_next_fast(x_2, x_3);
x_12 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*3, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_next_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ParseImports_State_next_x27(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_ParseImports_finishCommentBlock_eoi___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unterminated comment", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_finishCommentBlock_eoi___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParseImports_finishCommentBlock_eoi___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock_eoi(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_dec(x_3);
x_4 = l_Lean_ParseImports_finishCommentBlock_eoi___closed__2;
lean_ctor_set(x_1, 2, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_8 = l_Lean_ParseImports_finishCommentBlock_eoi___closed__2;
x_9 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_8 = lean_string_utf8_at_end(x_2, x_5);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_11 = 45;
x_12 = lean_uint32_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 47;
x_14 = lean_uint32_dec_eq(x_9, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_3, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_3, 0);
lean_dec(x_18);
lean_ctor_set(x_3, 1, x_10);
goto _start;
}
else
{
lean_object* x_20; 
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_6);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_7);
x_3 = x_20;
goto _start;
}
}
else
{
uint8_t x_22; 
x_22 = lean_string_utf8_at_end(x_2, x_10);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_3, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_3, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_3, 0);
lean_dec(x_26);
x_27 = lean_string_utf8_get_fast(x_2, x_10);
x_28 = lean_uint32_dec_eq(x_27, x_11);
if (x_28 == 0)
{
lean_ctor_set(x_3, 1, x_10);
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_1, x_30);
lean_dec(x_1);
x_32 = lean_string_utf8_next_fast(x_2, x_10);
lean_dec(x_10);
lean_ctor_set(x_3, 1, x_32);
x_1 = x_31;
goto _start;
}
}
else
{
uint32_t x_34; uint8_t x_35; 
lean_dec(x_3);
x_34 = lean_string_utf8_get_fast(x_2, x_10);
x_35 = lean_uint32_dec_eq(x_34, x_11);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_10);
lean_ctor_set(x_36, 2, x_6);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_7);
x_3 = x_36;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_1, x_38);
lean_dec(x_1);
x_40 = lean_string_utf8_next_fast(x_2, x_10);
lean_dec(x_10);
x_41 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_6);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_7);
x_1 = x_39;
x_3 = x_41;
goto _start;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_43 = l_Lean_ParseImports_finishCommentBlock_eoi(x_3);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = lean_string_utf8_at_end(x_2, x_10);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_3);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint32_t x_49; uint32_t x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_3, 2);
lean_dec(x_46);
x_47 = lean_ctor_get(x_3, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_3, 0);
lean_dec(x_48);
x_49 = lean_string_utf8_get_fast(x_2, x_10);
x_50 = 47;
x_51 = lean_uint32_dec_eq(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_string_utf8_next_fast(x_2, x_10);
lean_dec(x_10);
lean_ctor_set(x_3, 1, x_52);
goto _start;
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_dec_eq(x_1, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_nat_sub(x_1, x_54);
lean_dec(x_1);
x_57 = lean_string_utf8_next_fast(x_2, x_10);
lean_dec(x_10);
lean_ctor_set(x_3, 1, x_57);
x_1 = x_56;
goto _start;
}
else
{
lean_object* x_59; 
lean_dec(x_1);
x_59 = lean_string_utf8_next(x_2, x_10);
lean_dec(x_10);
lean_ctor_set(x_3, 1, x_59);
return x_3;
}
}
}
else
{
uint32_t x_60; uint32_t x_61; uint8_t x_62; 
lean_dec(x_3);
x_60 = lean_string_utf8_get_fast(x_2, x_10);
x_61 = 47;
x_62 = lean_uint32_dec_eq(x_60, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_string_utf8_next_fast(x_2, x_10);
lean_dec(x_10);
x_64 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_64, 0, x_4);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_6);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_7);
x_3 = x_64;
goto _start;
}
else
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_dec_eq(x_1, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_nat_sub(x_1, x_66);
lean_dec(x_1);
x_69 = lean_string_utf8_next_fast(x_2, x_10);
lean_dec(x_10);
x_70 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_70, 0, x_4);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_6);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_7);
x_1 = x_68;
x_3 = x_70;
goto _start;
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_1);
x_72 = lean_string_utf8_next(x_2, x_10);
lean_dec(x_10);
x_73 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_73, 0, x_4);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_6);
lean_ctor_set_uint8(x_73, sizeof(void*)*3, x_7);
return x_73;
}
}
}
}
else
{
lean_object* x_74; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_74 = l_Lean_ParseImports_finishCommentBlock_eoi(x_3);
return x_74;
}
}
}
else
{
lean_object* x_75; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_75 = l_Lean_ParseImports_finishCommentBlock_eoi(x_3);
return x_75;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_finishCommentBlock___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_finishCommentBlock(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_8 = lean_string_utf8_at_end(x_2, x_5);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = lean_box_uint32(x_9);
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_dec(x_16);
x_17 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_17);
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_19 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_6);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_7);
x_3 = x_20;
goto _start;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_takeUntil(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_takeWhile___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_8 = lean_string_utf8_at_end(x_2, x_5);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = lean_box_uint32(x_9);
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_dec(x_16);
x_17 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_17);
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_19 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_6);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_7);
x_3 = x_20;
goto _start;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_takeWhile___spec__1(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_takeWhile___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_takeWhile___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeWhile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_takeWhile(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_andthen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_apply_2(x_2, x_3, x_5);
return x_7;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_instAndThenParser(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_apply_3(x_2, x_7, x_3, x_5);
return x_8;
}
else
{
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_7 = lean_string_utf8_at_end(x_1, x_4);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_1, x_4);
x_9 = 10;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
x_15 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_15);
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_5);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_6);
x_2 = x_18;
goto _start;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
}
}
static lean_object* _init_l_Lean_ParseImports_whitespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tabs are not allowed; please configure your editor to expand them", 65);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_whitespace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParseImports_whitespace___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_7 = lean_string_utf8_at_end(x_1, x_4);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_1, x_4);
x_9 = 9;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Char_isWhitespace(x_8);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 45;
x_13 = lean_uint32_dec_eq(x_8, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 47;
x_15 = lean_uint32_dec_eq(x_8, x_14);
if (x_15 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_17 = lean_string_utf8_get(x_1, x_16);
x_18 = lean_uint32_dec_eq(x_17, x_12);
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; 
x_19 = lean_string_utf8_next(x_1, x_16);
lean_dec(x_16);
x_20 = lean_string_utf8_get(x_1, x_19);
x_21 = lean_uint32_dec_eq(x_20, x_12);
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 33;
x_23 = lean_uint32_dec_eq(x_20, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_2, 2);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_2, 0);
lean_dec(x_27);
x_28 = lean_string_utf8_next(x_1, x_19);
lean_dec(x_19);
lean_ctor_set(x_2, 1, x_28);
x_29 = lean_unsigned_to_nat(1u);
x_30 = l_Lean_ParseImports_finishCommentBlock(x_29, x_1, x_2);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
x_2 = x_30;
goto _start;
}
else
{
lean_dec(x_31);
return x_30;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_33 = lean_string_utf8_next(x_1, x_19);
lean_dec(x_19);
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_3);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_5);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_6);
x_35 = lean_unsigned_to_nat(1u);
x_36 = l_Lean_ParseImports_finishCommentBlock(x_35, x_1, x_34);
x_37 = lean_ctor_get(x_36, 2);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
x_2 = x_36;
goto _start;
}
else
{
lean_dec(x_37);
return x_36;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_3);
return x_2;
}
}
else
{
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_3);
return x_2;
}
}
}
}
else
{
lean_object* x_39; uint32_t x_40; uint8_t x_41; 
x_39 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_40 = lean_string_utf8_get(x_1, x_39);
x_41 = lean_uint32_dec_eq(x_40, x_12);
if (x_41 == 0)
{
lean_dec(x_39);
lean_dec(x_5);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_2);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_2, 2);
lean_dec(x_43);
x_44 = lean_ctor_get(x_2, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_2, 0);
lean_dec(x_45);
x_46 = lean_string_utf8_next(x_1, x_39);
lean_dec(x_39);
lean_ctor_set(x_2, 1, x_46);
x_47 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1(x_1, x_2);
x_48 = lean_ctor_get(x_47, 2);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
x_2 = x_47;
goto _start;
}
else
{
lean_dec(x_48);
return x_47;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_2);
x_50 = lean_string_utf8_next(x_1, x_39);
lean_dec(x_39);
x_51 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_5);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_6);
x_52 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1(x_1, x_51);
x_53 = lean_ctor_get(x_52, 2);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
x_2 = x_52;
goto _start;
}
else
{
lean_dec(x_53);
return x_52;
}
}
}
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_2);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_2, 2);
lean_dec(x_56);
x_57 = lean_ctor_get(x_2, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_2, 0);
lean_dec(x_58);
x_59 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_59);
goto _start;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_2);
x_61 = lean_string_utf8_next(x_1, x_4);
lean_dec(x_4);
x_62 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_62, 0, x_3);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_5);
lean_ctor_set_uint8(x_62, sizeof(void*)*3, x_6);
x_2 = x_62;
goto _start;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_5);
x_64 = !lean_is_exclusive(x_2);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_2, 2);
lean_dec(x_65);
x_66 = lean_ctor_get(x_2, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_2, 0);
lean_dec(x_67);
x_68 = l_Lean_ParseImports_whitespace___closed__2;
lean_ctor_set(x_2, 2, x_68);
return x_2;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_2);
x_69 = l_Lean_ParseImports_whitespace___closed__2;
x_70 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_70, 0, x_3);
lean_ctor_set(x_70, 1, x_4);
lean_ctor_set(x_70, 2, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_6);
return x_70;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_whitespace___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_whitespace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_whitespace(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_string_utf8_at_end(x_1, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_string_utf8_at_end(x_4, x_7);
if (x_9 == 0)
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_10 = lean_string_utf8_get_fast(x_1, x_6);
x_11 = lean_string_utf8_get_fast(x_4, x_7);
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_13 = lean_apply_2(x_2, x_4, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_string_utf8_next_fast(x_1, x_6);
lean_dec(x_6);
x_15 = lean_string_utf8_next_fast(x_4, x_7);
lean_dec(x_7);
x_6 = x_14;
x_7 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_17 = lean_apply_2(x_2, x_4, x_5);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_6);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 1);
lean_dec(x_19);
lean_ctor_set(x_5, 1, x_7);
x_20 = l_Lean_ParseImports_whitespace(x_4, x_5);
x_21 = lean_apply_2(x_3, x_4, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 2);
x_24 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_7);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_24);
x_26 = l_Lean_ParseImports_whitespace(x_4, x_25);
x_27 = lean_apply_2(x_3, x_4, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ParseImports_keywordCore_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_ParseImports_keywordCore_go(x_1, x_2, x_3, x_4, x_5, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ParseImports_keywordCore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("`", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` expected", 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_string_utf8_at_end(x_3, x_6);
if (x_8 == 0)
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = lean_string_utf8_get_fast(x_3, x_6);
x_11 = lean_uint32_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
x_12 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1;
x_13 = lean_string_append(x_12, x_1);
x_14 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_4, 2);
lean_dec(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_4, 2, x_18);
return x_4;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_4);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_15);
x_23 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_25 = lean_string_utf8_next_fast(x_3, x_6);
lean_dec(x_6);
x_5 = x_24;
x_6 = x_25;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_5);
x_27 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1;
x_28 = lean_string_append(x_27, x_1);
x_29 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_4, 2);
lean_dec(x_32);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_4, 2, x_33);
return x_4;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_4, 0);
x_35 = lean_ctor_get(x_4, 1);
x_36 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_30);
x_38 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_4);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_4, 1);
lean_dec(x_40);
lean_ctor_set(x_4, 1, x_6);
x_41 = l_Lean_ParseImports_whitespace(x_3, x_4);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_4, 0);
x_43 = lean_ctor_get(x_4, 2);
x_44 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_4);
x_45 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_6);
lean_ctor_set(x_45, 2, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_44);
x_46 = l_Lean_ParseImports_whitespace(x_3, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1(x_1, x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keyword___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_keyword(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdCont(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; uint32_t x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_string_utf8_get(x_1, x_3);
x_5 = 46;
x_6 = lean_uint32_dec_eq(x_4, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_string_utf8_next(x_1, x_3);
x_9 = lean_string_utf8_at_end(x_1, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = lean_string_utf8_get_fast(x_1, x_8);
lean_dec(x_8);
x_11 = l_Lean_isIdFirst(x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = l_Lean_idBeginEscape;
x_13 = lean_uint32_dec_eq(x_10, x_12);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = 0;
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdCont___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_ParseImports_isIdCont(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushModule(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = 0;
x_7 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1 + 1, x_2);
x_8 = lean_array_push(x_5, x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_13 = 0;
x_14 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1 + 1, x_2);
x_15 = lean_array_push(x_9, x_14);
x_16 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_State_pushModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_ParseImports_State_pushModule(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestCold(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 95;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 39;
x_5 = lean_uint32_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint32_t x_6; uint8_t x_7; 
x_6 = 33;
x_7 = lean_uint32_dec_eq(x_1, x_6);
if (x_7 == 0)
{
uint32_t x_8; uint8_t x_9; 
x_8 = 63;
x_9 = lean_uint32_dec_eq(x_1, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_isLetterLike(x_1);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_isSubScriptAlnum(x_1);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestCold___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParseImports_isIdRestCold(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_ParseImports_isIdRestFast(uint32_t x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Char_isAlphanum(x_1);
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 46;
x_4 = lean_uint32_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 10;
x_6 = lean_uint32_dec_eq(x_1, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 32;
x_8 = lean_uint32_dec_eq(x_1, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 95;
x_10 = lean_uint32_dec_eq(x_1, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 39;
x_12 = lean_uint32_dec_eq(x_1, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 33;
x_14 = lean_uint32_dec_eq(x_1, x_13);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 63;
x_16 = lean_uint32_dec_eq(x_1, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_isLetterLike(x_1);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_isSubScriptAlnum(x_1);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = 1;
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = 1;
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = 1;
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = 1;
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_isIdRestFast___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_ParseImports_isIdRestFast(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_16; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_16 = lean_string_utf8_at_end(x_1, x_3);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = lean_string_utf8_get_fast(x_1, x_3);
x_18 = l_Char_isAlphanum(x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 46;
x_20 = lean_uint32_dec_eq(x_17, x_19);
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 10;
x_22 = lean_uint32_dec_eq(x_17, x_21);
if (x_22 == 0)
{
uint32_t x_23; uint8_t x_24; 
x_23 = 32;
x_24 = lean_uint32_dec_eq(x_17, x_23);
if (x_24 == 0)
{
uint32_t x_25; uint8_t x_26; 
x_25 = 95;
x_26 = lean_uint32_dec_eq(x_17, x_25);
if (x_26 == 0)
{
uint32_t x_27; uint8_t x_28; 
x_27 = 39;
x_28 = lean_uint32_dec_eq(x_17, x_27);
if (x_28 == 0)
{
uint32_t x_29; uint8_t x_30; 
x_29 = 33;
x_30 = lean_uint32_dec_eq(x_17, x_29);
if (x_30 == 0)
{
uint32_t x_31; uint8_t x_32; 
x_31 = 63;
x_32 = lean_uint32_dec_eq(x_17, x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_isLetterLike(x_17);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_isSubScriptAlnum(x_17);
if (x_34 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_35; 
x_35 = lean_box(0);
x_4 = x_35;
goto block_15;
}
}
else
{
lean_object* x_36; 
x_36 = lean_box(0);
x_4 = x_36;
goto block_15;
}
}
else
{
lean_object* x_37; 
x_37 = lean_box(0);
x_4 = x_37;
goto block_15;
}
}
else
{
lean_object* x_38; 
x_38 = lean_box(0);
x_4 = x_38;
goto block_15;
}
}
else
{
lean_object* x_39; 
x_39 = lean_box(0);
x_4 = x_39;
goto block_15;
}
}
else
{
lean_object* x_40; 
x_40 = lean_box(0);
x_4 = x_40;
goto block_15;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
else
{
lean_dec(x_3);
return x_2;
}
}
else
{
lean_object* x_41; 
x_41 = lean_box(0);
x_4 = x_41;
goto block_15;
}
}
else
{
lean_dec(x_3);
return x_2;
}
block_15:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_string_utf8_next_fast(x_1, x_3);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
lean_ctor_set(x_2, 1, x_6);
goto _start;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_6);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_12);
x_2 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_7 = lean_string_utf8_at_end(x_1, x_4);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_1, x_4);
x_9 = l_Lean_idEndEscape;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
x_15 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_15);
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_5);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_6);
x_2 = x_18;
goto _start;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
}
}
static lean_object* _init_l_Lean_ParseImports_moduleIdent_parse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected identifier", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_moduleIdent_parse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParseImports_moduleIdent_parse___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ParseImports_moduleIdent_parse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unterminated identifier escape", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_moduleIdent_parse___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParseImports_moduleIdent_parse___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent_parse(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_9 = lean_string_utf8_at_end(x_2, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; uint32_t x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_4, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_4, 0);
lean_dec(x_13);
x_14 = lean_string_utf8_get_fast(x_2, x_6);
x_15 = l_Lean_idBeginEscape;
x_16 = lean_uint32_dec_eq(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_isIdFirst(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_3);
x_18 = l_Lean_ParseImports_moduleIdent_parse___closed__2;
lean_ctor_set(x_4, 2, x_18);
return x_4;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_36; uint32_t x_37; uint8_t x_38; 
x_19 = lean_string_utf8_next_fast(x_2, x_6);
lean_ctor_set(x_4, 1, x_19);
x_20 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1(x_2, x_4);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_string_utf8_extract(x_2, x_6, x_21);
lean_dec(x_6);
x_23 = l_Lean_Name_str___override(x_3, x_22);
x_36 = lean_string_utf8_get(x_2, x_21);
x_37 = 46;
x_38 = lean_uint32_dec_eq(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_21);
x_39 = l_Lean_ParseImports_State_pushModule(x_23, x_1, x_20);
x_40 = l_Lean_ParseImports_whitespace(x_2, x_39);
return x_40;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_string_utf8_next(x_2, x_21);
x_42 = lean_string_utf8_at_end(x_2, x_41);
if (x_42 == 0)
{
uint32_t x_43; uint8_t x_44; 
x_43 = lean_string_utf8_get_fast(x_2, x_41);
lean_dec(x_41);
x_44 = l_Lean_isIdFirst(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = lean_uint32_dec_eq(x_43, x_15);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_21);
x_46 = l_Lean_ParseImports_State_pushModule(x_23, x_1, x_20);
x_47 = l_Lean_ParseImports_whitespace(x_2, x_46);
return x_47;
}
else
{
lean_object* x_48; 
x_48 = lean_box(0);
x_24 = x_48;
goto block_35;
}
}
else
{
lean_object* x_49; 
x_49 = lean_box(0);
x_24 = x_49;
goto block_35;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_41);
lean_dec(x_21);
x_50 = l_Lean_ParseImports_State_pushModule(x_23, x_1, x_20);
x_51 = l_Lean_ParseImports_whitespace(x_2, x_50);
return x_51;
}
}
block_35:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_24);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
x_26 = lean_string_utf8_next(x_2, x_21);
lean_dec(x_21);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_20, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_20, 0);
lean_dec(x_29);
lean_ctor_set(x_20, 1, x_26);
x_3 = x_23;
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 2);
x_32 = lean_ctor_get_uint8(x_20, sizeof(void*)*3);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_32);
x_3 = x_23;
x_4 = x_33;
goto _start;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_string_utf8_next_fast(x_2, x_6);
lean_dec(x_6);
lean_inc(x_52);
lean_ctor_set(x_4, 1, x_52);
x_53 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2(x_2, x_4);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
x_57 = lean_ctor_get(x_53, 2);
x_58 = lean_ctor_get_uint8(x_53, sizeof(void*)*3);
x_59 = lean_string_utf8_at_end(x_2, x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint32_t x_63; uint32_t x_64; uint8_t x_65; 
x_60 = lean_string_utf8_next_fast(x_2, x_56);
lean_inc(x_57);
lean_inc(x_60);
lean_inc(x_55);
lean_ctor_set(x_53, 1, x_60);
x_61 = lean_string_utf8_extract(x_2, x_52, x_56);
lean_dec(x_56);
lean_dec(x_52);
x_62 = l_Lean_Name_str___override(x_3, x_61);
x_63 = lean_string_utf8_get(x_2, x_60);
x_64 = 46;
x_65 = lean_uint32_dec_eq(x_63, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_55);
x_66 = l_Lean_ParseImports_State_pushModule(x_62, x_1, x_53);
x_67 = l_Lean_ParseImports_whitespace(x_2, x_66);
return x_67;
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_string_utf8_next(x_2, x_60);
lean_dec(x_60);
x_69 = lean_string_utf8_at_end(x_2, x_68);
if (x_69 == 0)
{
uint32_t x_70; uint8_t x_71; 
x_70 = lean_string_utf8_get_fast(x_2, x_68);
x_71 = l_Lean_isIdFirst(x_70);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = lean_uint32_dec_eq(x_70, x_15);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_68);
lean_dec(x_57);
lean_dec(x_55);
x_73 = l_Lean_ParseImports_State_pushModule(x_62, x_1, x_53);
x_74 = l_Lean_ParseImports_whitespace(x_2, x_73);
return x_74;
}
else
{
lean_object* x_75; 
lean_dec(x_53);
x_75 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_75, 0, x_55);
lean_ctor_set(x_75, 1, x_68);
lean_ctor_set(x_75, 2, x_57);
lean_ctor_set_uint8(x_75, sizeof(void*)*3, x_58);
x_3 = x_62;
x_4 = x_75;
goto _start;
}
}
else
{
lean_object* x_77; 
lean_dec(x_53);
x_77 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_77, 0, x_55);
lean_ctor_set(x_77, 1, x_68);
lean_ctor_set(x_77, 2, x_57);
lean_ctor_set_uint8(x_77, sizeof(void*)*3, x_58);
x_3 = x_62;
x_4 = x_77;
goto _start;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_68);
lean_dec(x_57);
lean_dec(x_55);
x_79 = l_Lean_ParseImports_State_pushModule(x_62, x_1, x_53);
x_80 = l_Lean_ParseImports_whitespace(x_2, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; 
lean_dec(x_57);
lean_dec(x_52);
lean_dec(x_3);
x_81 = l_Lean_ParseImports_moduleIdent_parse___closed__4;
lean_ctor_set(x_53, 2, x_81);
return x_53;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_53, 0);
x_83 = lean_ctor_get(x_53, 1);
x_84 = lean_ctor_get(x_53, 2);
x_85 = lean_ctor_get_uint8(x_53, sizeof(void*)*3);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_53);
x_86 = lean_string_utf8_at_end(x_2, x_83);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint32_t x_91; uint32_t x_92; uint8_t x_93; 
x_87 = lean_string_utf8_next_fast(x_2, x_83);
lean_inc(x_84);
lean_inc(x_87);
lean_inc(x_82);
x_88 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_84);
lean_ctor_set_uint8(x_88, sizeof(void*)*3, x_85);
x_89 = lean_string_utf8_extract(x_2, x_52, x_83);
lean_dec(x_83);
lean_dec(x_52);
x_90 = l_Lean_Name_str___override(x_3, x_89);
x_91 = lean_string_utf8_get(x_2, x_87);
x_92 = 46;
x_93 = lean_uint32_dec_eq(x_91, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_87);
lean_dec(x_84);
lean_dec(x_82);
x_94 = l_Lean_ParseImports_State_pushModule(x_90, x_1, x_88);
x_95 = l_Lean_ParseImports_whitespace(x_2, x_94);
return x_95;
}
else
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_string_utf8_next(x_2, x_87);
lean_dec(x_87);
x_97 = lean_string_utf8_at_end(x_2, x_96);
if (x_97 == 0)
{
uint32_t x_98; uint8_t x_99; 
x_98 = lean_string_utf8_get_fast(x_2, x_96);
x_99 = l_Lean_isIdFirst(x_98);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = lean_uint32_dec_eq(x_98, x_15);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_96);
lean_dec(x_84);
lean_dec(x_82);
x_101 = l_Lean_ParseImports_State_pushModule(x_90, x_1, x_88);
x_102 = l_Lean_ParseImports_whitespace(x_2, x_101);
return x_102;
}
else
{
lean_object* x_103; 
lean_dec(x_88);
x_103 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_103, 0, x_82);
lean_ctor_set(x_103, 1, x_96);
lean_ctor_set(x_103, 2, x_84);
lean_ctor_set_uint8(x_103, sizeof(void*)*3, x_85);
x_3 = x_90;
x_4 = x_103;
goto _start;
}
}
else
{
lean_object* x_105; 
lean_dec(x_88);
x_105 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_105, 0, x_82);
lean_ctor_set(x_105, 1, x_96);
lean_ctor_set(x_105, 2, x_84);
lean_ctor_set_uint8(x_105, sizeof(void*)*3, x_85);
x_3 = x_90;
x_4 = x_105;
goto _start;
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_96);
lean_dec(x_84);
lean_dec(x_82);
x_107 = l_Lean_ParseImports_State_pushModule(x_90, x_1, x_88);
x_108 = l_Lean_ParseImports_whitespace(x_2, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_84);
lean_dec(x_52);
lean_dec(x_3);
x_109 = l_Lean_ParseImports_moduleIdent_parse___closed__4;
x_110 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_110, 0, x_82);
lean_ctor_set(x_110, 1, x_83);
lean_ctor_set(x_110, 2, x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*3, x_85);
return x_110;
}
}
}
}
else
{
uint32_t x_111; uint32_t x_112; uint8_t x_113; 
lean_dec(x_4);
x_111 = lean_string_utf8_get_fast(x_2, x_6);
x_112 = l_Lean_idBeginEscape;
x_113 = lean_uint32_dec_eq(x_111, x_112);
if (x_113 == 0)
{
uint8_t x_114; 
x_114 = l_Lean_isIdFirst(x_111);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_7);
lean_dec(x_3);
x_115 = l_Lean_ParseImports_moduleIdent_parse___closed__2;
x_116 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_116, 0, x_5);
lean_ctor_set(x_116, 1, x_6);
lean_ctor_set(x_116, 2, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*3, x_8);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint32_t x_132; uint32_t x_133; uint8_t x_134; 
x_117 = lean_string_utf8_next_fast(x_2, x_6);
x_118 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_118, 0, x_5);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_118, 2, x_7);
lean_ctor_set_uint8(x_118, sizeof(void*)*3, x_8);
x_119 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1(x_2, x_118);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
x_121 = lean_string_utf8_extract(x_2, x_6, x_120);
lean_dec(x_6);
x_122 = l_Lean_Name_str___override(x_3, x_121);
x_132 = lean_string_utf8_get(x_2, x_120);
x_133 = 46;
x_134 = lean_uint32_dec_eq(x_132, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_120);
x_135 = l_Lean_ParseImports_State_pushModule(x_122, x_1, x_119);
x_136 = l_Lean_ParseImports_whitespace(x_2, x_135);
return x_136;
}
else
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_string_utf8_next(x_2, x_120);
x_138 = lean_string_utf8_at_end(x_2, x_137);
if (x_138 == 0)
{
uint32_t x_139; uint8_t x_140; 
x_139 = lean_string_utf8_get_fast(x_2, x_137);
lean_dec(x_137);
x_140 = l_Lean_isIdFirst(x_139);
if (x_140 == 0)
{
uint8_t x_141; 
x_141 = lean_uint32_dec_eq(x_139, x_112);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_120);
x_142 = l_Lean_ParseImports_State_pushModule(x_122, x_1, x_119);
x_143 = l_Lean_ParseImports_whitespace(x_2, x_142);
return x_143;
}
else
{
lean_object* x_144; 
x_144 = lean_box(0);
x_123 = x_144;
goto block_131;
}
}
else
{
lean_object* x_145; 
x_145 = lean_box(0);
x_123 = x_145;
goto block_131;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_137);
lean_dec(x_120);
x_146 = l_Lean_ParseImports_State_pushModule(x_122, x_1, x_119);
x_147 = l_Lean_ParseImports_whitespace(x_2, x_146);
return x_147;
}
}
block_131:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_123);
x_124 = lean_ctor_get(x_119, 0);
lean_inc(x_124);
x_125 = lean_string_utf8_next(x_2, x_120);
lean_dec(x_120);
x_126 = lean_ctor_get(x_119, 2);
lean_inc(x_126);
x_127 = lean_ctor_get_uint8(x_119, sizeof(void*)*3);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 x_128 = x_119;
} else {
 lean_dec_ref(x_119);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 3, 1);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_124);
lean_ctor_set(x_129, 1, x_125);
lean_ctor_set(x_129, 2, x_126);
lean_ctor_set_uint8(x_129, sizeof(void*)*3, x_127);
x_3 = x_122;
x_4 = x_129;
goto _start;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; uint8_t x_156; 
x_148 = lean_string_utf8_next_fast(x_2, x_6);
lean_dec(x_6);
lean_inc(x_148);
x_149 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_149, 0, x_5);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set(x_149, 2, x_7);
lean_ctor_set_uint8(x_149, sizeof(void*)*3, x_8);
x_150 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2(x_2, x_149);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 2);
lean_inc(x_153);
x_154 = lean_ctor_get_uint8(x_150, sizeof(void*)*3);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 lean_ctor_release(x_150, 2);
 x_155 = x_150;
} else {
 lean_dec_ref(x_150);
 x_155 = lean_box(0);
}
x_156 = lean_string_utf8_at_end(x_2, x_152);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint32_t x_161; uint32_t x_162; uint8_t x_163; 
x_157 = lean_string_utf8_next_fast(x_2, x_152);
lean_inc(x_153);
lean_inc(x_157);
lean_inc(x_151);
if (lean_is_scalar(x_155)) {
 x_158 = lean_alloc_ctor(0, 3, 1);
} else {
 x_158 = x_155;
}
lean_ctor_set(x_158, 0, x_151);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_158, 2, x_153);
lean_ctor_set_uint8(x_158, sizeof(void*)*3, x_154);
x_159 = lean_string_utf8_extract(x_2, x_148, x_152);
lean_dec(x_152);
lean_dec(x_148);
x_160 = l_Lean_Name_str___override(x_3, x_159);
x_161 = lean_string_utf8_get(x_2, x_157);
x_162 = 46;
x_163 = lean_uint32_dec_eq(x_161, x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_157);
lean_dec(x_153);
lean_dec(x_151);
x_164 = l_Lean_ParseImports_State_pushModule(x_160, x_1, x_158);
x_165 = l_Lean_ParseImports_whitespace(x_2, x_164);
return x_165;
}
else
{
lean_object* x_166; uint8_t x_167; 
x_166 = lean_string_utf8_next(x_2, x_157);
lean_dec(x_157);
x_167 = lean_string_utf8_at_end(x_2, x_166);
if (x_167 == 0)
{
uint32_t x_168; uint8_t x_169; 
x_168 = lean_string_utf8_get_fast(x_2, x_166);
x_169 = l_Lean_isIdFirst(x_168);
if (x_169 == 0)
{
uint8_t x_170; 
x_170 = lean_uint32_dec_eq(x_168, x_112);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_166);
lean_dec(x_153);
lean_dec(x_151);
x_171 = l_Lean_ParseImports_State_pushModule(x_160, x_1, x_158);
x_172 = l_Lean_ParseImports_whitespace(x_2, x_171);
return x_172;
}
else
{
lean_object* x_173; 
lean_dec(x_158);
x_173 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_173, 0, x_151);
lean_ctor_set(x_173, 1, x_166);
lean_ctor_set(x_173, 2, x_153);
lean_ctor_set_uint8(x_173, sizeof(void*)*3, x_154);
x_3 = x_160;
x_4 = x_173;
goto _start;
}
}
else
{
lean_object* x_175; 
lean_dec(x_158);
x_175 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_175, 0, x_151);
lean_ctor_set(x_175, 1, x_166);
lean_ctor_set(x_175, 2, x_153);
lean_ctor_set_uint8(x_175, sizeof(void*)*3, x_154);
x_3 = x_160;
x_4 = x_175;
goto _start;
}
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_166);
lean_dec(x_153);
lean_dec(x_151);
x_177 = l_Lean_ParseImports_State_pushModule(x_160, x_1, x_158);
x_178 = l_Lean_ParseImports_whitespace(x_2, x_177);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_153);
lean_dec(x_148);
lean_dec(x_3);
x_179 = l_Lean_ParseImports_moduleIdent_parse___closed__4;
if (lean_is_scalar(x_155)) {
 x_180 = lean_alloc_ctor(0, 3, 1);
} else {
 x_180 = x_155;
}
lean_ctor_set(x_180, 0, x_151);
lean_ctor_set(x_180, 1, x_152);
lean_ctor_set(x_180, 2, x_179);
lean_ctor_set_uint8(x_180, sizeof(void*)*3, x_154);
return x_180;
}
}
}
}
else
{
lean_object* x_181; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_181 = l_Lean_ParseImports_State_mkEOIError(x_4);
return x_181;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ParseImports_takeUntil___at_Lean_ParseImports_moduleIdent_parse___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent_parse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_ParseImports_moduleIdent_parse(x_5, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_ParseImports_moduleIdent_parse(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_moduleIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_ParseImports_moduleIdent(x_4, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_many(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_array_get_size(x_4);
lean_dec(x_4);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_apply_2(x_1, x_2, x_3);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_free_object(x_3);
lean_dec(x_6);
lean_dec(x_5);
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = l_Array_shrink___rarg(x_14, x_6);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = 0;
lean_ctor_set(x_3, 2, x_16);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_17);
return x_3;
}
}
else
{
lean_object* x_18; 
lean_dec(x_3);
x_18 = lean_ctor_get(x_7, 2);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec(x_7);
x_21 = l_Array_shrink___rarg(x_20, x_6);
lean_dec(x_6);
x_22 = lean_box(0);
x_23 = 0;
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_5);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_1, x_4);
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__2;
x_12 = 0;
x_13 = l_Lean_ParseImports_State_pushModule(x_11, x_12, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_15 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_14;
x_5 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
x_17 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__2;
x_18 = 0;
x_19 = l_Lean_ParseImports_State_pushModule(x_17, x_18, x_3);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
lean_ctor_set(x_3, 1, x_5);
x_22 = l_Lean_ParseImports_whitespace(x_2, x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_26 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_5);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_25);
x_27 = l_Lean_ParseImports_whitespace(x_2, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_preludeOpt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_preludeOpt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_preludeOpt(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_privateOpt___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_1, x_4);
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 1;
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_16 = 1;
x_17 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_19 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
else
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = 1;
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_22);
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_3, 1);
lean_dec(x_29);
lean_ctor_set(x_3, 1, x_5);
x_30 = l_Lean_ParseImports_whitespace(x_2, x_3);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = 0;
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_32);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 1);
x_35 = lean_ctor_get(x_30, 2);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_30);
x_36 = 0;
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_ctor_get(x_3, 2);
x_40 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_3);
x_41 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_5);
lean_ctor_set(x_41, 2, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_40);
x_42 = l_Lean_ParseImports_whitespace(x_2, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 2);
lean_inc(x_45);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 x_46 = x_42;
} else {
 lean_dec_ref(x_42);
 x_46 = lean_box(0);
}
x_47 = 0;
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 3, 1);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_45);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_privateOpt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_privateOpt___spec__1(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_privateOpt___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_privateOpt___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_privateOpt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_privateOpt(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("import", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1;
x_2 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__2;
x_2 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_1, x_4);
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 2);
lean_dec(x_12);
x_13 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4;
lean_ctor_set(x_3, 2, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_17 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4;
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_20 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_19;
x_5 = x_20;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_3, 2);
lean_dec(x_23);
x_24 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4;
lean_ctor_set(x_3, 2, x_24);
return x_3;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_28 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4;
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_3, 1);
lean_dec(x_31);
lean_ctor_set(x_3, 1, x_5);
x_32 = l_Lean_ParseImports_whitespace(x_2, x_3);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_3, 0);
x_34 = lean_ctor_get(x_3, 2);
x_35 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_3);
x_36 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_5);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_35);
x_37 = l_Lean_ParseImports_whitespace(x_2, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_string_utf8_at_end(x_1, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_string_utf8_at_end(x_2, x_5);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_1, x_4);
x_9 = lean_string_utf8_get_fast(x_2, x_5);
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l_Lean_ParseImports_moduleIdent_parse(x_11, x_2, x_12, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_string_utf8_next_fast(x_1, x_4);
lean_dec(x_4);
x_15 = lean_string_utf8_next_fast(x_2, x_5);
lean_dec(x_5);
x_4 = x_14;
x_5 = x_15;
goto _start;
}
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
x_17 = 0;
x_18 = lean_box(0);
x_19 = l_Lean_ParseImports_moduleIdent_parse(x_17, x_2, x_18, x_3);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_3, 1);
lean_dec(x_21);
lean_ctor_set(x_3, 1, x_5);
x_22 = l_Lean_ParseImports_whitespace(x_2, x_3);
x_23 = 1;
x_24 = lean_box(0);
x_25 = l_Lean_ParseImports_moduleIdent_parse(x_23, x_2, x_24, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 2);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_3);
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_5);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_28);
x_30 = l_Lean_ParseImports_whitespace(x_2, x_29);
x_31 = 1;
x_32 = lean_box(0);
x_33 = l_Lean_ParseImports_moduleIdent_parse(x_31, x_2, x_32, x_30);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("private", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("runtime", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_array_get_size(x_4);
lean_dec(x_4);
x_7 = l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1;
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_3);
x_8 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_privateOpt___spec__1(x_7, x_2, x_3, x_1, x_5);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
x_15 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1;
lean_inc(x_1);
x_16 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1(x_15, x_2, x_8, x_1, x_14);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__2;
lean_inc(x_1);
x_20 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2(x_19, x_2, x_16, x_1, x_18);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_free_object(x_3);
lean_dec(x_6);
lean_dec(x_5);
x_3 = x_20;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_21);
lean_dec(x_1);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Array_shrink___rarg(x_23, x_6);
lean_dec(x_6);
x_25 = lean_box(0);
x_26 = 0;
lean_ctor_set(x_3, 2, x_25);
lean_ctor_set(x_3, 0, x_24);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_26);
return x_3;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_1);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = l_Array_shrink___rarg(x_27, x_6);
lean_dec(x_6);
x_29 = lean_box(0);
x_30 = 0;
lean_ctor_set(x_3, 2, x_29);
lean_ctor_set(x_3, 0, x_28);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_30);
return x_3;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_13);
lean_dec(x_1);
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
lean_dec(x_8);
x_32 = l_Array_shrink___rarg(x_31, x_6);
lean_dec(x_6);
x_33 = lean_box(0);
x_34 = 0;
lean_ctor_set(x_3, 2, x_33);
lean_ctor_set(x_3, 0, x_32);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_34);
return x_3;
}
}
else
{
lean_object* x_35; 
lean_dec(x_3);
x_35 = lean_ctor_get(x_8, 2);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
x_37 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1;
lean_inc(x_1);
x_38 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1(x_37, x_2, x_8, x_1, x_36);
x_39 = lean_ctor_get(x_38, 2);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
x_41 = l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__2;
lean_inc(x_1);
x_42 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2(x_41, x_2, x_38, x_1, x_40);
x_43 = lean_ctor_get(x_42, 2);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
x_3 = x_42;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
lean_dec(x_43);
lean_dec(x_1);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l_Array_shrink___rarg(x_45, x_6);
lean_dec(x_6);
x_47 = lean_box(0);
x_48 = 0;
x_49 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_5);
lean_ctor_set(x_49, 2, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
lean_dec(x_39);
lean_dec(x_1);
x_50 = lean_ctor_get(x_38, 0);
lean_inc(x_50);
lean_dec(x_38);
x_51 = l_Array_shrink___rarg(x_50, x_6);
lean_dec(x_6);
x_52 = lean_box(0);
x_53 = 0;
x_54 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_5);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
lean_dec(x_35);
lean_dec(x_1);
x_55 = lean_ctor_get(x_8, 0);
lean_inc(x_55);
lean_dec(x_8);
x_56 = l_Array_shrink___rarg(x_55, x_6);
lean_dec(x_6);
x_57 = lean_box(0);
x_58 = 0;
x_59 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_5);
lean_ctor_set(x_59, 2, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*3, x_58);
return x_59;
}
}
}
}
static lean_object* _init_l_Lean_ParseImports_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("prelude", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_ParseImports_main___closed__1;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1(x_4, x_1, x_2, x_5, x_3);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3(x_5, x_1, x_6);
lean_dec(x_1);
return x_8;
}
else
{
lean_dec(x_7);
lean_dec(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_parseImports_x27___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_parseImports_x27___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_ParseImports_instInhabitedState___closed__1;
x_5 = l_Lean_ParseImports_whitespace(x_1, x_4);
x_6 = l_Lean_ParseImports_main(x_1, x_5);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_parseImports_x27___closed__1;
x_12 = lean_string_append(x_11, x_2);
x_13 = l_Lean_parseImports_x27___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_14, x_10);
lean_dec(x_10);
x_16 = lean_string_append(x_15, x_11);
x_17 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_parseImports_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_parseImports_x27(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1693____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("module", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1693____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("runtimeOnly", 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1693_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = 1;
x_4 = l_Lean_Name_toString(x_2, x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1693____closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_11 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_11, 0, x_10);
x_12 = l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_16, 0, x_15);
x_17 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1693____closed__2;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_List_join___rarg(x_22);
x_24 = l_Lean_Json_mkObj(x_23);
return x_24;
}
}
static lean_object* _init_l_Lean_instToJsonImport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1693_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToJsonImport() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToJsonImport___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_PrintImportResult_imports_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrintImportResult_errors___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ParseImports_State_imports___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1693_(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____spec__2(x_6, x_7, x_4);
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("imports", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("errors", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____closed__1;
x_4 = l_Lean_Json_opt___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____spec__1(x_3, x_2);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____spec__3(x_7, x_8, x_5);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____closed__2;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_List_join___rarg(x_16);
x_18 = l_Lean_Json_mkObj(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____spec__3(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_instToJsonPrintImportResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToJsonPrintImportResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToJsonPrintImportResult___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1878____spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797_(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1878_(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1878____spec__1(x_3, x_4, x_1);
x_6 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_List_join___rarg(x_11);
x_13 = l_Lean_Json_mkObj(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1878____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1878____spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_instToJsonPrintImportsResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1878_), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instToJsonPrintImportsResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instToJsonPrintImportsResult___closed__1;
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_2, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_uget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_10 = l_IO_FS_readFile(x_7, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_parseImports_x27(x_11, x_7, x_12);
lean_dec(x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = l_Lean_ParseImports_State_imports___default___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_9, x_2, x_18);
x_2 = x_20;
x_3 = x_21;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_box(0);
x_26 = lean_io_error_to_string(x_23);
x_27 = l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1;
x_28 = lean_array_push(x_27, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = 1;
x_31 = lean_usize_add(x_2, x_30);
x_32 = lean_array_uset(x_9, x_2, x_29);
x_2 = x_31;
x_3 = x_32;
x_4 = x_24;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
lean_dec(x_7);
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_box(0);
x_37 = lean_io_error_to_string(x_34);
x_38 = l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1;
x_39 = lean_array_push(x_38, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = 1;
x_42 = lean_usize_add(x_2, x_41);
x_43 = lean_array_uset(x_9, x_2, x_40);
x_2 = x_42;
x_3 = x_43;
x_4 = x_35;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lean_print_imports_json(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1(x_4, x_5, x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportsResult____x40_Lean_Elab_ParseImportsFast___hyg_1878_(x_7);
x_10 = l_Lean_Json_compress(x_9);
x_11 = l_IO_println___at_Lean_instEval___spec__1(x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1(x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ParseImportsFast(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_ParseImports_State_imports___default___closed__1 = _init_l_Lean_ParseImports_State_imports___default___closed__1();
lean_mark_persistent(l_Lean_ParseImports_State_imports___default___closed__1);
l_Lean_ParseImports_State_imports___default = _init_l_Lean_ParseImports_State_imports___default();
lean_mark_persistent(l_Lean_ParseImports_State_imports___default);
l_Lean_ParseImports_State_pos___default = _init_l_Lean_ParseImports_State_pos___default();
lean_mark_persistent(l_Lean_ParseImports_State_pos___default);
l_Lean_ParseImports_State_error_x3f___default = _init_l_Lean_ParseImports_State_error_x3f___default();
lean_mark_persistent(l_Lean_ParseImports_State_error_x3f___default);
l_Lean_ParseImports_State_nextPriv___default = _init_l_Lean_ParseImports_State_nextPriv___default();
l_Lean_ParseImports_instInhabitedState___closed__1 = _init_l_Lean_ParseImports_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_ParseImports_instInhabitedState___closed__1);
l_Lean_ParseImports_instInhabitedState = _init_l_Lean_ParseImports_instInhabitedState();
lean_mark_persistent(l_Lean_ParseImports_instInhabitedState);
l_Lean_ParseImports_State_mkEOIError___closed__1 = _init_l_Lean_ParseImports_State_mkEOIError___closed__1();
lean_mark_persistent(l_Lean_ParseImports_State_mkEOIError___closed__1);
l_Lean_ParseImports_State_mkEOIError___closed__2 = _init_l_Lean_ParseImports_State_mkEOIError___closed__2();
lean_mark_persistent(l_Lean_ParseImports_State_mkEOIError___closed__2);
l_Lean_ParseImports_finishCommentBlock_eoi___closed__1 = _init_l_Lean_ParseImports_finishCommentBlock_eoi___closed__1();
lean_mark_persistent(l_Lean_ParseImports_finishCommentBlock_eoi___closed__1);
l_Lean_ParseImports_finishCommentBlock_eoi___closed__2 = _init_l_Lean_ParseImports_finishCommentBlock_eoi___closed__2();
lean_mark_persistent(l_Lean_ParseImports_finishCommentBlock_eoi___closed__2);
l_Lean_ParseImports_whitespace___closed__1 = _init_l_Lean_ParseImports_whitespace___closed__1();
lean_mark_persistent(l_Lean_ParseImports_whitespace___closed__1);
l_Lean_ParseImports_whitespace___closed__2 = _init_l_Lean_ParseImports_whitespace___closed__2();
lean_mark_persistent(l_Lean_ParseImports_whitespace___closed__2);
l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1 = _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1();
lean_mark_persistent(l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__1);
l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2 = _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2();
lean_mark_persistent(l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_keyword___spec__1___closed__2);
l_Lean_ParseImports_moduleIdent_parse___closed__1 = _init_l_Lean_ParseImports_moduleIdent_parse___closed__1();
lean_mark_persistent(l_Lean_ParseImports_moduleIdent_parse___closed__1);
l_Lean_ParseImports_moduleIdent_parse___closed__2 = _init_l_Lean_ParseImports_moduleIdent_parse___closed__2();
lean_mark_persistent(l_Lean_ParseImports_moduleIdent_parse___closed__2);
l_Lean_ParseImports_moduleIdent_parse___closed__3 = _init_l_Lean_ParseImports_moduleIdent_parse___closed__3();
lean_mark_persistent(l_Lean_ParseImports_moduleIdent_parse___closed__3);
l_Lean_ParseImports_moduleIdent_parse___closed__4 = _init_l_Lean_ParseImports_moduleIdent_parse___closed__4();
lean_mark_persistent(l_Lean_ParseImports_moduleIdent_parse___closed__4);
l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__1 = _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__1();
lean_mark_persistent(l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__1);
l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__2 = _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__2();
lean_mark_persistent(l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_preludeOpt___spec__1___closed__2);
l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1 = _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1();
lean_mark_persistent(l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__1);
l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__2 = _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__2();
lean_mark_persistent(l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__2);
l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__3 = _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__3();
lean_mark_persistent(l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__3);
l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4 = _init_l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4();
lean_mark_persistent(l_Lean_ParseImports_keywordCore_go___at_Lean_ParseImports_main___spec__1___closed__4);
l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1 = _init_l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1();
lean_mark_persistent(l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__1);
l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__2 = _init_l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__2();
lean_mark_persistent(l_Lean_ParseImports_many___at_Lean_ParseImports_main___spec__3___closed__2);
l_Lean_ParseImports_main___closed__1 = _init_l_Lean_ParseImports_main___closed__1();
lean_mark_persistent(l_Lean_ParseImports_main___closed__1);
l_Lean_parseImports_x27___closed__1 = _init_l_Lean_parseImports_x27___closed__1();
lean_mark_persistent(l_Lean_parseImports_x27___closed__1);
l_Lean_parseImports_x27___closed__2 = _init_l_Lean_parseImports_x27___closed__2();
lean_mark_persistent(l_Lean_parseImports_x27___closed__2);
l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1693____closed__1 = _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1693____closed__1();
lean_mark_persistent(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1693____closed__1);
l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1693____closed__2 = _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1693____closed__2();
lean_mark_persistent(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonImport____x40_Lean_Elab_ParseImportsFast___hyg_1693____closed__2);
l_Lean_instToJsonImport___closed__1 = _init_l_Lean_instToJsonImport___closed__1();
lean_mark_persistent(l_Lean_instToJsonImport___closed__1);
l_Lean_instToJsonImport = _init_l_Lean_instToJsonImport();
lean_mark_persistent(l_Lean_instToJsonImport);
l_Lean_PrintImportResult_imports_x3f___default = _init_l_Lean_PrintImportResult_imports_x3f___default();
lean_mark_persistent(l_Lean_PrintImportResult_imports_x3f___default);
l_Lean_PrintImportResult_errors___default = _init_l_Lean_PrintImportResult_errors___default();
lean_mark_persistent(l_Lean_PrintImportResult_errors___default);
l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____closed__1 = _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____closed__1();
lean_mark_persistent(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____closed__1);
l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____closed__2 = _init_l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____closed__2();
lean_mark_persistent(l___private_Lean_Elab_ParseImportsFast_0__Lean_toJsonPrintImportResult____x40_Lean_Elab_ParseImportsFast___hyg_1797____closed__2);
l_Lean_instToJsonPrintImportResult___closed__1 = _init_l_Lean_instToJsonPrintImportResult___closed__1();
lean_mark_persistent(l_Lean_instToJsonPrintImportResult___closed__1);
l_Lean_instToJsonPrintImportResult = _init_l_Lean_instToJsonPrintImportResult();
lean_mark_persistent(l_Lean_instToJsonPrintImportResult);
l_Lean_instToJsonPrintImportsResult___closed__1 = _init_l_Lean_instToJsonPrintImportsResult___closed__1();
lean_mark_persistent(l_Lean_instToJsonPrintImportsResult___closed__1);
l_Lean_instToJsonPrintImportsResult = _init_l_Lean_instToJsonPrintImportsResult();
lean_mark_persistent(l_Lean_instToJsonPrintImportsResult);
l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_printImportsJson___spec__1___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
