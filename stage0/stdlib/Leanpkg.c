// Lean compiler output
// Module: Leanpkg
// Imports: Init Leanpkg.Resolve Leanpkg.Git
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
lean_object* lean_string_push(lean_object*, uint32_t);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Leanpkg_withLockFile_acquire___lambda__2(lean_object*, lean_object*);
lean_object* l_Leanpkg_init(lean_object*, lean_object*);
lean_object* l_Leanpkg_initPkg(lean_object*, uint8_t, lean_object*);
lean_object* l_Leanpkg_writeManifest(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___at_Leanpkg_buildImports___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_execMake___lambda__1___closed__4;
lean_object* l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__3;
extern lean_object* l_String_instInhabitedString;
extern lean_object* l_Leanpkg_gitParseRevision___closed__5;
extern uint8_t l_System_Platform_isWindows;
lean_object* l_List_map___at_Leanpkg_configure___spec__2___closed__1;
lean_object* l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Leanpkg_main___closed__3;
lean_object* l_IO_FS_writeFile___at_Leanpkg_writeManifest___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_execMake___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_execMake___lambda__1___closed__1;
lean_object* lean_io_is_dir(lean_object*, lean_object*);
lean_object* _lean_main(lean_object*, lean_object*);
lean_object* l_Leanpkg_readManifest(lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_configure(lean_object*);
lean_object* l_Leanpkg_buildImports(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Leanpkg_withLockFile_acquire___closed__1;
lean_object* l_List_map___at_Leanpkg_configure___spec__2(lean_object*);
lean_object* l_Leanpkg_execCmd(lean_object*, lean_object*);
lean_object* l_Leanpkg_withLockFile_acquire___closed__8;
extern lean_object* l_String_quote___closed__2;
lean_object* l_Leanpkg_initPkg___closed__12;
lean_object* l_Leanpkg_withLockFile_acquire___boxed(lean_object*, lean_object*);
lean_object* l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore_match__1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Leanpkg_readManifest___closed__3;
lean_object* l_Leanpkg_execMake___closed__1;
lean_object* l_Leanpkg_withLockFile_acquire_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_sleep(uint32_t, lean_object*);
lean_object* l_Leanpkg_initPkg___closed__11;
lean_object* l_Leanpkg_usage;
extern lean_object* l_Leanpkg_gitParseRevision___closed__1;
lean_object* l_Leanpkg_main___closed__2;
lean_object* l_Leanpkg_withLockFile_acquire(uint8_t, lean_object*);
lean_object* l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_execMake___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_initPkg___closed__8;
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_List_map___at_Leanpkg_buildImports___spec__1(lean_object*);
lean_object* l_Leanpkg_build(lean_object*, lean_object*);
lean_object* l_Leanpkg_initPkg___closed__1;
lean_object* l_Leanpkg_initPkg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_buildImports___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_usage___closed__3;
lean_object* l_IO_FS_Handle_putStr___at_Leanpkg_initPkg___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_initPkg___closed__9;
lean_object* l_String_toName(lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
lean_object* l_Leanpkg_initPkg___closed__4;
lean_object* l_IO_removeFile___at_Leanpkg_withLockFile___spec__1(lean_object*, lean_object*);
lean_object* l_Leanpkg_readManifest___closed__4;
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_mk___at_Lean_Parser_testParseFile___spec__2(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Leanpkg_initPkg___closed__2;
lean_object* l_Leanpkg_withLockFile_acquire___closed__4;
lean_object* l_Leanpkg_execMake___lambda__1___closed__6;
lean_object* l_Leanpkg_buildImports___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_mapAux___at_String_toLower___spec__1(lean_object*, lean_object*);
lean_object* l_Leanpkg_withLockFile_acquire___closed__6;
lean_object* l_String_capitalize(lean_object*);
lean_object* l_Leanpkg_readManifest___closed__1;
lean_object* l_Leanpkg_buildImports___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Leanpkg_uiLeanVersionString;
lean_object* l_IO_Prim_fopenFlags(uint8_t, uint8_t);
lean_object* l_Leanpkg_solveDeps(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Leanpkg_initPkg___closed__6;
lean_object* l_Leanpkg_withLockFile_acquire___closed__5;
lean_object* l_Leanpkg_initGitignoreContents;
lean_object* l_Leanpkg_withLockFile_acquire___closed__3;
extern lean_object* l_Leanpkg_leanpkgTomlFn;
lean_object* l_Leanpkg_withLockFile_acquire___closed__2;
lean_object* l_Leanpkg_withLockFile_acquire___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l_Leanpkg_execMake___lambda__1___closed__2;
lean_object* l_Leanpkg_main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_readManifest___closed__2;
lean_object* l_Leanpkg_withLockFile_acquire___lambda__1(lean_object*, lean_object*);
extern lean_object* l_Leanpkg_leanVersionString___closed__3;
lean_object* l_IO_FS_writeFile___at_Leanpkg_initPkg___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putStr___at_Leanpkg_writeManifest___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore(lean_object*);
lean_object* l_IO_appDir___at_Lean_getBuiltinSearchPath___spec__1(lean_object*);
lean_object* l_Leanpkg_execMake___lambda__1___closed__3;
lean_object* l_Leanpkg_withLockFile___rarg(lean_object*, lean_object*);
lean_object* l_Leanpkg_initPkg___closed__13;
extern lean_object* l_IO_Prim_fopenFlags___closed__6;
lean_object* l_Leanpkg_Manifest_fromFile(lean_object*, lean_object*);
lean_object* l_Leanpkg_withLockFile_acquire___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore_match__2(lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Compiler_InitAttr___hyg_535____closed__1;
extern lean_object* l_Leanpkg_materialize___lambda__1___closed__2;
lean_object* l_Leanpkg_configure_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Leanpkg_withLockFile(lean_object*);
lean_object* lean_init_search_path(lean_object*, lean_object*);
lean_object* l_Leanpkg_configure_match__1___rarg(lean_object*);
lean_object* l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore___closed__1;
lean_object* l_main_match__1(lean_object*);
lean_object* l_Leanpkg_splitCmdlineArgs_match__1(lean_object*);
lean_object* l_Leanpkg_constructPath(lean_object*, lean_object*);
lean_object* l_Leanpkg_execMake___lambda__1___closed__7;
lean_object* l_List_map___at_Leanpkg_buildImports___spec__3(lean_object*);
lean_object* l_Leanpkg_splitCmdlineArgs_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putStr___at_Leanpkg_writeManifest___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_file_exists(lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__4;
extern lean_object* l_Lean_Syntax_mkApp___closed__1;
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_IO_removeFile___at_Leanpkg_withLockFile___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_main_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_List_partition___rarg___closed__1;
lean_object* l_Leanpkg_usage___closed__4;
extern uint32_t l_System_FilePath_searchPathSeparator;
lean_object* l_Leanpkg_execMake___lambda__1___closed__5;
lean_object* l_Leanpkg_lockFileName___closed__1;
lean_object* l_Leanpkg_withLockFile_acquire___closed__7;
lean_object* l_Leanpkg_configure___closed__2;
lean_object* l_Leanpkg_splitCmdlineArgs(lean_object*, lean_object*);
lean_object* l_Leanpkg_buildImports___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_initGitignoreContents___closed__1;
lean_object* l_Leanpkg_writeManifest___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_initPkg___closed__5;
lean_object* l_Leanpkg_execMake(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_initPkg___closed__14;
lean_object* l_IO_FS_Handle_mk___at_Leanpkg_writeManifest___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_main_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_initPkg___closed__15;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Leanpkg_main_match__1(lean_object*);
extern lean_object* l_Leanpkg_leanVersionString;
lean_object* l_Leanpkg_lockFileName;
lean_object* l_Leanpkg_usage___closed__2;
lean_object* l_Leanpkg_initPkg___closed__7;
lean_object* l_Leanpkg_splitCmdlineArgs_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Leanpkg_configure___closed__1;
lean_object* l_Leanpkg_execMake_match__1(lean_object*);
lean_object* l_Leanpkg_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_main___closed__1;
lean_object* l_List_forIn_loop___at_Leanpkg_configure___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_execMake_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_initPkg___closed__3;
lean_object* l_List_map___at_Leanpkg_buildImports___spec__3___closed__2;
lean_object* lean_io_remove_file(lean_object*, lean_object*);
lean_object* l_Leanpkg_withLockFile_acquire_match__1(lean_object*);
lean_object* l_IO_FS_Handle_putStr___at_Leanpkg_initPkg___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_usage___closed__1;
lean_object* l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__1;
lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Leanpkg_configure___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__2;
uint8_t l_Leanpkg_initPkg___closed__10;
lean_object* l_Lean_modPathToFilePath(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* lean_io_app_dir(lean_object*);
lean_object* l_Leanpkg_Manifest_effectivePath(lean_object*);
extern lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_pushNewline___closed__1;
lean_object* l_Leanpkg_execMake___lambda__1___closed__8;
lean_object* l_Leanpkg_main_match__1___rarg___closed__2;
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Leanpkg_main_match__1___rarg___closed__1;
uint8_t l_List_beq___at_Lean_OpenDecl_instToStringOpenDecl___spec__1(lean_object*, lean_object*);
extern lean_object* l_Leanpkg_gitParseRevision___closed__9;
lean_object* l_IO_FS_writeFile___at_Leanpkg_writeManifest___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_configure_match__1(lean_object*, lean_object*);
lean_object* l_List_map___at_Leanpkg_buildImports___spec__3___closed__1;
lean_object* lean_io_prim_handle_mk(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Leanpkg_upstreamGitBranch;
lean_object* l_IO_FS_writeFile___at_Leanpkg_initPkg___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_splitCmdlineArgs_match__2(lean_object*);
lean_object* l_Leanpkg_main___closed__4;
lean_object* l_Leanpkg_main_match__1___rarg___closed__3;
lean_object* l_IO_FS_Handle_mk___at_Leanpkg_writeManifest___spec__2(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_reprint(lean_object*);
extern lean_object* l___private_Init_Data_Format_Basic_0__Std_Format_be___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* _init_l_Leanpkg_readManifest___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nWARNING: Lean version mismatch: installed version is ");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_readManifest___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_readManifest___closed__1;
x_2 = l_Leanpkg_leanVersionString;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_readManifest___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", but package requires ");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_readManifest___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_readManifest___closed__2;
x_2 = l_Leanpkg_readManifest___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_Leanpkg_readManifest(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Leanpkg_leanpkgTomlFn;
x_3 = l_Leanpkg_Manifest_fromFile(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_5, 2);
lean_inc(x_7);
x_8 = l_Leanpkg_leanVersionString;
x_9 = lean_string_dec_eq(x_7, x_8);
x_10 = l_instDecidableNot___rarg(x_9);
if (x_10 == 0)
{
lean_dec(x_7);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_3);
x_11 = l_Leanpkg_readManifest___closed__4;
x_12 = lean_string_append(x_11, x_7);
lean_dec(x_7);
x_13 = l___private_Init_Data_Format_Basic_0__Std_Format_pushNewline___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_14, x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_5);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
x_27 = l_Leanpkg_leanVersionString;
x_28 = lean_string_dec_eq(x_26, x_27);
x_29 = l_instDecidableNot___rarg(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = l_Leanpkg_readManifest___closed__4;
x_32 = lean_string_append(x_31, x_26);
lean_dec(x_26);
x_33 = l___private_Init_Data_Format_Basic_0__Std_Format_pushNewline___closed__1;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_34, x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_24);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_41 = x_35;
} else {
 lean_dec_ref(x_35);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_3);
if (x_43 == 0)
{
return x_3;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_3);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l_IO_FS_Handle_mk___at_Leanpkg_writeManifest___spec__2(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_IO_Prim_fopenFlags(x_2, x_3);
x_6 = lean_io_prim_handle_mk(x_1, x_5, x_4);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_IO_FS_Handle_putStr___at_Leanpkg_writeManifest___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_put_str(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_IO_FS_writeFile___at_Leanpkg_writeManifest___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = 1;
x_5 = 0;
x_6 = l_IO_FS_Handle_mk___at_Leanpkg_writeManifest___spec__2(x_1, x_4, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_io_prim_handle_put_str(x_7, x_2, x_8);
lean_dec(x_7);
return x_9;
}
else
{
uint8_t x_10; 
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
lean_object* l_Leanpkg_writeManifest(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_reprint(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_String_instInhabitedString;
x_6 = l_Option_get_x21___rarg___closed__4;
x_7 = lean_panic_fn(x_5, x_6);
x_8 = l_IO_FS_writeFile___at_Leanpkg_writeManifest___spec__1(x_2, x_7, x_3);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_IO_FS_writeFile___at_Leanpkg_writeManifest___spec__1(x_2, x_9, x_3);
lean_dec(x_9);
return x_10;
}
}
}
lean_object* l_IO_FS_Handle_mk___at_Leanpkg_writeManifest___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_IO_FS_Handle_mk___at_Leanpkg_writeManifest___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_IO_FS_Handle_putStr___at_Leanpkg_writeManifest___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Handle_putStr___at_Leanpkg_writeManifest___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_FS_writeFile___at_Leanpkg_writeManifest___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_writeFile___at_Leanpkg_writeManifest___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Leanpkg_writeManifest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Leanpkg_writeManifest(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Leanpkg_lockFileName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".leanpkg-lock");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_lockFileName() {
_start:
{
lean_object* x_1; 
x_1 = l_Leanpkg_lockFileName___closed__1;
return x_1;
}
}
lean_object* l_Leanpkg_withLockFile_acquire_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint32_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get_uint32(x_1, sizeof(void*)*1);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box_uint32(x_4);
x_7 = lean_apply_2(x_2, x_6, x_5);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Leanpkg_withLockFile_acquire_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_withLockFile_acquire_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Leanpkg_withLockFile_acquire___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = 300;
x_4 = l_IO_sleep(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = 0;
x_7 = l_Leanpkg_withLockFile_acquire(x_6, x_5);
return x_7;
}
else
{
uint8_t x_8; 
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
lean_object* l_Leanpkg_withLockFile_acquire___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Leanpkg_lockFileName;
x_4 = l_IO_Prim_fopenFlags___closed__6;
x_5 = lean_io_prim_handle_mk(x_3, x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Leanpkg_withLockFile_acquire___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Leanpkg_withLockFile_acquire___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Leanpkg_withLockFile_acquire___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Waiting for prior leanpkg invocation to finish... (remove '");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_withLockFile_acquire___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_withLockFile_acquire___closed__2;
x_2 = l_Leanpkg_lockFileName;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_withLockFile_acquire___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' if stuck)");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_withLockFile_acquire___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_withLockFile_acquire___closed__3;
x_2 = l_Leanpkg_withLockFile_acquire___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_withLockFile_acquire___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("wx");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_withLockFile_acquire___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Leanpkg_withLockFile_acquire___lambda__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Leanpkg_withLockFile_acquire___closed__8() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint32(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
lean_object* l_Leanpkg_withLockFile_acquire(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_19; 
x_19 = l_System_Platform_isWindows;
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Leanpkg_lockFileName;
x_21 = l_Leanpkg_withLockFile_acquire___closed__6;
x_22 = lean_io_prim_handle_mk(x_20, x_21, x_2);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_3 = x_29;
x_4 = x_30;
goto block_18;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Leanpkg_lockFileName;
x_32 = lean_io_file_exists(x_31, x_2);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = l_Leanpkg_withLockFile_acquire___closed__7;
x_37 = lean_box(0);
x_38 = lean_apply_2(x_36, x_37, x_35);
if (lean_obj_tag(x_38) == 0)
{
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_3 = x_39;
x_4 = x_40;
goto block_18;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
x_42 = l_Leanpkg_withLockFile_acquire___closed__8;
x_3 = x_42;
x_4 = x_41;
goto block_18;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_32, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_dec(x_32);
x_3 = x_43;
x_4 = x_44;
goto block_18;
}
}
block_18:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = l_Leanpkg_withLockFile_acquire___closed__1;
if (x_1 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, x_6, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Leanpkg_withLockFile_acquire___closed__5;
x_9 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_8, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_apply_2(x_5, x_10, x_11);
return x_12;
}
else
{
uint8_t x_13; 
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
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
}
}
lean_object* l_Leanpkg_withLockFile_acquire___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Leanpkg_withLockFile_acquire___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Leanpkg_withLockFile_acquire___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Leanpkg_withLockFile_acquire___lambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Leanpkg_withLockFile_acquire___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Leanpkg_withLockFile_acquire(x_3, x_2);
return x_4;
}
}
lean_object* l_IO_removeFile___at_Leanpkg_withLockFile___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_remove_file(x_1, x_2);
return x_3;
}
}
lean_object* l_Leanpkg_withLockFile___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 1;
x_4 = l_Leanpkg_withLockFile_acquire(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Leanpkg_lockFileName;
x_10 = lean_io_remove_file(x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec(x_6);
x_21 = l_Leanpkg_lockFileName;
x_22 = lean_io_remove_file(x_21, x_20);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_19);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_19);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
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
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
return x_4;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_4);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* l_Leanpkg_withLockFile(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_withLockFile___rarg), 2, 0);
return x_2;
}
}
lean_object* l_IO_removeFile___at_Leanpkg_withLockFile___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_removeFile___at_Leanpkg_withLockFile___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Leanpkg_configure_match__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_Leanpkg_configure_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Leanpkg_configure_match__1___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Leanpkg_configure_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Leanpkg_configure_match__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("./.");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("build");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__2;
x_2 = l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_List_forIn_loop___at_Leanpkg_configure___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__1;
x_8 = lean_string_dec_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_io_app_dir(x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_5);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_5);
x_13 = l_Leanpkg_gitParseRevision___closed__1;
x_14 = l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__3;
x_15 = l_Array_empty___closed__1;
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_15);
x_17 = l_Leanpkg_execCmd(x_16, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_1 = x_6;
x_2 = x_19;
x_3 = x_18;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_9);
if (x_25 == 0)
{
return x_9;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
x_29 = lean_box(0);
x_1 = x_6;
x_2 = x_29;
goto _start;
}
}
}
}
static lean_object* _init_l_List_map___at_Leanpkg_configure___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("/build");
return x_1;
}
}
lean_object* l_List_map___at_Leanpkg_configure___spec__2(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_List_map___at_Leanpkg_configure___spec__2___closed__1;
x_7 = lean_string_append(x_4, x_6);
x_8 = l_List_map___at_Leanpkg_configure___spec__2(x_5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_List_map___at_Leanpkg_configure___spec__2___closed__1;
x_12 = lean_string_append(x_9, x_11);
x_13 = l_List_map___at_Leanpkg_configure___spec__2(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Leanpkg_configure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("configuring ");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_configure___closed__2() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
x_2 = l_System_FilePath_searchPathSeparator;
x_3 = lean_string_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Leanpkg_configure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Leanpkg_readManifest(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = l_Leanpkg_configure___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l___private_Init_Data_Format_Basic_0__Std_Format_be___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_11, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Leanpkg_solveDeps(x_3, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Leanpkg_constructPath(x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = l_List_forIn_loop___at_Leanpkg_configure___spec__1(x_18, x_20, x_19);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_inc(x_18);
x_24 = l_List_map___at_Leanpkg_configure___spec__2(x_18);
x_25 = l_Leanpkg_configure___closed__2;
x_26 = l_String_intercalate(x_25, x_24);
x_27 = l_String_intercalate(x_25, x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
lean_inc(x_18);
x_30 = l_List_map___at_Leanpkg_configure___spec__2(x_18);
x_31 = l_Leanpkg_configure___closed__2;
x_32 = l_String_intercalate(x_31, x_30);
x_33 = l_String_intercalate(x_31, x_18);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_18);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_17);
if (x_40 == 0)
{
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_17);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_12);
if (x_48 == 0)
{
return x_12;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_12, 0);
x_50 = lean_ctor_get(x_12, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_12);
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
x_52 = !lean_is_exclusive(x_2);
if (x_52 == 0)
{
return x_2;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_2, 0);
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_2);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
lean_object* l_List_forIn_loop___at_Leanpkg_configure___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forIn_loop___at_Leanpkg_configure___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Leanpkg_execMake_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Leanpkg_execMake_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_execMake_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Leanpkg_execMake___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("/leanmake\" LEAN_OPTS=\"");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_execMake___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\" LEAN_PATH=\"");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_execMake___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\" ");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_execMake___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" >&2");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_execMake___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("-c");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_execMake___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_mkApp___closed__1;
x_2 = l_Leanpkg_execMake___lambda__1___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_execMake___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sh");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_execMake___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("-T");
return x_1;
}
}
lean_object* l_Leanpkg_execMake___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_7 = l_IO_appDir___at_Lean_getBuiltinSearchPath___spec__1(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_42; 
x_42 = lean_box(0);
x_8 = x_42;
goto block_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_6, 0);
lean_inc(x_43);
lean_dec(x_6);
x_44 = l_Nat_repr(x_43);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Leanpkg_execMake___lambda__1___closed__8;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_8 = x_48;
goto block_41;
}
block_41:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_List_append___rarg(x_8, x_1);
x_12 = l_String_quote___closed__2;
x_13 = lean_string_append(x_12, x_9);
lean_dec(x_9);
x_14 = l_Leanpkg_execMake___lambda__1___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = l___private_Init_Data_Format_Basic_0__Std_Format_be___closed__1;
x_17 = l_String_intercalate(x_16, x_11);
x_18 = lean_string_append(x_15, x_17);
lean_dec(x_17);
x_19 = l_Leanpkg_execMake___lambda__1___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_string_append(x_20, x_2);
x_22 = l_Leanpkg_execMake___lambda__1___closed__3;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_String_intercalate(x_16, x_3);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = l_Leanpkg_execMake___lambda__1___closed__4;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Leanpkg_execMake___lambda__1___closed__6;
x_29 = lean_array_push(x_28, x_27);
x_30 = l_Leanpkg_Manifest_effectivePath(x_4);
lean_dec(x_4);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Leanpkg_gitParseRevision___closed__1;
x_33 = l_Leanpkg_execMake___lambda__1___closed__7;
x_34 = l_Array_empty___closed__1;
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set(x_35, 4, x_34);
x_36 = l_Leanpkg_execCmd(x_35, x_10);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_7);
if (x_37 == 0)
{
return x_7;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_7, 0);
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_7);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
static lean_object* _init_l_Leanpkg_execMake___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Leanpkg_readManifest), 1, 0);
return x_1;
}
}
lean_object* l_Leanpkg_execMake(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_alloc_closure((void*)(l_Leanpkg_execMake___lambda__1___boxed), 5, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_1);
x_6 = l_Leanpkg_execMake___closed__1;
x_7 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = l_Leanpkg_withLockFile___rarg(x_7, x_4);
return x_8;
}
}
lean_object* l_Leanpkg_execMake___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Leanpkg_execMake___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_List_map___at_Leanpkg_buildImports___spec__1(lean_object* x_1) {
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
x_6 = l_String_toName(x_4);
x_7 = l_List_map___at_Leanpkg_buildImports___spec__1(x_5);
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
x_10 = l_String_toName(x_8);
x_11 = l_List_map___at_Leanpkg_buildImports___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_filterAux___at_Leanpkg_buildImports___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_Name_getRoot(x_6);
x_9 = l_Lean_Name_toString___closed__1;
x_10 = l_Lean_Name_toStringWithSep(x_9, x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_String_mapAux___at_String_toLower___spec__1(x_11, x_10);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = l_String_mapAux___at_String_toLower___spec__1(x_11, x_13);
x_15 = lean_string_dec_eq(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
if (x_15 == 0)
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = l_Lean_Name_getRoot(x_18);
x_21 = l_Lean_Name_toString___closed__1;
x_22 = l_Lean_Name_toStringWithSep(x_21, x_20);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_String_mapAux___at_String_toLower___spec__1(x_23, x_22);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = l_String_mapAux___at_String_toLower___spec__1(x_23, x_25);
x_27 = lean_string_dec_eq(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_dec(x_18);
x_2 = x_19;
goto _start;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_3);
x_2 = x_19;
x_3 = x_29;
goto _start;
}
}
}
}
}
static lean_object* _init_l_List_map___at_Leanpkg_buildImports___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\"build");
return x_1;
}
}
static lean_object* _init_l_List_map___at_Leanpkg_buildImports___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".olean\"");
return x_1;
}
}
lean_object* l_List_map___at_Leanpkg_buildImports___spec__3(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_modPathToFilePath(x_4);
lean_dec(x_4);
x_7 = l_List_map___at_Leanpkg_buildImports___spec__3___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_List_map___at_Leanpkg_buildImports___spec__3___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_List_map___at_Leanpkg_buildImports___spec__3(x_5);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_modPathToFilePath(x_12);
lean_dec(x_12);
x_15 = l_List_map___at_Leanpkg_buildImports___spec__3___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_List_map___at_Leanpkg_buildImports___spec__3___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_List_map___at_Leanpkg_buildImports___spec__3(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Leanpkg_buildImports___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_IO_println___at_Lean_instEval___spec__1(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_IO_println___at_Lean_instEval___spec__1(x_7, x_6);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_1);
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
lean_object* l_Leanpkg_buildImports___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Leanpkg_readManifest(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Leanpkg_configure(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_map___at_Leanpkg_buildImports___spec__1(x_1);
x_12 = lean_box(0);
x_13 = l_List_filterAux___at_Leanpkg_buildImports___spec__2(x_6, x_11, x_12);
x_14 = l_List_beq___at_Lean_OpenDecl_instToStringOpenDecl___spec__1(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_List_map___at_Leanpkg_buildImports___spec__3(x_13);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
x_17 = l_Leanpkg_execMake(x_15, x_2, x_16, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Leanpkg_buildImports___lambda__1(x_9, x_18, x_19);
lean_dec(x_18);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_2);
x_25 = lean_box(0);
x_26 = l_Leanpkg_buildImports___lambda__1(x_9, x_25, x_10);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
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
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
return x_5;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_5, 0);
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_5);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* l_Leanpkg_buildImports(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Leanpkg_leanpkgTomlFn;
x_5 = lean_io_file_exists(x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_box(0);
x_16 = l_Leanpkg_buildImports___lambda__2(x_1, x_2, x_15, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l_Leanpkg_buildImports___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Leanpkg_buildImports___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Leanpkg_buildImports___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Leanpkg_buildImports___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Leanpkg_build(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Leanpkg_configure(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Leanpkg_execMake(x_6, x_1, x_7, x_5);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Leanpkg_initGitignoreContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("/build\n");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_initGitignoreContents() {
_start:
{
lean_object* x_1; 
x_1 = l_Leanpkg_initGitignoreContents___closed__1;
return x_1;
}
}
lean_object* l_IO_FS_Handle_putStr___at_Leanpkg_initPkg___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_put_str(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_IO_FS_writeFile___at_Leanpkg_initPkg___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = 1;
x_5 = 0;
x_6 = l_IO_FS_Handle_mk___at_Lean_Parser_testParseFile___spec__2(x_1, x_4, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_io_prim_handle_put_str(x_7, x_2, x_8);
lean_dec(x_7);
return x_9;
}
else
{
uint8_t x_10; 
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
static lean_object* _init_l_Leanpkg_initPkg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[package]\nname = \"");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_initPkg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\"\nversion = \"0.1\"\n");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_initPkg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".lean");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_initPkg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("def main : IO Unit :=\n  IO.println \"Hello, world!\"\n");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_initPkg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".gitignore");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_initPkg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".git");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_initPkg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_mkApp___closed__1;
x_2 = l_Lean_initFn____x40_Lean_Compiler_InitAttr___hyg_535____closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_initPkg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_initPkg___closed__7;
x_2 = l_Leanpkg_gitParseRevision___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_initPkg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Leanpkg_gitParseRevision___closed__1;
x_3 = l_Leanpkg_gitParseRevision___closed__9;
x_4 = l_Leanpkg_initPkg___closed__8;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static uint8_t _init_l_Leanpkg_initPkg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Leanpkg_upstreamGitBranch;
x_2 = l_Leanpkg_leanVersionString___closed__3;
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_initPkg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("-B");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_initPkg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_materialize___lambda__1___closed__2;
x_2 = l_Leanpkg_initPkg___closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_initPkg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_initPkg___closed__12;
x_2 = l_Leanpkg_upstreamGitBranch;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_initPkg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Leanpkg_gitParseRevision___closed__1;
x_3 = l_Leanpkg_gitParseRevision___closed__9;
x_4 = l_Leanpkg_initPkg___closed__13;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Leanpkg_initPkg___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("WARNING: failed to initialize git repository");
return x_1;
}
}
lean_object* l_Leanpkg_initPkg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Leanpkg_initPkg___closed__1;
x_5 = lean_string_append(x_4, x_1);
x_6 = l_Leanpkg_initPkg___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_Leanpkg_leanpkgTomlFn;
x_9 = l_IO_FS_writeFile___at_Leanpkg_initPkg___spec__1(x_8, x_7, x_3);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_String_capitalize(x_1);
x_12 = l_Lean_instInhabitedParserDescr___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Leanpkg_initPkg___closed__3;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Leanpkg_initPkg___closed__4;
x_17 = l_IO_FS_writeFile___at_Leanpkg_initPkg___spec__1(x_15, x_16, x_10);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Leanpkg_initPkg___closed__5;
x_20 = 3;
x_21 = 0;
x_22 = l_IO_FS_Handle_mk___at_Lean_Parser_testParseFile___spec__2(x_19, x_20, x_21, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Leanpkg_initGitignoreContents;
x_26 = lean_io_prim_handle_put_str(x_23, x_25, x_24);
lean_dec(x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Leanpkg_initPkg___closed__6;
x_29 = lean_io_is_dir(x_28, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l_Leanpkg_initPkg___closed__9;
x_34 = l_Leanpkg_execCmd(x_33, x_32);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_34, 1);
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = l_Leanpkg_initPkg___closed__10;
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_free_object(x_34);
x_39 = l_Leanpkg_initPkg___closed__14;
x_40 = l_Leanpkg_execCmd(x_39, x_36);
if (lean_obj_tag(x_40) == 0)
{
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Leanpkg_initPkg___closed__15;
x_43 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_42, x_41);
return x_43;
}
}
else
{
lean_object* x_44; 
x_44 = lean_box(0);
lean_ctor_set(x_34, 0, x_44);
return x_34;
}
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_34, 1);
lean_inc(x_45);
lean_dec(x_34);
x_46 = l_Leanpkg_initPkg___closed__10;
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Leanpkg_initPkg___closed__14;
x_48 = l_Leanpkg_execCmd(x_47, x_45);
if (lean_obj_tag(x_48) == 0)
{
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Leanpkg_initPkg___closed__15;
x_51 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_50, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_45);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
lean_dec(x_34);
x_55 = l_Leanpkg_initPkg___closed__15;
x_56 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_55, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_29);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_29, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_29, 0, x_59);
return x_29;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_29, 1);
lean_inc(x_60);
lean_dec(x_29);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_29);
if (x_63 == 0)
{
return x_29;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_29, 0);
x_65 = lean_ctor_get(x_29, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_29);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_26);
if (x_67 == 0)
{
return x_26;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_26, 0);
x_69 = lean_ctor_get(x_26, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_26);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_22);
if (x_71 == 0)
{
return x_22;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_22, 0);
x_73 = lean_ctor_get(x_22, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_22);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_17);
if (x_75 == 0)
{
return x_17;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_17, 0);
x_77 = lean_ctor_get(x_17, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_17);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_9);
if (x_79 == 0)
{
return x_9;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_9, 0);
x_81 = lean_ctor_get(x_9, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_9);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
lean_object* l_IO_FS_Handle_putStr___at_Leanpkg_initPkg___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Handle_putStr___at_Leanpkg_initPkg___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_FS_writeFile___at_Leanpkg_initPkg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_writeFile___at_Leanpkg_initPkg___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Leanpkg_initPkg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Leanpkg_initPkg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_Leanpkg_init(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = l_Leanpkg_initPkg(x_1, x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Leanpkg_usage___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean package manager, version ");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_usage___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_usage___closed__1;
x_2 = l_Leanpkg_uiLeanVersionString;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_usage___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n\nUsage: leanpkg <command>\n\nconfigure              download and build dependencies and print resulting LEAN_PATH\nbuild [-- <Lean-args>] configure and build *.olean files\ninit <name>            create a Lean package in the current directory\n\nSee `leanpkg help <command>` for more information on a specific command.");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_usage___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_usage___closed__2;
x_2 = l_Leanpkg_usage___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_usage() {
_start:
{
lean_object* x_1; 
x_1 = l_Leanpkg_usage___closed__4;
return x_1;
}
}
static lean_object* _init_l_Leanpkg_main_match__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("configure");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_main_match__1___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("print-paths");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_main_match__1___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("help");
return x_1;
}
}
lean_object* l_Leanpkg_main_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Leanpkg_main_match__1___rarg___closed__1;
x_14 = lean_string_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_4);
x_15 = l_Leanpkg_main_match__1___rarg___closed__2;
x_16 = lean_string_dec_eq(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_5);
x_17 = l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__2;
x_18 = lean_string_dec_eq(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
x_19 = l_Lean_initFn____x40_Lean_Compiler_InitAttr___hyg_535____closed__1;
x_20 = lean_string_dec_eq(x_1, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_7);
x_21 = l_Leanpkg_main_match__1___rarg___closed__3;
x_22 = lean_string_dec_eq(x_1, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_23 = lean_apply_3(x_12, x_1, x_2, x_3);
return x_23;
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_24; 
lean_dec(x_12);
x_24 = lean_apply_1(x_11, x_3);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_11);
x_25 = lean_apply_3(x_12, x_21, x_2, x_3);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
x_28 = lean_string_dec_eq(x_26, x_13);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_8);
x_29 = lean_string_dec_eq(x_26, x_17);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_9);
x_30 = lean_string_dec_eq(x_26, x_19);
lean_dec(x_26);
if (x_30 == 0)
{
lean_dec(x_27);
lean_dec(x_10);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_31; 
lean_dec(x_12);
x_31 = lean_apply_1(x_11, x_2);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_11);
x_32 = lean_apply_3(x_12, x_21, x_2, x_3);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_2, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_2, 0);
lean_dec(x_35);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_11);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_2);
lean_dec(x_12);
x_36 = lean_box(0);
x_37 = lean_apply_1(x_10, x_36);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_19);
x_38 = lean_apply_3(x_12, x_21, x_2, x_3);
return x_38;
}
}
else
{
lean_dec(x_10);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_39; 
lean_dec(x_12);
lean_ctor_set(x_2, 0, x_19);
x_39 = lean_apply_1(x_11, x_2);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_11);
lean_ctor_set(x_2, 0, x_19);
x_40 = lean_apply_3(x_12, x_21, x_2, x_3);
return x_40;
}
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_11);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_12);
x_41 = lean_box(0);
x_42 = lean_apply_1(x_10, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_19);
lean_ctor_set(x_43, 1, x_27);
x_44 = lean_apply_3(x_12, x_21, x_43, x_3);
return x_44;
}
}
else
{
lean_dec(x_10);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_12);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_19);
lean_ctor_set(x_45, 1, x_27);
x_46 = lean_apply_1(x_11, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_19);
lean_ctor_set(x_47, 1, x_27);
x_48 = lean_apply_3(x_12, x_21, x_47, x_3);
return x_48;
}
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_26);
lean_dec(x_10);
x_49 = !lean_is_exclusive(x_2);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_2, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_2, 0);
lean_dec(x_51);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_11);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_free_object(x_2);
lean_dec(x_12);
x_52 = lean_box(0);
x_53 = lean_apply_1(x_9, x_52);
return x_53;
}
else
{
lean_object* x_54; 
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_17);
x_54 = lean_apply_3(x_12, x_21, x_2, x_3);
return x_54;
}
}
else
{
lean_dec(x_9);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_55; 
lean_dec(x_12);
lean_ctor_set(x_2, 0, x_17);
x_55 = lean_apply_1(x_11, x_2);
return x_55;
}
else
{
lean_object* x_56; 
lean_dec(x_11);
lean_ctor_set(x_2, 0, x_17);
x_56 = lean_apply_3(x_12, x_21, x_2, x_3);
return x_56;
}
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_11);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_12);
x_57 = lean_box(0);
x_58 = lean_apply_1(x_9, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_9);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_17);
lean_ctor_set(x_59, 1, x_27);
x_60 = lean_apply_3(x_12, x_21, x_59, x_3);
return x_60;
}
}
else
{
lean_dec(x_9);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_12);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_17);
lean_ctor_set(x_61, 1, x_27);
x_62 = lean_apply_1(x_11, x_61);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_11);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_17);
lean_ctor_set(x_63, 1, x_27);
x_64 = lean_apply_3(x_12, x_21, x_63, x_3);
return x_64;
}
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
x_65 = !lean_is_exclusive(x_2);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_2, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_2, 0);
lean_dec(x_67);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_11);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_free_object(x_2);
lean_dec(x_12);
x_68 = lean_box(0);
x_69 = lean_apply_1(x_8, x_68);
return x_69;
}
else
{
lean_object* x_70; 
lean_dec(x_8);
lean_ctor_set(x_2, 0, x_13);
x_70 = lean_apply_3(x_12, x_21, x_2, x_3);
return x_70;
}
}
else
{
lean_dec(x_8);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_71; 
lean_dec(x_12);
lean_ctor_set(x_2, 0, x_13);
x_71 = lean_apply_1(x_11, x_2);
return x_71;
}
else
{
lean_object* x_72; 
lean_dec(x_11);
lean_ctor_set(x_2, 0, x_13);
x_72 = lean_apply_3(x_12, x_21, x_2, x_3);
return x_72;
}
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_11);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_12);
x_73 = lean_box(0);
x_74 = lean_apply_1(x_8, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_8);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_13);
lean_ctor_set(x_75, 1, x_27);
x_76 = lean_apply_3(x_12, x_21, x_75, x_3);
return x_76;
}
}
else
{
lean_dec(x_8);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_12);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_13);
lean_ctor_set(x_77, 1, x_27);
x_78 = lean_apply_1(x_11, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_11);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_13);
lean_ctor_set(x_79, 1, x_27);
x_80 = lean_apply_3(x_12, x_21, x_79, x_3);
return x_80;
}
}
}
}
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_81; 
lean_dec(x_7);
x_81 = lean_apply_3(x_12, x_19, x_2, x_3);
return x_81;
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_2, 1);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_12);
x_83 = lean_ctor_get(x_2, 0);
lean_inc(x_83);
lean_dec(x_2);
x_84 = lean_apply_1(x_7, x_83);
return x_84;
}
else
{
lean_object* x_85; 
lean_dec(x_7);
x_85 = lean_apply_3(x_12, x_19, x_2, x_3);
return x_85;
}
}
else
{
lean_object* x_86; 
lean_dec(x_82);
lean_dec(x_7);
x_86 = lean_apply_3(x_12, x_19, x_2, x_3);
return x_86;
}
}
}
}
else
{
lean_object* x_87; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_87 = lean_apply_2(x_6, x_2, x_3);
return x_87;
}
}
else
{
lean_object* x_88; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_88 = lean_apply_2(x_5, x_2, x_3);
return x_88;
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_12);
x_89 = lean_box(0);
x_90 = lean_apply_1(x_4, x_89);
return x_90;
}
else
{
lean_object* x_91; 
lean_dec(x_4);
x_91 = lean_apply_3(x_12, x_13, x_2, x_3);
return x_91;
}
}
else
{
lean_object* x_92; 
lean_dec(x_4);
x_92 = lean_apply_3(x_12, x_13, x_2, x_3);
return x_92;
}
}
}
}
lean_object* l_Leanpkg_main_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_main_match__1___rarg), 12, 0);
return x_2;
}
}
static lean_object* _init_l_Leanpkg_main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Leanpkg_usage;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Leanpkg_main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Create a new Lean package in the current directory\n\nUsage:\n  leanpkg init <name>\n\nThis command creates a new Lean package with the given name in the current\ndirectory.");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("download dependencies and build *.olean files\n\nUsage:\n  leanpkg build [-- <lean-args>]\n\nThis command invokes `Leanpkg configure` followed by\n`Leanmake <lean-args>`, building the package's Lean files as well as\n(transitively) imported files of dependencies. If defined, the `package.timeout`\nconfiguration value is passed to Lean via its `-T` parameter.");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Download dependencies\n\nUsage:\n  leanpkg configure\n\nThis command sets up the `build/deps` directory.\n\nFor each (transitive) git dependency, the specified commit is checked out\ninto a sub-directory of `build/deps`. If there are dependencies on multiple\nversions of the same package, the version materialized is undefined. No copy\nis made of local dependencies.");
return x_1;
}
}
lean_object* l_Leanpkg_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Leanpkg_main_match__1___rarg___closed__1;
x_6 = lean_string_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Leanpkg_main_match__1___rarg___closed__2;
x_8 = lean_string_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__2;
x_10 = lean_string_dec_eq(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_initFn____x40_Lean_Compiler_InitAttr___hyg_535____closed__1;
x_12 = lean_string_dec_eq(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Leanpkg_main_match__1___rarg___closed__3;
x_14 = lean_string_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = l_Leanpkg_main___closed__1;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Leanpkg_usage;
x_18 = l_IO_println___at_Lean_instEval___spec__1(x_17, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_19 = l_Leanpkg_main___closed__1;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_string_dec_eq(x_21, x_5);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = lean_string_dec_eq(x_21, x_9);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_string_dec_eq(x_21, x_11);
lean_dec(x_21);
if (x_25 == 0)
{
lean_dec(x_22);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Leanpkg_usage;
x_27 = l_IO_println___at_Lean_instEval___spec__1(x_26, x_4);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
x_28 = l_Leanpkg_main___closed__1;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_4);
return x_29;
}
}
else
{
if (lean_obj_tag(x_22) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Leanpkg_main___closed__2;
x_31 = l_IO_println___at_Lean_instEval___spec__1(x_30, x_4);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
x_32 = l_Leanpkg_main___closed__1;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
return x_33;
}
}
else
{
lean_dec(x_22);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Leanpkg_usage;
x_35 = l_IO_println___at_Lean_instEval___spec__1(x_34, x_4);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_3);
x_36 = l_Leanpkg_main___closed__1;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_4);
return x_37;
}
}
}
}
else
{
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Leanpkg_main___closed__3;
x_39 = l_IO_println___at_Lean_instEval___spec__1(x_38, x_4);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_3);
x_40 = l_Leanpkg_main___closed__1;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
return x_41;
}
}
else
{
lean_dec(x_22);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Leanpkg_usage;
x_43 = l_IO_println___at_Lean_instEval___spec__1(x_42, x_4);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_3);
x_44 = l_Leanpkg_main___closed__1;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_4);
return x_45;
}
}
}
}
else
{
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_Leanpkg_main___closed__4;
x_47 = l_IO_println___at_Lean_instEval___spec__1(x_46, x_4);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
x_48 = l_Leanpkg_main___closed__1;
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_4);
return x_49;
}
}
else
{
lean_dec(x_22);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Leanpkg_usage;
x_51 = l_IO_println___at_Lean_instEval___spec__1(x_50, x_4);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_3);
x_52 = l_Leanpkg_main___closed__1;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
return x_53;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_3);
x_54 = l_Leanpkg_main___closed__1;
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_4);
return x_55;
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
if (lean_obj_tag(x_56) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_2, 0);
lean_inc(x_57);
lean_dec(x_2);
x_58 = 0;
x_59 = l_Leanpkg_initPkg(x_57, x_58, x_4);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_3);
lean_dec(x_2);
x_60 = l_Leanpkg_main___closed__1;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_4);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_56);
lean_dec(x_3);
lean_dec(x_2);
x_62 = l_Leanpkg_main___closed__1;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_4);
return x_63;
}
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_2);
x_64 = l_Leanpkg_build(x_3, x_4);
return x_64;
}
}
else
{
lean_object* x_65; 
x_65 = l_Leanpkg_buildImports(x_2, x_3, x_4);
return x_65;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_66; 
x_66 = l_Leanpkg_configure(x_4);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set(x_66, 0, x_69);
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_66);
if (x_73 == 0)
{
return x_66;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_66, 0);
x_75 = lean_ctor_get(x_66, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_66);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_3);
x_77 = l_Leanpkg_main___closed__1;
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_4);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_3);
lean_dec(x_2);
x_79 = l_Leanpkg_main___closed__1;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_4);
return x_80;
}
}
}
}
lean_object* l_Leanpkg_main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Leanpkg_main(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("--");
return x_1;
}
}
lean_object* l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_partition___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore___closed__1;
x_7 = lean_string_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore(x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_1);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_18 = l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore___closed__1;
x_19 = lean_string_dec_eq(x_16, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore(x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_21);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_16);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_17);
return x_27;
}
}
}
}
}
lean_object* l_Leanpkg_splitCmdlineArgs_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Leanpkg_splitCmdlineArgs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_splitCmdlineArgs_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Leanpkg_splitCmdlineArgs_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_2(x_4, x_10, x_7);
return x_11;
}
}
}
}
lean_object* l_Leanpkg_splitCmdlineArgs_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_splitCmdlineArgs_match__2___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Leanpkg_splitCmdlineArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Leanpkg_main___closed__1;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_List_partition___rarg___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore(x_5);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_2);
return x_19;
}
}
}
}
}
lean_object* l_main_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_main_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_main_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* _lean_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_init_search_path(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Leanpkg_splitCmdlineArgs(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Leanpkg_main(x_10, x_11, x_12, x_9);
lean_dec(x_10);
return x_13;
}
else
{
uint8_t x_14; 
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
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
return x_4;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_4);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Leanpkg_Resolve(lean_object*);
lean_object* initialize_Leanpkg_Git(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Leanpkg(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Leanpkg_Resolve(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Leanpkg_Git(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Leanpkg_readManifest___closed__1 = _init_l_Leanpkg_readManifest___closed__1();
lean_mark_persistent(l_Leanpkg_readManifest___closed__1);
l_Leanpkg_readManifest___closed__2 = _init_l_Leanpkg_readManifest___closed__2();
lean_mark_persistent(l_Leanpkg_readManifest___closed__2);
l_Leanpkg_readManifest___closed__3 = _init_l_Leanpkg_readManifest___closed__3();
lean_mark_persistent(l_Leanpkg_readManifest___closed__3);
l_Leanpkg_readManifest___closed__4 = _init_l_Leanpkg_readManifest___closed__4();
lean_mark_persistent(l_Leanpkg_readManifest___closed__4);
l_Leanpkg_lockFileName___closed__1 = _init_l_Leanpkg_lockFileName___closed__1();
lean_mark_persistent(l_Leanpkg_lockFileName___closed__1);
l_Leanpkg_lockFileName = _init_l_Leanpkg_lockFileName();
lean_mark_persistent(l_Leanpkg_lockFileName);
l_Leanpkg_withLockFile_acquire___closed__1 = _init_l_Leanpkg_withLockFile_acquire___closed__1();
lean_mark_persistent(l_Leanpkg_withLockFile_acquire___closed__1);
l_Leanpkg_withLockFile_acquire___closed__2 = _init_l_Leanpkg_withLockFile_acquire___closed__2();
lean_mark_persistent(l_Leanpkg_withLockFile_acquire___closed__2);
l_Leanpkg_withLockFile_acquire___closed__3 = _init_l_Leanpkg_withLockFile_acquire___closed__3();
lean_mark_persistent(l_Leanpkg_withLockFile_acquire___closed__3);
l_Leanpkg_withLockFile_acquire___closed__4 = _init_l_Leanpkg_withLockFile_acquire___closed__4();
lean_mark_persistent(l_Leanpkg_withLockFile_acquire___closed__4);
l_Leanpkg_withLockFile_acquire___closed__5 = _init_l_Leanpkg_withLockFile_acquire___closed__5();
lean_mark_persistent(l_Leanpkg_withLockFile_acquire___closed__5);
l_Leanpkg_withLockFile_acquire___closed__6 = _init_l_Leanpkg_withLockFile_acquire___closed__6();
lean_mark_persistent(l_Leanpkg_withLockFile_acquire___closed__6);
l_Leanpkg_withLockFile_acquire___closed__7 = _init_l_Leanpkg_withLockFile_acquire___closed__7();
lean_mark_persistent(l_Leanpkg_withLockFile_acquire___closed__7);
l_Leanpkg_withLockFile_acquire___closed__8 = _init_l_Leanpkg_withLockFile_acquire___closed__8();
lean_mark_persistent(l_Leanpkg_withLockFile_acquire___closed__8);
l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__1 = _init_l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__1);
l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__2 = _init_l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__2);
l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__3 = _init_l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__3();
lean_mark_persistent(l_List_forIn_loop___at_Leanpkg_configure___spec__1___closed__3);
l_List_map___at_Leanpkg_configure___spec__2___closed__1 = _init_l_List_map___at_Leanpkg_configure___spec__2___closed__1();
lean_mark_persistent(l_List_map___at_Leanpkg_configure___spec__2___closed__1);
l_Leanpkg_configure___closed__1 = _init_l_Leanpkg_configure___closed__1();
lean_mark_persistent(l_Leanpkg_configure___closed__1);
l_Leanpkg_configure___closed__2 = _init_l_Leanpkg_configure___closed__2();
lean_mark_persistent(l_Leanpkg_configure___closed__2);
l_Leanpkg_execMake___lambda__1___closed__1 = _init_l_Leanpkg_execMake___lambda__1___closed__1();
lean_mark_persistent(l_Leanpkg_execMake___lambda__1___closed__1);
l_Leanpkg_execMake___lambda__1___closed__2 = _init_l_Leanpkg_execMake___lambda__1___closed__2();
lean_mark_persistent(l_Leanpkg_execMake___lambda__1___closed__2);
l_Leanpkg_execMake___lambda__1___closed__3 = _init_l_Leanpkg_execMake___lambda__1___closed__3();
lean_mark_persistent(l_Leanpkg_execMake___lambda__1___closed__3);
l_Leanpkg_execMake___lambda__1___closed__4 = _init_l_Leanpkg_execMake___lambda__1___closed__4();
lean_mark_persistent(l_Leanpkg_execMake___lambda__1___closed__4);
l_Leanpkg_execMake___lambda__1___closed__5 = _init_l_Leanpkg_execMake___lambda__1___closed__5();
lean_mark_persistent(l_Leanpkg_execMake___lambda__1___closed__5);
l_Leanpkg_execMake___lambda__1___closed__6 = _init_l_Leanpkg_execMake___lambda__1___closed__6();
lean_mark_persistent(l_Leanpkg_execMake___lambda__1___closed__6);
l_Leanpkg_execMake___lambda__1___closed__7 = _init_l_Leanpkg_execMake___lambda__1___closed__7();
lean_mark_persistent(l_Leanpkg_execMake___lambda__1___closed__7);
l_Leanpkg_execMake___lambda__1___closed__8 = _init_l_Leanpkg_execMake___lambda__1___closed__8();
lean_mark_persistent(l_Leanpkg_execMake___lambda__1___closed__8);
l_Leanpkg_execMake___closed__1 = _init_l_Leanpkg_execMake___closed__1();
lean_mark_persistent(l_Leanpkg_execMake___closed__1);
l_List_map___at_Leanpkg_buildImports___spec__3___closed__1 = _init_l_List_map___at_Leanpkg_buildImports___spec__3___closed__1();
lean_mark_persistent(l_List_map___at_Leanpkg_buildImports___spec__3___closed__1);
l_List_map___at_Leanpkg_buildImports___spec__3___closed__2 = _init_l_List_map___at_Leanpkg_buildImports___spec__3___closed__2();
lean_mark_persistent(l_List_map___at_Leanpkg_buildImports___spec__3___closed__2);
l_Leanpkg_initGitignoreContents___closed__1 = _init_l_Leanpkg_initGitignoreContents___closed__1();
lean_mark_persistent(l_Leanpkg_initGitignoreContents___closed__1);
l_Leanpkg_initGitignoreContents = _init_l_Leanpkg_initGitignoreContents();
lean_mark_persistent(l_Leanpkg_initGitignoreContents);
l_Leanpkg_initPkg___closed__1 = _init_l_Leanpkg_initPkg___closed__1();
lean_mark_persistent(l_Leanpkg_initPkg___closed__1);
l_Leanpkg_initPkg___closed__2 = _init_l_Leanpkg_initPkg___closed__2();
lean_mark_persistent(l_Leanpkg_initPkg___closed__2);
l_Leanpkg_initPkg___closed__3 = _init_l_Leanpkg_initPkg___closed__3();
lean_mark_persistent(l_Leanpkg_initPkg___closed__3);
l_Leanpkg_initPkg___closed__4 = _init_l_Leanpkg_initPkg___closed__4();
lean_mark_persistent(l_Leanpkg_initPkg___closed__4);
l_Leanpkg_initPkg___closed__5 = _init_l_Leanpkg_initPkg___closed__5();
lean_mark_persistent(l_Leanpkg_initPkg___closed__5);
l_Leanpkg_initPkg___closed__6 = _init_l_Leanpkg_initPkg___closed__6();
lean_mark_persistent(l_Leanpkg_initPkg___closed__6);
l_Leanpkg_initPkg___closed__7 = _init_l_Leanpkg_initPkg___closed__7();
lean_mark_persistent(l_Leanpkg_initPkg___closed__7);
l_Leanpkg_initPkg___closed__8 = _init_l_Leanpkg_initPkg___closed__8();
lean_mark_persistent(l_Leanpkg_initPkg___closed__8);
l_Leanpkg_initPkg___closed__9 = _init_l_Leanpkg_initPkg___closed__9();
lean_mark_persistent(l_Leanpkg_initPkg___closed__9);
l_Leanpkg_initPkg___closed__10 = _init_l_Leanpkg_initPkg___closed__10();
l_Leanpkg_initPkg___closed__11 = _init_l_Leanpkg_initPkg___closed__11();
lean_mark_persistent(l_Leanpkg_initPkg___closed__11);
l_Leanpkg_initPkg___closed__12 = _init_l_Leanpkg_initPkg___closed__12();
lean_mark_persistent(l_Leanpkg_initPkg___closed__12);
l_Leanpkg_initPkg___closed__13 = _init_l_Leanpkg_initPkg___closed__13();
lean_mark_persistent(l_Leanpkg_initPkg___closed__13);
l_Leanpkg_initPkg___closed__14 = _init_l_Leanpkg_initPkg___closed__14();
lean_mark_persistent(l_Leanpkg_initPkg___closed__14);
l_Leanpkg_initPkg___closed__15 = _init_l_Leanpkg_initPkg___closed__15();
lean_mark_persistent(l_Leanpkg_initPkg___closed__15);
l_Leanpkg_usage___closed__1 = _init_l_Leanpkg_usage___closed__1();
lean_mark_persistent(l_Leanpkg_usage___closed__1);
l_Leanpkg_usage___closed__2 = _init_l_Leanpkg_usage___closed__2();
lean_mark_persistent(l_Leanpkg_usage___closed__2);
l_Leanpkg_usage___closed__3 = _init_l_Leanpkg_usage___closed__3();
lean_mark_persistent(l_Leanpkg_usage___closed__3);
l_Leanpkg_usage___closed__4 = _init_l_Leanpkg_usage___closed__4();
lean_mark_persistent(l_Leanpkg_usage___closed__4);
l_Leanpkg_usage = _init_l_Leanpkg_usage();
lean_mark_persistent(l_Leanpkg_usage);
l_Leanpkg_main_match__1___rarg___closed__1 = _init_l_Leanpkg_main_match__1___rarg___closed__1();
lean_mark_persistent(l_Leanpkg_main_match__1___rarg___closed__1);
l_Leanpkg_main_match__1___rarg___closed__2 = _init_l_Leanpkg_main_match__1___rarg___closed__2();
lean_mark_persistent(l_Leanpkg_main_match__1___rarg___closed__2);
l_Leanpkg_main_match__1___rarg___closed__3 = _init_l_Leanpkg_main_match__1___rarg___closed__3();
lean_mark_persistent(l_Leanpkg_main_match__1___rarg___closed__3);
l_Leanpkg_main___closed__1 = _init_l_Leanpkg_main___closed__1();
lean_mark_persistent(l_Leanpkg_main___closed__1);
l_Leanpkg_main___closed__2 = _init_l_Leanpkg_main___closed__2();
lean_mark_persistent(l_Leanpkg_main___closed__2);
l_Leanpkg_main___closed__3 = _init_l_Leanpkg_main___closed__3();
lean_mark_persistent(l_Leanpkg_main___closed__3);
l_Leanpkg_main___closed__4 = _init_l_Leanpkg_main___closed__4();
lean_mark_persistent(l_Leanpkg_main___closed__4);
l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore___closed__1 = _init_l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore___closed__1();
lean_mark_persistent(l___private_Leanpkg_0__Leanpkg_splitCmdlineArgsCore___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
void lean_initialize();

  #if defined(WIN32) || defined(_WIN32)
  #include <windows.h>
  #endif

  int main(int argc, char ** argv) {
  #if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  #endif
  lean_object* in; lean_object* res;
lean_initialize();
res = initialize_Leanpkg(lean_io_mk_world());
lean_io_mark_end_initialization();
if (lean_io_result_is_ok(res)) {
lean_dec_ref(res);
lean_init_task_manager();
in = lean_box(0);
int i = argc;
while (i > 1) {
 lean_object* n;
 i--;
 n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);
 in = n;
}
res = _lean_main(in, lean_io_mk_world());
}
if (lean_io_result_is_ok(res)) {
  int ret = lean_unbox(lean_io_result_get_value(res));
  lean_dec_ref(res);
  return ret;
} else {
  lean_io_result_show_error(res);
  lean_dec_ref(res);
  return 1;
}
}
#ifdef __cplusplus
}
#endif
