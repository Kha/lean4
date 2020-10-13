// Lean compiler output
// Module: Init.System.IO
// Imports: Init.Control.EState Init.Control.Reader Init.Data.String Init.Data.ByteArray Init.System.IOError Init.System.FilePath Init.System.ST
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
lean_object* l_IO_FS_linesAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_IO_cancel___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_linesAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_getStdin___rarg___closed__1;
lean_object* l_IO_FS_Handle_putStrLn___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_getStdout(lean_object*, lean_object*);
lean_object* l_IO_FS_withIsolatedStreams___rarg(lean_object*, lean_object*);
lean_object* l_ByteArray_findIdxAux___main___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_allocprof___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_mkRef___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stdin(lean_object*);
extern uint8_t l_System_Platform_isWindows;
lean_object* l_IO_appPath___rarg___closed__1;
lean_object* lean_io_prim_handle_get_line(lean_object*, lean_object*);
lean_object* lean_io_timeit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IO_HasEval___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_is_eof(lean_object*, lean_object*);
lean_object* l_mkEIOMonadIO(lean_object*, lean_object*);
lean_object* lean_get_set_stdout(lean_object*, lean_object*);
lean_object* l_IO_Prim_iterate___main(lean_object*, lean_object*);
lean_object* lean_chmod(lean_object*, uint32_t, lean_object*);
lean_object* l_IO_FS_Stream_ofHandle___elambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_runEval(lean_object*);
uint8_t l_UInt8_decEq(uint8_t, uint8_t);
lean_object* l_IO_Prim_getEnv___boxed(lean_object*, lean_object*);
lean_object* lean_io_wait_any(lean_object*, lean_object*);
lean_object* l_IO_bindTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_println(lean_object*);
lean_object* l_Lean_Unit_hasEval(lean_object*);
lean_object* l_IO_currentDir___rarg___closed__1;
lean_object* l_IO_Prim_getStderr___boxed(lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__12;
lean_object* l_IO_hasFinished___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofHandle___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_read___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Unit_hasEval___rarg___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_withFile___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_io_is_dir(lean_object*, lean_object*);
lean_object* l_IO_print___at_Lean_HasRepr_hasEval___spec__2(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putStr___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer___elambda__2(lean_object*, lean_object*);
lean_object* lean_io_cancel(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_putStrLn___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_waitAny___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_getEnv___rarg(lean_object*, lean_object*);
lean_object* l_IO_toEIO(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_getLine___rarg(lean_object*, lean_object*);
lean_object* l_IO_setStdin___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_mk___boxed(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_IO_FS_Handle_putStrLn___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_getStdout___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_unsafeIO___rarg(lean_object*);
lean_object* l_EIO_toIO_x27(lean_object*, lean_object*);
lean_object* lean_get_stderr(lean_object*);
uint32_t l_UInt32_shiftLeft(uint32_t, uint32_t);
lean_object* l_IO_FS_Handle_write(lean_object*, lean_object*);
lean_object* l_IO_print(lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer___elambda__5(lean_object*);
lean_object* l_IO_FS_Handle_flush___rarg(lean_object*, lean_object*);
extern lean_object* l_Unit_HasRepr___closed__1;
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_withStdin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_Handle_mk___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEnd(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_IO_withStderr___at_IO_FS_withIsolatedStreams___spec__3(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_fileExists___boxed(lean_object*, lean_object*);
uint32_t l_IO_AccessRight_flags___closed__6;
lean_object* l_IO_FS_Handle_readToEnd___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_EIO_MonadFinally(lean_object*);
lean_object* l_IO_setStderr___boxed(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Unit_hasEval___boxed(lean_object*);
lean_object* l_IO_isDir(lean_object*, lean_object*);
extern lean_object* l_EST_Monad___closed__1;
lean_object* l_IO_Prim_setStdout___boxed(lean_object*, lean_object*);
lean_object* l_EIO_Inhabited(lean_object*, lean_object*);
lean_object* l_IO_FS_withIsolatedStreams___rarg___closed__3;
lean_object* l_IO_FS_Handle_putStr___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_setStderr___boxed(lean_object*, lean_object*);
lean_object* l_IO_withStdin___at_IO_FS_withIsolatedStreams___spec__8___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__11;
lean_object* l_IO_print___at_IO_println___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_lines___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
uint32_t l_IO_AccessRight_flags___closed__13;
lean_object* l_IO_FS_Handle_getLine___at_IO_Process_output___spec__2(lean_object*, lean_object*);
lean_object* l_IO_setAccessRights(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_setStdout(lean_object*, lean_object*);
lean_object* l_IO_withStdin(lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_eprintln(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer___lambda__1(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofHandle___elambda__5(lean_object*, lean_object*);
lean_object* l_IO_Prim_Handle_isEof___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
lean_object* l_IO_FS_Stream_ofHandle___elambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_setStderr(lean_object*, lean_object*);
lean_object* l_Lean_HasRepr_hasEval___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_getLine___boxed(lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_eprint___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_withStdout___at_IO_FS_withIsolatedStreams___spec__6(lean_object*);
lean_object* l_IO_FS_Handle_readToEndAux(lean_object*);
uint32_t l_IO_AccessRight_flags___closed__8;
lean_object* l_EIO_Inhabited___rarg(lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__7;
lean_object* l_EStateM_Inhabited___rarg(lean_object*, lean_object*);
lean_object* l_Functor_discard___rarg(lean_object*, lean_object*);
lean_object* l_IO_FS_linesAux___main(lean_object*);
lean_object* l_IO_lazyPure___rarg(lean_object*, lean_object*);
lean_object* l_IO_FS_withIsolatedStreams___rarg___closed__2;
lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__1(lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_AccessRight_flags___boxed(lean_object*);
lean_object* l_EStateM_MonadFinally(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_realPath___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer___elambda__2___boxed(lean_object*, lean_object*);
lean_object* l_EStateM_catch___at_IO_FS_withIsolatedStreams___spec__2(lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* l_IO_appDir(lean_object*);
lean_object* l_IO_getStdout___at_Lean_HasRepr_hasEval___spec__3(lean_object*);
lean_object* l_EIO_toIO___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_eprintln___at___private_Init_System_IO_1__eprintlnAux___spec__1(lean_object*, lean_object*);
uint32_t l_IO_AccessRight_flags___closed__1;
uint32_t l_IO_AccessRight_flags___closed__9;
lean_object* l_IO_appPath___rarg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t l_IO_AccessRight_flags___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_dedicated;
lean_object* l_IO_FS_Stream_ofBuffer___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_get_set_stderr(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_read___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_println___at_Lean_HasRepr_hasEval___spec__1(lean_object*, lean_object*);
lean_object* l_monadIOTrans(lean_object*, lean_object*);
uint32_t l_IO_AccessRight_flags___closed__4;
lean_object* l_IO_FS_Stream_ofBuffer___elambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_getStderr___rarg___closed__1;
lean_object* lean_io_current_dir(lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__10;
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*);
lean_object* l_IO_withStderr___at_IO_FS_withIsolatedStreams___spec__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* l_IO_print___at_IO_println___spec__1(lean_object*);
lean_object* l_IO_FS_Handle_write___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_withStdin___at_IO_FS_withIsolatedStreams___spec__8(lean_object*);
lean_object* l_IO_realPath___boxed(lean_object*, lean_object*);
lean_object* l_IO_getStderr___rarg(lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
lean_object* l_System_FilePath_dirName(lean_object*);
lean_object* l_IO_getStdout___rarg(lean_object*);
lean_object* l_EIO_MonadFinally___closed__1;
lean_object* l_IO_FS_Handle_readToEndAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_catch___at_IO_FS_withIsolatedStreams___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_runEvalOld(lean_object*);
lean_object* l_IO_Prim_fopenFlags(uint8_t, uint8_t);
lean_object* l_IO_eprintln___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_IO_FS_linesAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Process_run___closed__1;
lean_object* l_IO_withStdout___at_IO_FS_withIsolatedStreams___spec__6___rarg(lean_object*, lean_object*, lean_object*);
uint32_t l_String_back(lean_object*);
lean_object* l_IO_Prim_Handle_write___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_allocprof(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_EIO_HasOrelse(lean_object*, lean_object*);
lean_object* l_Lean_runEvalOld___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_getLine(lean_object*, lean_object*);
lean_object* l_IO_eprint(lean_object*);
lean_object* l_IO_FS_Handle_readToEndAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEndAux___main___at_IO_Process_output___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_appPath___boxed(lean_object*, lean_object*);
lean_object* l_EIO_toIO_x27___rarg(lean_object*, lean_object*);
lean_object* l_monadExceptAdapter___closed__1;
lean_object* l_IO_FS_Stream_ofHandle___elambda__2___boxed(lean_object*, lean_object*);
lean_object* l_IO_initializing___boxed(lean_object*);
lean_object* lean_stream_of_handle(lean_object*);
lean_object* l_IO_Prim_iterate(lean_object*, lean_object*);
lean_object* l_IO_Prim_iterate___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* l_IO_FS_Handle_mk(lean_object*, lean_object*);
lean_object* l_EIO_toIO(lean_object*, lean_object*);
lean_object* l_IO_FS_linesAux(lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer___elambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_Handle_getLine___boxed(lean_object*, lean_object*);
lean_object* l_ByteArray_findIdxAux___main___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_mk___rarg(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_monadIOTrans___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_println___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Process_spawn___boxed(lean_object*, lean_object*);
lean_object* l_monadIOSelf___rarg(lean_object*, lean_object*);
lean_object* l_IO_getStdout___rarg___closed__1;
lean_object* l_IO_isDir___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofHandle___elambda__5___boxed(lean_object*, lean_object*);
lean_object* l_IO_getStdin___rarg(lean_object*);
lean_object* l_IO_FS_Handle_readToEndAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_fileExists___rarg(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_isEof(lean_object*, lean_object*);
lean_object* l_IO_Process_run___closed__2;
lean_object* l_IO_realPath___rarg(lean_object*, lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__6;
lean_object* l_IO_Prim_appPath___boxed(lean_object*);
lean_object* l_IO_setStdin___rarg(lean_object*, lean_object*);
lean_object* l_IO_FileRight_flags___boxed(lean_object*);
uint32_t l_IO_AccessRight_flags___closed__11;
lean_object* l_IO_setStdin___at_IO_FS_withIsolatedStreams___spec__9(lean_object*, lean_object*);
lean_object* l_IO_getStderr___at___private_Init_System_IO_1__eprintlnAux___spec__3(lean_object*);
lean_object* l_IO_FS_Handle_read(lean_object*, lean_object*);
lean_object* lean_io_has_finished(lean_object*, lean_object*);
extern lean_object* l_finally___rarg___closed__1;
lean_object* l_String_dropRight(lean_object*, lean_object*);
lean_object* l_EIO_catchExceptions(lean_object*, lean_object*);
lean_object* l_IO_setAccessRights___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_IO_setStderr___at_IO_FS_withIsolatedStreams___spec__4(lean_object*, lean_object*);
lean_object* l_IO_print___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_setStdout___rarg(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofHandle___elambda__2(lean_object*, lean_object*);
lean_object* l_IO_Process_run(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer___elambda__6(lean_object*, lean_object*);
lean_object* l_IO_ofExcept___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_fileExists___boxed(lean_object*, lean_object*);
lean_object* l_IO_print___at_IO_println___spec__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_EST_MonadExceptOf___closed__2;
lean_object* l_IO_FS_readFile___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_realPath(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_withIsolatedStreams___rarg___closed__1;
lean_object* l_EIO_HasOrelse___closed__1;
lean_object* l_IO_FS_Stream_ofBuffer___elambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept(lean_object*, lean_object*);
lean_object* lean_io_file_exists(lean_object*, lean_object*);
lean_object* l_Lean_IO_HasEval(lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* lean_io_check_canceled(lean_object*);
lean_object* l_IO_FS_Stream_ofHandle___elambda__4(lean_object*, size_t, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer___elambda__4(lean_object*, size_t, lean_object*);
lean_object* l_IO_currentDir(lean_object*, lean_object*);
lean_object* l_IO_Prim_isDir___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putStr(lean_object*, lean_object*);
lean_object* l_IO_Prim_setAccessRights___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_isDir___rarg(lean_object*, lean_object*);
lean_object* l_IO_getStdin___boxed(lean_object*, lean_object*);
lean_object* l_IO_getEnv(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEndAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofHandle___elambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_dbgTraceVal___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_IO_eprint___at_IO_eprintln___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_IO_lazyPure(lean_object*);
lean_object* l_IO_setStderr___rarg(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_mk___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_wait___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_MonadExcept_orelse___at_EIO_HasOrelse___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer___elambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_currentDir___boxed(lean_object*);
lean_object* l_IO_FS_Handle_write___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__5;
lean_object* lean_get_stdout(lean_object*);
lean_object* l_IO_FS_Stream_ofHandle___elambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__14;
lean_object* l_IO_ofExcept___at_IO_Process_output___spec__3(lean_object*, lean_object*);
lean_object* l_IO_withStderr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEndAux___main(lean_object*);
lean_object* l_EIO_MonadExceptOf(lean_object*);
lean_object* l_IO_FS_readFile___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_st2eio(lean_object*, lean_object*);
lean_object* l_IO_eprint___at___private_Init_System_IO_1__eprintlnAux___spec__2(lean_object*, lean_object*);
uint32_t l_IO_AccessRight_flags(lean_object*);
lean_object* l_unsafeIO(lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__3;
lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__2(lean_object*, lean_object*);
lean_object* l_IO_getEnv___boxed(lean_object*, lean_object*);
lean_object* l_IO_withStdin___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_checkCanceled___boxed(lean_object*);
lean_object* l_monadIOSelf(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_toEIO___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_IO_FS_lines___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_withIsolatedStreams(lean_object*);
lean_object* lean_get_set_stdin(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_getLine___at_IO_Process_output___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_IO_eprint___at_IO_eprintln___spec__1(lean_object*);
lean_object* l_IO_appDir___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_read___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_monadExceptAdapter(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_IO_AccessRight_flags___closed__10;
lean_object* l_IO_asTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Unit_hasEval___rarg(uint8_t, lean_object*);
lean_object* lean_io_prim_handle_flush(lean_object*, lean_object*);
uint32_t l_UInt32_lor(uint32_t, uint32_t);
lean_object* l_IO_Prim_fopenFlags___closed__4;
lean_object* l_IO_appPath(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEndAux___main___at_IO_Process_output___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
lean_object* l_IO_FS_Stream_ofHandle___elambda__6___boxed(lean_object*, lean_object*);
lean_object* l_monadExceptAdapter(lean_object*, lean_object*);
lean_object* l_IO_withStderr(lean_object*);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__9;
lean_object* lean_string_length(lean_object*);
lean_object* l_IO_mkRef(lean_object*, lean_object*, lean_object*);
uint8_t lean_byte_array_get(lean_object*, lean_object*);
lean_object* l_MonadExcept_orelse___at_EIO_HasOrelse___spec__1(lean_object*, lean_object*);
lean_object* l_IO_getStderr(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_isEof___boxed(lean_object*, lean_object*);
lean_object* l_EIO_Monad(lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__8;
lean_object* l_IO_Prim_Handle_putStr___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_withStdout(lean_object*);
lean_object* l_Lean_IO_HasEval___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_mkEIOMonadIO___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_timeit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_app_dir(lean_object*);
lean_object* l_IO_FS_Handle_isEof___rarg(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_flush(lean_object*, lean_object*);
uint32_t l_IO_AccessRight_flags___closed__12;
lean_object* l_IO_currentDir___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_fopenFlags___boxed(lean_object*, lean_object*);
lean_object* l_IO_mkRef___rarg(lean_object*, lean_object*);
lean_object* l_IO_getStdin(lean_object*, lean_object*);
lean_object* l_IO_mapTask___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofHandle___elambda__6(lean_object*, lean_object*);
lean_object* l_Lean_HasRepr_hasEval___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__1;
lean_object* l_IO_getStderr___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_withFile___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_read(lean_object*, size_t, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_IO_FS_lines(lean_object*);
lean_object* l_Functor_discard___at_IO_FS_withIsolatedStreams___spec__5(lean_object*, lean_object*);
lean_object* l_IO_fileExists(lean_object*, lean_object*);
lean_object* l_IO_getStdout___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_flush___boxed(lean_object*, lean_object*);
lean_object* l_Lean_runEval___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_withStderr___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_print___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__2;
lean_object* lean_io_eprintln(lean_object*, lean_object*);
lean_object* l_IO_withStdout___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint32_t l_IO_AccessRight_flags___closed__5;
lean_object* l_IO_withStdout___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer___closed__1;
lean_object* l_IO_appDir___rarg(lean_object*, lean_object*);
lean_object* l_IO_currentDir___rarg(lean_object*);
lean_object* l_IO_setStdout___at_IO_FS_withIsolatedStreams___spec__7(lean_object*, lean_object*);
lean_object* l_IO_Prim_iterate___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
uint32_t l_IO_AccessRight_flags___closed__7;
uint32_t l_IO_FileRight_flags(lean_object*);
lean_object* l_IO_Process_Child_wait___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_setStdin(lean_object*, lean_object*);
lean_object* l_EIO_catchExceptions___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_setStdin___boxed(lean_object*, lean_object*);
lean_object* l_IO_st2eio___rarg(lean_object*, lean_object*);
lean_object* l_IO_Prim_Handle_read___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Prim_fopenFlags___closed__13;
uint32_t l_IO_AccessRight_flags___closed__3;
lean_object* l_IO_FS_withFile(lean_object*);
lean_object* l_IO_FS_Stream_putStrLn___boxed(lean_object*, lean_object*);
lean_object* l_IO_Prim_getStdin___boxed(lean_object*);
lean_object* l_IO_Prim_Handle_flush___boxed(lean_object*, lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
lean_object* l_Lean_HasRepr_hasEval(lean_object*);
lean_object* l_IO_mkRef___at_IO_FS_withIsolatedStreams___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_IO_setStdout___boxed(lean_object*, lean_object*);
static lean_object* _init_l_monadExceptAdapter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_monadExceptAdapter), 4, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
lean_object* l_monadExceptAdapter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_monadExceptAdapter___closed__1;
return x_3;
}
}
lean_object* l_EIO_catchExceptions___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_apply_2(x_2, x_9, x_10);
return x_11;
}
}
}
lean_object* l_EIO_catchExceptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EIO_catchExceptions___rarg), 3, 0);
return x_3;
}
}
lean_object* l_EIO_Monad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_EST_Monad___closed__1;
return x_2;
}
}
static lean_object* _init_l_EIO_MonadFinally___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_MonadFinally), 4, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
lean_object* l_EIO_MonadFinally(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_EIO_MonadFinally___closed__1;
return x_2;
}
}
lean_object* l_EIO_MonadExceptOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_EST_MonadExceptOf___closed__2;
return x_2;
}
}
lean_object* l_MonadExcept_orelse___at_EIO_HasOrelse___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_MonadExcept_orelse___at_EIO_HasOrelse___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_MonadExcept_orelse___at_EIO_HasOrelse___spec__1___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_EIO_HasOrelse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_MonadExcept_orelse___at_EIO_HasOrelse___spec__1___rarg), 3, 0);
return x_1;
}
}
lean_object* l_EIO_HasOrelse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_EIO_HasOrelse___closed__1;
return x_3;
}
}
lean_object* l_EIO_Inhabited___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_EStateM_Inhabited___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_EIO_Inhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EIO_Inhabited___rarg), 1, 0);
return x_3;
}
}
lean_object* l_EIO_toIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_apply_1(x_1, x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_apply_1(x_1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
lean_object* l_EIO_toIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EIO_toIO___rarg), 3, 0);
return x_3;
}
}
lean_object* l_EIO_toIO_x27___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
lean_object* l_EIO_toIO_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_EIO_toIO_x27___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_toEIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_apply_1(x_1, x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_apply_1(x_1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
lean_object* l_IO_toEIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_toEIO___rarg), 3, 0);
return x_3;
}
}
lean_object* l_unsafeIO___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
lean_object* l_unsafeIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_unsafeIO___rarg), 1, 0);
return x_2;
}
}
lean_object* l_timeit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_timeit(x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_allocprof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_allocprof(x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_IO_initializing___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_initializing(x_1);
return x_2;
}
}
lean_object* l_monadIOTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_monadIOTrans(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_monadIOTrans___rarg), 4, 0);
return x_3;
}
}
lean_object* l_monadIOSelf___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_monadIOSelf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_monadIOSelf___rarg), 2, 0);
return x_2;
}
}
lean_object* l_mkEIOMonadIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_1, lean_box(0), x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_2);
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
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_apply_1(x_2, x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_apply_1(x_2, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
lean_object* l_mkEIOMonadIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_mkEIOMonadIO___rarg), 5, 0);
return x_3;
}
}
lean_object* l_IO_ofExcept___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
lean_object* l_IO_ofExcept(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_ofExcept___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_lazyPure___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l_IO_lazyPure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_lazyPure___rarg), 2, 0);
return x_2;
}
}
lean_object* l_IO_asTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_io_as_task(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_IO_mapTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_io_map_task(x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_IO_bindTask___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_io_bind_task(x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_IO_checkCanceled___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_check_canceled(x_1);
return x_2;
}
}
lean_object* l_IO_cancel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_cancel(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_IO_hasFinished___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_has_finished(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_IO_wait___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_wait(x_2, x_3);
return x_4;
}
}
lean_object* l_IO_waitAny___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_wait_any(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_IO_Prim_getStdin___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stdin(x_1);
return x_2;
}
}
lean_object* l_IO_Prim_getStdout___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stdout(x_1);
return x_2;
}
}
lean_object* l_IO_Prim_getStderr___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stderr(x_1);
return x_2;
}
}
lean_object* l_IO_Prim_setStdin___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_set_stdin(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_Prim_setStdout___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_set_stdout(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_Prim_setStderr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_set_stderr(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_Prim_iterate___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = lean_apply_2(x_2, x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_1 = x_7;
x_3 = x_6;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_IO_Prim_iterate___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_iterate___main___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_Prim_iterate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_Prim_iterate___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_IO_Prim_iterate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_iterate___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_IO_Prim_fopenFlags___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("r");
return x_1;
}
}
static lean_object* _init_l_IO_Prim_fopenFlags___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("t");
return x_1;
}
}
static lean_object* _init_l_IO_Prim_fopenFlags___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_Prim_fopenFlags___closed__1;
x_2 = l_IO_Prim_fopenFlags___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_Prim_fopenFlags___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("b");
return x_1;
}
}
static lean_object* _init_l_IO_Prim_fopenFlags___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_Prim_fopenFlags___closed__1;
x_2 = l_IO_Prim_fopenFlags___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_Prim_fopenFlags___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("w");
return x_1;
}
}
static lean_object* _init_l_IO_Prim_fopenFlags___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_Prim_fopenFlags___closed__6;
x_2 = l_IO_Prim_fopenFlags___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_Prim_fopenFlags___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_Prim_fopenFlags___closed__6;
x_2 = l_IO_Prim_fopenFlags___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_Prim_fopenFlags___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("r+");
return x_1;
}
}
static lean_object* _init_l_IO_Prim_fopenFlags___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_Prim_fopenFlags___closed__9;
x_2 = l_IO_Prim_fopenFlags___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_Prim_fopenFlags___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_Prim_fopenFlags___closed__9;
x_2 = l_IO_Prim_fopenFlags___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_Prim_fopenFlags___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a");
return x_1;
}
}
static lean_object* _init_l_IO_Prim_fopenFlags___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_Prim_fopenFlags___closed__12;
x_2 = l_IO_Prim_fopenFlags___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_Prim_fopenFlags___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_IO_Prim_fopenFlags___closed__12;
x_2 = l_IO_Prim_fopenFlags___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_Prim_fopenFlags(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_IO_Prim_fopenFlags___closed__3;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_IO_Prim_fopenFlags___closed__5;
return x_4;
}
}
case 1:
{
if (x_2 == 0)
{
lean_object* x_5; 
x_5 = l_IO_Prim_fopenFlags___closed__7;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_IO_Prim_fopenFlags___closed__8;
return x_6;
}
}
case 2:
{
if (x_2 == 0)
{
lean_object* x_7; 
x_7 = l_IO_Prim_fopenFlags___closed__10;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_IO_Prim_fopenFlags___closed__11;
return x_8;
}
}
default: 
{
if (x_2 == 0)
{
lean_object* x_9; 
x_9 = l_IO_Prim_fopenFlags___closed__13;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_IO_Prim_fopenFlags___closed__14;
return x_10;
}
}
}
}
}
lean_object* l_IO_Prim_fopenFlags___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_IO_Prim_fopenFlags(x_3, x_4);
return x_5;
}
}
lean_object* l_IO_Prim_Handle_mk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_mk(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_Prim_Handle_isEof___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_is_eof(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_Handle_flush___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_flush(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_Handle_read___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_io_prim_handle_read(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_IO_Prim_Handle_write___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_write(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_Prim_Handle_getLine___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_get_line(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_Handle_putStr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_put_str(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_Prim_getEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_getenv(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_realPath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_realpath(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_Prim_isDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_is_dir(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_fileExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_file_exists(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_Prim_appPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_app_dir(x_1);
return x_2;
}
}
lean_object* l_IO_Prim_currentDir___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_current_dir(x_1);
return x_2;
}
}
lean_object* l_IO_FS_Handle_mk___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_IO_Prim_fopenFlags(x_3, x_4);
x_6 = lean_alloc_closure((void*)(l_IO_Prim_Handle_mk___boxed), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_IO_FS_Handle_mk(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_mk___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_mk___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_IO_FS_Handle_mk___rarg(x_1, x_2, x_5, x_6);
return x_7;
}
}
lean_object* l_IO_FS_Handle_mk___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_mk(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_withFile___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = 1;
x_9 = l_IO_FS_Handle_mk___rarg(x_2, x_4, x_5, x_8);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_6);
return x_10;
}
}
lean_object* l_IO_FS_withFile(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_withFile___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_IO_FS_withFile___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_IO_FS_withFile___rarg(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
lean_object* l_IO_FS_Handle_isEof___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_Handle_isEof___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_FS_Handle_isEof(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_isEof___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_isEof___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_isEof(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_flush___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_Handle_flush___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_FS_Handle_flush(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_flush___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_flush___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_flush(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_read___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_usize_of_nat(x_3);
x_5 = lean_box_usize(x_4);
x_6 = lean_alloc_closure((void*)(l_IO_Prim_Handle_read___boxed), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_IO_FS_Handle_read(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_read___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_read___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Handle_read___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_IO_FS_Handle_read___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_read(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_write___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_IO_Prim_Handle_write___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_IO_FS_Handle_write(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_write___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_write___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_write(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_getLine___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_Handle_getLine___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_FS_Handle_getLine(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_getLine___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_getLine___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_getLine(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_putStr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_IO_Prim_Handle_putStr___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_IO_FS_Handle_putStr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_putStr___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_putStr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_putStr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_putStrLn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 10;
x_5 = lean_string_push(x_3, x_4);
x_6 = l_IO_FS_Handle_putStr___rarg(x_1, x_2, x_5);
return x_6;
}
}
lean_object* l_IO_FS_Handle_putStrLn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Handle_putStrLn___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_FS_Handle_putStrLn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_putStrLn(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_readToEndAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_string_length(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_string_append(x_1, x_5);
x_10 = l_IO_FS_Handle_readToEndAux___main___rarg(x_2, x_3, x_4, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_12, lean_box(0), x_1);
return x_13;
}
}
}
lean_object* l_IO_FS_Handle_readToEndAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_IO_FS_Handle_getLine___rarg(x_2, x_3);
x_7 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEndAux___main___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_IO_FS_Handle_readToEndAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEndAux___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_Handle_readToEndAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Handle_readToEndAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_IO_FS_Handle_readToEndAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Handle_readToEndAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_IO_FS_Handle_readToEndAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEndAux___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_Handle_readToEnd___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_String_splitAux___main___closed__1;
x_5 = l_IO_FS_Handle_readToEndAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_IO_FS_Handle_readToEnd(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEnd___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_FS_readFile___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_String_splitAux___main___closed__1;
x_5 = l_IO_FS_Handle_readToEndAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_IO_FS_readFile___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = 0;
x_6 = 0;
lean_inc(x_2);
x_7 = l_IO_FS_Handle_mk___rarg(x_2, x_3, x_5, x_6);
x_8 = lean_alloc_closure((void*)(l_IO_FS_readFile___rarg___lambda__1), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_IO_FS_readFile(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_readFile___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_FS_linesAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_string_length(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; uint8_t x_30; 
x_9 = l_String_back(x_5);
x_10 = 10;
x_30 = x_9 == x_10;
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = 0;
x_11 = x_31;
goto block_29;
}
else
{
uint8_t x_32; 
x_32 = 1;
x_11 = x_32;
goto block_29;
}
block_29:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_array_push(x_2, x_5);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_String_dropRight(x_5, x_16);
x_18 = l_System_Platform_isWindows;
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_push(x_2, x_17);
x_20 = l_IO_FS_linesAux___main___rarg(x_1, x_3, x_4, x_19);
return x_20;
}
else
{
uint32_t x_21; uint32_t x_22; uint8_t x_23; 
x_21 = l_String_back(x_17);
x_22 = 13;
x_23 = x_21 == x_22;
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_array_push(x_2, x_17);
x_25 = l_IO_FS_linesAux___main___rarg(x_1, x_3, x_4, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = l_String_dropRight(x_17, x_16);
x_27 = lean_array_push(x_2, x_26);
x_28 = l_IO_FS_linesAux___main___rarg(x_1, x_3, x_4, x_27);
return x_28;
}
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_apply_2(x_34, lean_box(0), x_2);
return x_35;
}
}
}
lean_object* l_IO_FS_linesAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_IO_FS_Handle_getLine___rarg(x_2, x_3);
x_7 = lean_alloc_closure((void*)(l_IO_FS_linesAux___main___rarg___lambda__1), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_IO_FS_linesAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_linesAux___main___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_linesAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_linesAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_IO_FS_linesAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_linesAux___rarg), 4, 0);
return x_2;
}
}
lean_object* l_IO_FS_lines___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Array_empty___closed__1;
x_5 = l_IO_FS_linesAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_IO_FS_lines___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = 0;
x_6 = 0;
lean_inc(x_2);
x_7 = l_IO_FS_Handle_mk___rarg(x_2, x_3, x_5, x_6);
x_8 = lean_alloc_closure((void*)(l_IO_FS_lines___rarg___lambda__1), 3, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_IO_FS_lines(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_lines___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_FS_Stream_putStrLn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 5);
lean_inc(x_4);
lean_dec(x_2);
x_5 = 10;
x_6 = lean_string_push(x_3, x_5);
x_7 = lean_apply_1(x_4, x_6);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_IO_FS_Stream_putStrLn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_FS_Stream_putStrLn___rarg), 3, 0);
return x_3;
}
}
lean_object* l_IO_FS_Stream_putStrLn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_putStrLn(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_IO_getStdin___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_Prim_getStdin___boxed), 1, 0);
return x_1;
}
}
lean_object* l_IO_getStdin___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_getStdin___rarg___closed__1;
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_IO_getStdin(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_getStdin___rarg), 1, 0);
return x_3;
}
}
lean_object* l_IO_getStdin___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_getStdin(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_IO_getStdout___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_Prim_getStdout___boxed), 1, 0);
return x_1;
}
}
lean_object* l_IO_getStdout___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_getStdout___rarg___closed__1;
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_IO_getStdout(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_getStdout___rarg), 1, 0);
return x_3;
}
}
lean_object* l_IO_getStdout___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_getStdout(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_IO_getStderr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_Prim_getStderr___boxed), 1, 0);
return x_1;
}
}
lean_object* l_IO_getStderr___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_getStderr___rarg___closed__1;
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_IO_getStderr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_getStderr___rarg), 1, 0);
return x_3;
}
}
lean_object* l_IO_getStderr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_getStderr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_setStdin___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_setStdin___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_setStdin(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_setStdin___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_setStdin___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_setStdin(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_setStdout___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_setStdout___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_setStdout(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_setStdout___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_setStdout___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_setStdout(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_setStderr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_setStderr___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_setStderr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_setStderr___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_setStderr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_setStderr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_withStdin___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_IO_setStdin___rarg(x_2, x_5);
lean_inc(x_7);
x_9 = l_Functor_discard___rarg(x_7, x_8);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_closure((void*)(l_dbgTraceVal___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_11);
x_13 = l_finally___rarg___closed__1;
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_12);
return x_14;
}
}
lean_object* l_IO_withStdin___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_2);
x_8 = l_IO_setStdin___rarg(x_2, x_5);
x_9 = lean_alloc_closure((void*)(l_IO_withStdin___rarg___lambda__1), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_6);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_IO_withStdin(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___rarg), 6, 0);
return x_2;
}
}
lean_object* l_IO_withStdout___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_IO_setStdout___rarg(x_2, x_5);
lean_inc(x_7);
x_9 = l_Functor_discard___rarg(x_7, x_8);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_closure((void*)(l_dbgTraceVal___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_11);
x_13 = l_finally___rarg___closed__1;
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_12);
return x_14;
}
}
lean_object* l_IO_withStdout___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_2);
x_8 = l_IO_setStdout___rarg(x_2, x_5);
x_9 = lean_alloc_closure((void*)(l_IO_withStdout___rarg___lambda__1), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_6);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_IO_withStdout(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___rarg), 6, 0);
return x_2;
}
}
lean_object* l_IO_withStderr___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_IO_setStderr___rarg(x_2, x_5);
lean_inc(x_7);
x_9 = l_Functor_discard___rarg(x_7, x_8);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_alloc_closure((void*)(l_dbgTraceVal___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_11);
x_13 = l_finally___rarg___closed__1;
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_12);
return x_14;
}
}
lean_object* l_IO_withStderr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_2);
x_8 = l_IO_setStderr___rarg(x_2, x_5);
x_9 = lean_alloc_closure((void*)(l_IO_withStderr___rarg___lambda__1), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_6);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_IO_withStderr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStderr___rarg), 6, 0);
return x_2;
}
}
lean_object* l_IO_print___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 5);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_1(x_1, x_2);
x_7 = lean_apply_1(x_5, x_6);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
return x_8;
}
}
lean_object* l_IO_print___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_IO_getStdout___rarg___closed__1;
lean_inc(x_2);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_IO_print___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_2);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_IO_print(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_print___rarg), 5, 0);
return x_2;
}
}
lean_object* l_IO_print___at_IO_println___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 5);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_4, x_1);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_IO_print___at_IO_println___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_IO_getStdout___rarg___closed__1;
lean_inc(x_2);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
x_7 = lean_alloc_closure((void*)(l_IO_print___at_IO_println___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_IO_print___at_IO_println___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_print___at_IO_println___spec__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_println___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_apply_1(x_4, x_5);
x_7 = 10;
x_8 = lean_string_push(x_6, x_7);
x_9 = l_IO_print___at_IO_println___spec__1___rarg(x_1, x_2, x_8);
return x_9;
}
}
lean_object* l_IO_println(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_println___rarg), 5, 0);
return x_2;
}
}
lean_object* l_IO_eprint___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_IO_getStderr___rarg___closed__1;
lean_inc(x_2);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_IO_print___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_2);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_IO_eprint(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_eprint___rarg), 5, 0);
return x_2;
}
}
lean_object* l_IO_eprint___at_IO_eprintln___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_IO_getStderr___rarg___closed__1;
lean_inc(x_2);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
x_7 = lean_alloc_closure((void*)(l_IO_print___at_IO_println___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_IO_eprint___at_IO_eprintln___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_eprint___at_IO_eprintln___spec__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_eprintln___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_apply_1(x_4, x_5);
x_7 = 10;
x_8 = lean_string_push(x_6, x_7);
x_9 = l_IO_eprint___at_IO_eprintln___spec__1___rarg(x_1, x_2, x_8);
return x_9;
}
}
lean_object* l_IO_eprintln(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_eprintln___rarg), 5, 0);
return x_2;
}
}
lean_object* l_IO_getStderr___at___private_Init_System_IO_1__eprintlnAux___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stderr(x_1);
return x_2;
}
}
lean_object* l_IO_eprint___at___private_Init_System_IO_1__eprintlnAux___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_stderr(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 5);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_6, x_1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* l_IO_eprintln___at___private_Init_System_IO_1__eprintlnAux___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_eprint___at___private_Init_System_IO_1__eprintlnAux___spec__2(x_4, x_2);
return x_5;
}
}
lean_object* lean_io_eprintln(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprintln___at___private_Init_System_IO_1__eprintlnAux___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_getEnv___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_getEnv___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_getEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_getEnv___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_getEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_getEnv(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_realPath___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_realPath___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_realPath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_realPath___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_realPath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_realPath(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_isDir___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_isDir___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_isDir(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_isDir___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_isDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_isDir(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_fileExists___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_IO_Prim_fileExists___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_fileExists(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_fileExists___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_fileExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_fileExists(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_IO_appPath___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_Prim_appPath___boxed), 1, 0);
return x_1;
}
}
lean_object* l_IO_appPath___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_appPath___rarg___closed__1;
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_IO_appPath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_appPath___rarg), 1, 0);
return x_3;
}
}
lean_object* l_IO_appPath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_appPath(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_appDir___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_System_FilePath_dirName(x_2);
x_4 = l_IO_realPath___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l_IO_appDir___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_IO_appPath___rarg___closed__1;
lean_inc(x_2);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
x_6 = lean_alloc_closure((void*)(l_IO_appDir___rarg___lambda__1), 2, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_IO_appDir(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_appDir___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_IO_currentDir___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_Prim_currentDir___boxed), 1, 0);
return x_1;
}
}
lean_object* l_IO_currentDir___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_currentDir___rarg___closed__1;
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
lean_object* l_IO_currentDir(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_currentDir___rarg), 1, 0);
return x_3;
}
}
lean_object* l_IO_currentDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_currentDir(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_IO_Process_spawn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_process_spawn(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_Process_Child_wait___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_process_child_wait(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_FS_Handle_getLine___at_IO_Process_output___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_get_line(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_FS_Handle_readToEndAux___main___at_IO_Process_output___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_get_line(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_string_length(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_4);
x_11 = lean_string_append(x_2, x_6);
lean_dec(x_6);
x_2 = x_11;
x_3 = x_7;
goto _start;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_string_length(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_string_append(x_2, x_13);
lean_dec(x_13);
x_2 = x_18;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_20; 
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
return x_4;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_IO_ofExcept___at_IO_Process_output___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_io_error_to_string(x_3);
x_5 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
}
lean_object* l_IO_Process_output(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
lean_ctor_set_uint8(x_4, 1, x_6);
lean_ctor_set_uint8(x_4, 2, x_6);
lean_inc(x_4);
x_7 = lean_io_process_spawn(x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = l_String_splitAux___main___closed__1;
x_12 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEndAux___main___at_IO_Process_output___spec__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Task_Priority_dedicated;
x_14 = lean_io_as_task(x_12, x_13, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_8, 2);
lean_inc(x_17);
x_18 = l_IO_FS_Handle_readToEndAux___main___at_IO_Process_output___spec__1(x_17, x_11, x_16);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_io_process_child_wait(x_4, x_8, x_20);
lean_dec(x_8);
lean_dec(x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_task_get_own(x_15);
x_25 = l_IO_ofExcept___at_IO_Process_output___spec__3(x_24, x_23);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint32_t x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_19);
x_29 = lean_unbox_uint32(x_22);
lean_dec(x_22);
lean_ctor_set_uint32(x_28, sizeof(void*)*2, x_29);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint32_t x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_19);
x_33 = lean_unbox_uint32(x_22);
lean_dec(x_22);
lean_ctor_set_uint32(x_32, sizeof(void*)*2, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_22);
lean_dec(x_19);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_15);
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
return x_21;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
return x_18;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_18, 0);
x_45 = lean_ctor_get(x_18, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_18);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_8);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_14);
if (x_47 == 0)
{
return x_14;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_14, 0);
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_14);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_7);
if (x_51 == 0)
{
return x_7;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_7, 0);
x_53 = lean_ctor_get(x_7, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_7);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get_uint8(x_4, 0);
lean_dec(x_4);
x_56 = 0;
x_57 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, 2, x_56);
lean_inc(x_57);
lean_ctor_set(x_1, 0, x_57);
x_58 = lean_io_process_spawn(x_1, x_2);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
x_62 = l_String_splitAux___main___closed__1;
x_63 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEndAux___main___at_IO_Process_output___spec__1___boxed), 3, 2);
lean_closure_set(x_63, 0, x_61);
lean_closure_set(x_63, 1, x_62);
x_64 = l_Task_Priority_dedicated;
x_65 = lean_io_as_task(x_63, x_64, x_60);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_59, 2);
lean_inc(x_68);
x_69 = l_IO_FS_Handle_readToEndAux___main___at_IO_Process_output___spec__1(x_68, x_62, x_67);
lean_dec(x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_io_process_child_wait(x_57, x_59, x_71);
lean_dec(x_59);
lean_dec(x_57);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_task_get_own(x_66);
x_76 = l_IO_ofExcept___at_IO_Process_output___spec__3(x_75, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint32_t x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_70);
x_81 = lean_unbox_uint32(x_73);
lean_dec(x_73);
lean_ctor_set_uint32(x_80, sizeof(void*)*2, x_81);
if (lean_is_scalar(x_79)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_79;
}
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_78);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_73);
lean_dec(x_70);
x_83 = lean_ctor_get(x_76, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_76, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_85 = x_76;
} else {
 lean_dec_ref(x_76);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_70);
lean_dec(x_66);
x_87 = lean_ctor_get(x_72, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_72, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_89 = x_72;
} else {
 lean_dec_ref(x_72);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_66);
lean_dec(x_59);
lean_dec(x_57);
x_91 = lean_ctor_get(x_69, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_69, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_93 = x_69;
} else {
 lean_dec_ref(x_69);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_59);
lean_dec(x_57);
x_95 = lean_ctor_get(x_65, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_65, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_97 = x_65;
} else {
 lean_dec_ref(x_65);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_57);
x_99 = lean_ctor_get(x_58, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_58, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_101 = x_58;
} else {
 lean_dec_ref(x_58);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_103 = lean_ctor_get(x_1, 0);
x_104 = lean_ctor_get(x_1, 1);
x_105 = lean_ctor_get(x_1, 2);
x_106 = lean_ctor_get(x_1, 3);
x_107 = lean_ctor_get(x_1, 4);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_1);
x_108 = lean_ctor_get_uint8(x_103, 0);
if (lean_is_exclusive(x_103)) {
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
x_110 = 0;
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 0, 3);
} else {
 x_111 = x_109;
}
lean_ctor_set_uint8(x_111, 0, x_108);
lean_ctor_set_uint8(x_111, 1, x_110);
lean_ctor_set_uint8(x_111, 2, x_110);
lean_inc(x_111);
x_112 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_104);
lean_ctor_set(x_112, 2, x_105);
lean_ctor_set(x_112, 3, x_106);
lean_ctor_set(x_112, 4, x_107);
x_113 = lean_io_process_spawn(x_112, x_2);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
x_117 = l_String_splitAux___main___closed__1;
x_118 = lean_alloc_closure((void*)(l_IO_FS_Handle_readToEndAux___main___at_IO_Process_output___spec__1___boxed), 3, 2);
lean_closure_set(x_118, 0, x_116);
lean_closure_set(x_118, 1, x_117);
x_119 = l_Task_Priority_dedicated;
x_120 = lean_io_as_task(x_118, x_119, x_115);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_ctor_get(x_114, 2);
lean_inc(x_123);
x_124 = l_IO_FS_Handle_readToEndAux___main___at_IO_Process_output___spec__1(x_123, x_117, x_122);
lean_dec(x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_io_process_child_wait(x_111, x_114, x_126);
lean_dec(x_114);
lean_dec(x_111);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_task_get_own(x_121);
x_131 = l_IO_ofExcept___at_IO_Process_output___spec__3(x_130, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint32_t x_136; lean_object* x_137; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
x_135 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_125);
x_136 = lean_unbox_uint32(x_128);
lean_dec(x_128);
lean_ctor_set_uint32(x_135, sizeof(void*)*2, x_136);
if (lean_is_scalar(x_134)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_134;
}
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_133);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_128);
lean_dec(x_125);
x_138 = lean_ctor_get(x_131, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_131, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_140 = x_131;
} else {
 lean_dec_ref(x_131);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_125);
lean_dec(x_121);
x_142 = lean_ctor_get(x_127, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_127, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_144 = x_127;
} else {
 lean_dec_ref(x_127);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_121);
lean_dec(x_114);
lean_dec(x_111);
x_146 = lean_ctor_get(x_124, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_124, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_148 = x_124;
} else {
 lean_dec_ref(x_124);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_114);
lean_dec(x_111);
x_150 = lean_ctor_get(x_120, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_120, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_152 = x_120;
} else {
 lean_dec_ref(x_120);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_111);
x_154 = lean_ctor_get(x_113, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_113, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_156 = x_113;
} else {
 lean_dec_ref(x_113);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
}
lean_object* l_IO_FS_Handle_getLine___at_IO_Process_output___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Handle_getLine___at_IO_Process_output___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_FS_Handle_readToEndAux___main___at_IO_Process_output___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Handle_readToEndAux___main___at_IO_Process_output___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_IO_Process_run___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("process '");
return x_1;
}
}
static lean_object* _init_l_IO_Process_run___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' exited with code ");
return x_1;
}
}
lean_object* l_IO_Process_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_IO_Process_output(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get_uint32(x_5, sizeof(void*)*2);
x_7 = 0;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_IO_Process_run___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l_IO_Process_run___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_uint32_to_nat(x_6);
x_15 = l_Nat_repr(x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
else
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_18);
return x_3;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint32_t x_21; uint32_t x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_21 = lean_ctor_get_uint32(x_19, sizeof(void*)*2);
x_22 = 0;
x_23 = x_21 == x_22;
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_19);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_IO_Process_run___closed__1;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_IO_Process_run___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_uint32_to_nat(x_21);
x_30 = l_Nat_repr(x_29);
x_31 = lean_string_append(x_28, x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_20);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_20);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_3);
if (x_36 == 0)
{
return x_3;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_3, 0);
x_38 = lean_ctor_get(x_3, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_3);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__1() {
_start:
{
uint32_t x_1; uint32_t x_2; 
x_1 = 0;
x_2 = x_1 | x_1;
return x_2;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__2() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = l_IO_AccessRight_flags___closed__1;
x_3 = x_1 | x_2;
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__3() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = 1;
x_3 = x_1 | x_2;
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__4() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = l_IO_AccessRight_flags___closed__3;
x_3 = x_1 | x_2;
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__5() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = 2;
x_3 = x_2 | x_1;
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__6() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = l_IO_AccessRight_flags___closed__5;
x_3 = x_1 | x_2;
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__7() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 2;
x_2 = 1;
x_3 = x_1 | x_2;
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__8() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 0;
x_2 = l_IO_AccessRight_flags___closed__7;
x_3 = x_1 | x_2;
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__9() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 4;
x_2 = l_IO_AccessRight_flags___closed__1;
x_3 = x_1 | x_2;
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__10() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 4;
x_2 = l_IO_AccessRight_flags___closed__3;
x_3 = x_1 | x_2;
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__11() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 2;
x_2 = 0;
x_3 = x_1 | x_2;
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__12() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 4;
x_2 = l_IO_AccessRight_flags___closed__11;
x_3 = x_1 | x_2;
return x_3;
}
}
static uint32_t _init_l_IO_AccessRight_flags___closed__13() {
_start:
{
uint32_t x_1; uint32_t x_2; uint32_t x_3; 
x_1 = 4;
x_2 = l_IO_AccessRight_flags___closed__7;
x_3 = x_1 | x_2;
return x_3;
}
}
uint32_t l_IO_AccessRight_flags(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, 0);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, 1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, 2);
if (x_4 == 0)
{
uint32_t x_5; 
x_5 = l_IO_AccessRight_flags___closed__2;
return x_5;
}
else
{
uint32_t x_6; 
x_6 = l_IO_AccessRight_flags___closed__4;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, 2);
if (x_7 == 0)
{
uint32_t x_8; 
x_8 = l_IO_AccessRight_flags___closed__6;
return x_8;
}
else
{
uint32_t x_9; 
x_9 = l_IO_AccessRight_flags___closed__8;
return x_9;
}
}
}
else
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_1, 1);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_1, 2);
if (x_11 == 0)
{
uint32_t x_12; 
x_12 = l_IO_AccessRight_flags___closed__9;
return x_12;
}
else
{
uint32_t x_13; 
x_13 = l_IO_AccessRight_flags___closed__10;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_1, 2);
if (x_14 == 0)
{
uint32_t x_15; 
x_15 = l_IO_AccessRight_flags___closed__12;
return x_15;
}
else
{
uint32_t x_16; 
x_16 = l_IO_AccessRight_flags___closed__13;
return x_16;
}
}
}
}
}
lean_object* l_IO_AccessRight_flags___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_IO_AccessRight_flags(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
uint32_t l_IO_FileRight_flags(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint32_t x_4; uint32_t x_5; uint32_t x_6; lean_object* x_7; uint32_t x_8; uint32_t x_9; lean_object* x_10; uint32_t x_11; uint32_t x_12; uint32_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_IO_AccessRight_flags(x_2);
x_4 = 3;
x_5 = 6;
x_6 = x_3 << x_5;
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_IO_AccessRight_flags(x_7);
x_9 = x_8 << x_4;
x_10 = lean_ctor_get(x_1, 2);
x_11 = l_IO_AccessRight_flags(x_10);
x_12 = x_9 | x_11;
x_13 = x_6 | x_12;
return x_13;
}
}
lean_object* l_IO_FileRight_flags___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_IO_FileRight_flags(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
lean_object* l_IO_Prim_setAccessRights___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_chmod(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_IO_setAccessRights(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = l_IO_FileRight_flags(x_2);
x_5 = lean_chmod(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_IO_setAccessRights___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_setAccessRights(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_st2eio___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_apply_1(x_1, x_2);
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
lean_object* l_IO_st2eio(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_IO_st2eio___rarg), 2, 0);
return x_3;
}
}
lean_object* l_IO_mkRef___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
lean_object* l_IO_mkRef(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_IO_mkRef___rarg), 2, 0);
return x_4;
}
}
lean_object* l_IO_mkRef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_mkRef(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_IO_FS_Stream_ofHandle___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_put_str(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_IO_FS_Stream_ofHandle___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_get_line(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_FS_Stream_ofHandle___elambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_write(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_IO_FS_Stream_ofHandle___elambda__4(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_prim_handle_read(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_IO_FS_Stream_ofHandle___elambda__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_flush(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_FS_Stream_ofHandle___elambda__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_prim_handle_is_eof(x_1, x_2);
return x_3;
}
}
lean_object* lean_stream_of_handle(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__6___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__5___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__4___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__3___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__2___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofHandle___elambda__1___boxed), 3, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set(x_8, 3, x_5);
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set(x_8, 5, x_7);
return x_8;
}
}
lean_object* l_IO_FS_Stream_ofHandle___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_ofHandle___elambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_FS_Stream_ofHandle___elambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_ofHandle___elambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_FS_Stream_ofHandle___elambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_ofHandle___elambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_FS_Stream_ofHandle___elambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_IO_FS_Stream_ofHandle___elambda__4(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_IO_FS_Stream_ofHandle___elambda__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_ofHandle___elambda__5(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_FS_Stream_ofHandle___elambda__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_ofHandle___elambda__6(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_FS_Stream_ofBuffer___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_st_ref_take(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_string_to_utf8(x_2);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_byte_array_size(x_7);
x_11 = lean_unsigned_to_nat(0u);
x_12 = 0;
lean_inc(x_10);
lean_inc(x_9);
x_13 = lean_byte_array_copy_slice(x_7, x_11, x_8, x_9, x_10, x_12);
lean_dec(x_7);
x_14 = lean_nat_add(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_st_ref_set(x_1, x_15, x_6);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
lean_object* l_ByteArray_findIdxAux___main___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_byte_array_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_6 = lean_byte_array_get(x_1, x_2);
x_7 = 0;
x_8 = x_6 == x_7;
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; 
x_9 = 10;
x_10 = x_6 == x_9;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_2);
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
}
}
}
lean_object* l_IO_FS_Stream_ofBuffer___elambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = l_ByteArray_findIdxAux___main___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1(x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_byte_array_size(x_7);
x_11 = l_ByteArray_extract(x_7, x_8, x_10);
x_12 = lean_string_from_utf8_unchecked(x_11);
lean_dec(x_11);
lean_ctor_set(x_4, 1, x_10);
x_13 = lean_st_ref_set(x_1, x_4, x_5);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_byte_array_get(x_7, x_18);
x_20 = 0;
x_21 = x_19 == x_20;
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_18, x_22);
lean_dec(x_18);
x_24 = l_ByteArray_extract(x_7, x_8, x_23);
x_25 = lean_string_from_utf8_unchecked(x_24);
lean_dec(x_24);
lean_ctor_set(x_4, 1, x_23);
x_26 = lean_st_ref_set(x_1, x_4, x_5);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = l_ByteArray_extract(x_7, x_8, x_18);
x_32 = lean_string_from_utf8_unchecked(x_31);
lean_dec(x_31);
lean_ctor_set(x_4, 1, x_18);
x_33 = lean_st_ref_set(x_1, x_4, x_5);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_4, 0);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_4);
lean_inc(x_39);
x_40 = l_ByteArray_findIdxAux___main___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1(x_38, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_byte_array_size(x_38);
x_42 = l_ByteArray_extract(x_38, x_39, x_41);
x_43 = lean_string_from_utf8_unchecked(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_41);
x_45 = lean_st_ref_set(x_1, x_44, x_5);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_byte_array_get(x_38, x_49);
x_51 = 0;
x_52 = x_50 == x_51;
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_49, x_53);
lean_dec(x_49);
x_55 = l_ByteArray_extract(x_38, x_39, x_54);
x_56 = lean_string_from_utf8_unchecked(x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_38);
lean_ctor_set(x_57, 1, x_54);
x_58 = lean_st_ref_set(x_1, x_57, x_5);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = l_ByteArray_extract(x_38, x_39, x_49);
x_63 = lean_string_from_utf8_unchecked(x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_38);
lean_ctor_set(x_64, 1, x_49);
x_65 = lean_st_ref_set(x_1, x_64, x_5);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
lean_object* l_IO_FS_Stream_ofBuffer___elambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_4 = lean_st_ref_take(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_byte_array_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = 0;
lean_inc(x_9);
lean_inc(x_8);
x_12 = lean_byte_array_copy_slice(x_2, x_10, x_7, x_8, x_9, x_11);
x_13 = lean_nat_add(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_st_ref_set(x_1, x_14, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l_IO_FS_Stream_ofBuffer___elambda__4(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_usize_to_nat(x_2);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_10);
lean_inc(x_9);
x_12 = l_ByteArray_extract(x_8, x_9, x_11);
lean_dec(x_11);
x_13 = lean_byte_array_size(x_12);
x_14 = lean_nat_add(x_9, x_13);
lean_dec(x_13);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_14);
x_15 = lean_st_ref_set(x_1, x_5, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_usize_to_nat(x_2);
x_23 = lean_nat_add(x_21, x_22);
lean_dec(x_22);
lean_inc(x_21);
x_24 = l_ByteArray_extract(x_20, x_21, x_23);
lean_dec(x_23);
x_25 = lean_byte_array_size(x_24);
x_26 = lean_nat_add(x_21, x_25);
lean_dec(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_st_ref_set(x_1, x_27, x_6);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
lean_object* l_IO_FS_Stream_ofBuffer___elambda__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_IO_FS_Stream_ofBuffer___elambda__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_byte_array_size(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_nat_dec_le(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = lean_box(x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_byte_array_size(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_nat_dec_le(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_IO_FS_Stream_ofBuffer___lambda__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_IO_FS_Stream_ofBuffer___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__5), 1, 0);
return x_1;
}
}
lean_object* l_IO_FS_Stream_ofBuffer(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__6), 2, 1);
lean_closure_set(x_3, 0, x_2);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__4___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__3___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__2___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_alloc_closure((void*)(l_IO_FS_Stream_ofBuffer___elambda__1___boxed), 3, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_IO_FS_Stream_ofBuffer___closed__1;
x_9 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set(x_9, 3, x_5);
lean_ctor_set(x_9, 4, x_6);
lean_ctor_set(x_9, 5, x_7);
return x_9;
}
}
lean_object* l_IO_FS_Stream_ofBuffer___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_ofBuffer___elambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_ByteArray_findIdxAux___main___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_ByteArray_findIdxAux___main___at_IO_FS_Stream_ofBuffer___elambda__2___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_FS_Stream_ofBuffer___elambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_ofBuffer___elambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_FS_Stream_ofBuffer___elambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_ofBuffer___elambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_FS_Stream_ofBuffer___elambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_IO_FS_Stream_ofBuffer___elambda__4(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_IO_FS_Stream_ofBuffer___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_ofBuffer___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_mkRef___at_IO_FS_withIsolatedStreams___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
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
lean_object* l_EStateM_catch___at_IO_FS_withIsolatedStreams___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
}
}
lean_object* l_EStateM_catch___at_IO_FS_withIsolatedStreams___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_EStateM_catch___at_IO_FS_withIsolatedStreams___spec__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_setStderr___at_IO_FS_withIsolatedStreams___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_set_stderr(x_1, x_2);
return x_3;
}
}
lean_object* l_Functor_discard___at_IO_FS_withIsolatedStreams___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_IO_withStderr___at_IO_FS_withIsolatedStreams___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_get_set_stderr(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_closure((void*)(l_IO_setStderr___at_IO_FS_withIsolatedStreams___spec__4), 2, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Functor_discard___at_IO_FS_withIsolatedStreams___spec__5(x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
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
lean_dec(x_9);
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
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_dec(x_8);
x_22 = l_Functor_discard___at_IO_FS_withIsolatedStreams___spec__5(x_7, x_21);
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
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_20);
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
lean_dec(x_2);
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
lean_object* l_IO_withStderr___at_IO_FS_withIsolatedStreams___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStderr___at_IO_FS_withIsolatedStreams___spec__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_setStdout___at_IO_FS_withIsolatedStreams___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_set_stdout(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_withStdout___at_IO_FS_withIsolatedStreams___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_get_set_stdout(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_closure((void*)(l_IO_setStdout___at_IO_FS_withIsolatedStreams___spec__7), 2, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Functor_discard___at_IO_FS_withIsolatedStreams___spec__5(x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
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
lean_dec(x_9);
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
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_dec(x_8);
x_22 = l_Functor_discard___at_IO_FS_withIsolatedStreams___spec__5(x_7, x_21);
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
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_20);
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
lean_dec(x_2);
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
lean_object* l_IO_withStdout___at_IO_FS_withIsolatedStreams___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdout___at_IO_FS_withIsolatedStreams___spec__6___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_setStdin___at_IO_FS_withIsolatedStreams___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_set_stdin(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_withStdin___at_IO_FS_withIsolatedStreams___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_get_set_stdin(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_closure((void*)(l_IO_setStdin___at_IO_FS_withIsolatedStreams___spec__9), 2, 1);
lean_closure_set(x_7, 0, x_5);
x_8 = lean_apply_1(x_2, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Functor_discard___at_IO_FS_withIsolatedStreams___spec__5(x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
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
lean_dec(x_9);
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
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_dec(x_8);
x_22 = l_Functor_discard___at_IO_FS_withIsolatedStreams___spec__5(x_7, x_21);
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
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_20);
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
lean_dec(x_2);
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
lean_object* l_IO_withStdin___at_IO_FS_withIsolatedStreams___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_withStdin___at_IO_FS_withIsolatedStreams___spec__8___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_IO_FS_withIsolatedStreams___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ByteArray_empty;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___rarg___lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_IO_FS_withIsolatedStreams___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___rarg___lambda__2), 2, 0);
return x_1;
}
}
lean_object* l_IO_FS_withIsolatedStreams___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_3 = l_IO_FS_withIsolatedStreams___rarg___closed__1;
x_4 = l_IO_mkRef___at_IO_FS_withIsolatedStreams___spec__1(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_IO_mkRef___at_IO_FS_withIsolatedStreams___spec__1(x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_IO_FS_Stream_ofBuffer(x_5);
lean_inc(x_8);
x_11 = l_IO_FS_Stream_ofBuffer(x_8);
x_12 = l_IO_FS_withIsolatedStreams___rarg___closed__2;
x_13 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = l_IO_FS_withIsolatedStreams___rarg___closed__3;
x_15 = lean_alloc_closure((void*)(l_EStateM_catch___at_IO_FS_withIsolatedStreams___spec__2___rarg), 3, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
lean_inc(x_11);
x_16 = lean_alloc_closure((void*)(l_IO_withStderr___at_IO_FS_withIsolatedStreams___spec__3___rarg), 3, 2);
lean_closure_set(x_16, 0, x_11);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_IO_withStdout___at_IO_FS_withIsolatedStreams___spec__6___rarg), 3, 2);
lean_closure_set(x_17, 0, x_11);
lean_closure_set(x_17, 1, x_16);
x_18 = l_IO_withStdin___at_IO_FS_withIsolatedStreams___spec__8___rarg(x_10, x_17, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_8, x_20);
lean_dec(x_8);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_string_from_utf8_unchecked(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_string_from_utf8_unchecked(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_19);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_8);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_IO_FS_withIsolatedStreams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_FS_withIsolatedStreams___rarg), 2, 0);
return x_2;
}
}
lean_object* l_IO_getStdout___at_Lean_HasRepr_hasEval___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stdout(x_1);
return x_2;
}
}
lean_object* l_IO_print___at_Lean_HasRepr_hasEval___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_stdout(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 5);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_6, x_1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* l_IO_println___at_Lean_HasRepr_hasEval___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at_Lean_HasRepr_hasEval___spec__2(x_4, x_2);
return x_5;
}
}
lean_object* l_Lean_HasRepr_hasEval___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
x_7 = lean_apply_1(x_1, x_6);
x_8 = l_IO_println___at_Lean_HasRepr_hasEval___spec__1(x_7, x_4);
return x_8;
}
}
lean_object* l_Lean_HasRepr_hasEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HasRepr_hasEval___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_HasRepr_hasEval___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_HasRepr_hasEval___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_Unit_hasEval___rarg(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Unit_HasRepr___closed__1;
x_4 = l_IO_println___at_Lean_HasRepr_hasEval___spec__1(x_3, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
lean_object* l_Lean_Unit_hasEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Unit_hasEval___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Unit_hasEval___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Unit_hasEval___rarg(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Unit_hasEval___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Unit_hasEval(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IO_HasEval___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_apply_2(x_2, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_dbgTraceVal___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_apply_3(x_1, x_9, x_11, x_8);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_IO_HasEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IO_HasEval___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_IO_HasEval___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_IO_HasEval___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_runEval___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = 0;
x_5 = lean_box(x_4);
x_6 = lean_apply_2(x_1, x_2, x_5);
x_7 = l_IO_FS_withIsolatedStreams___rarg(x_6, x_3);
return x_7;
}
}
lean_object* l_Lean_runEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_runEval___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_runEvalOld___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_dbgTraceVal___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l_Lean_runEval___rarg(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_Lean_runEvalOld(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_runEvalOld___rarg), 3, 0);
return x_2;
}
}
lean_object* initialize_Init_Control_EState(lean_object*);
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Data_String(lean_object*);
lean_object* initialize_Init_Data_ByteArray(lean_object*);
lean_object* initialize_Init_System_IOError(lean_object*);
lean_object* initialize_Init_System_FilePath(lean_object*);
lean_object* initialize_Init_System_ST(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_System_IO(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_EState(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IOError(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_ST(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_monadExceptAdapter___closed__1 = _init_l_monadExceptAdapter___closed__1();
lean_mark_persistent(l_monadExceptAdapter___closed__1);
l_EIO_MonadFinally___closed__1 = _init_l_EIO_MonadFinally___closed__1();
lean_mark_persistent(l_EIO_MonadFinally___closed__1);
l_EIO_HasOrelse___closed__1 = _init_l_EIO_HasOrelse___closed__1();
lean_mark_persistent(l_EIO_HasOrelse___closed__1);
l_IO_Prim_fopenFlags___closed__1 = _init_l_IO_Prim_fopenFlags___closed__1();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__1);
l_IO_Prim_fopenFlags___closed__2 = _init_l_IO_Prim_fopenFlags___closed__2();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__2);
l_IO_Prim_fopenFlags___closed__3 = _init_l_IO_Prim_fopenFlags___closed__3();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__3);
l_IO_Prim_fopenFlags___closed__4 = _init_l_IO_Prim_fopenFlags___closed__4();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__4);
l_IO_Prim_fopenFlags___closed__5 = _init_l_IO_Prim_fopenFlags___closed__5();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__5);
l_IO_Prim_fopenFlags___closed__6 = _init_l_IO_Prim_fopenFlags___closed__6();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__6);
l_IO_Prim_fopenFlags___closed__7 = _init_l_IO_Prim_fopenFlags___closed__7();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__7);
l_IO_Prim_fopenFlags___closed__8 = _init_l_IO_Prim_fopenFlags___closed__8();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__8);
l_IO_Prim_fopenFlags___closed__9 = _init_l_IO_Prim_fopenFlags___closed__9();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__9);
l_IO_Prim_fopenFlags___closed__10 = _init_l_IO_Prim_fopenFlags___closed__10();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__10);
l_IO_Prim_fopenFlags___closed__11 = _init_l_IO_Prim_fopenFlags___closed__11();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__11);
l_IO_Prim_fopenFlags___closed__12 = _init_l_IO_Prim_fopenFlags___closed__12();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__12);
l_IO_Prim_fopenFlags___closed__13 = _init_l_IO_Prim_fopenFlags___closed__13();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__13);
l_IO_Prim_fopenFlags___closed__14 = _init_l_IO_Prim_fopenFlags___closed__14();
lean_mark_persistent(l_IO_Prim_fopenFlags___closed__14);
l_IO_getStdin___rarg___closed__1 = _init_l_IO_getStdin___rarg___closed__1();
lean_mark_persistent(l_IO_getStdin___rarg___closed__1);
l_IO_getStdout___rarg___closed__1 = _init_l_IO_getStdout___rarg___closed__1();
lean_mark_persistent(l_IO_getStdout___rarg___closed__1);
l_IO_getStderr___rarg___closed__1 = _init_l_IO_getStderr___rarg___closed__1();
lean_mark_persistent(l_IO_getStderr___rarg___closed__1);
l_IO_appPath___rarg___closed__1 = _init_l_IO_appPath___rarg___closed__1();
lean_mark_persistent(l_IO_appPath___rarg___closed__1);
l_IO_currentDir___rarg___closed__1 = _init_l_IO_currentDir___rarg___closed__1();
lean_mark_persistent(l_IO_currentDir___rarg___closed__1);
l_IO_Process_run___closed__1 = _init_l_IO_Process_run___closed__1();
lean_mark_persistent(l_IO_Process_run___closed__1);
l_IO_Process_run___closed__2 = _init_l_IO_Process_run___closed__2();
lean_mark_persistent(l_IO_Process_run___closed__2);
l_IO_AccessRight_flags___closed__1 = _init_l_IO_AccessRight_flags___closed__1();
l_IO_AccessRight_flags___closed__2 = _init_l_IO_AccessRight_flags___closed__2();
l_IO_AccessRight_flags___closed__3 = _init_l_IO_AccessRight_flags___closed__3();
l_IO_AccessRight_flags___closed__4 = _init_l_IO_AccessRight_flags___closed__4();
l_IO_AccessRight_flags___closed__5 = _init_l_IO_AccessRight_flags___closed__5();
l_IO_AccessRight_flags___closed__6 = _init_l_IO_AccessRight_flags___closed__6();
l_IO_AccessRight_flags___closed__7 = _init_l_IO_AccessRight_flags___closed__7();
l_IO_AccessRight_flags___closed__8 = _init_l_IO_AccessRight_flags___closed__8();
l_IO_AccessRight_flags___closed__9 = _init_l_IO_AccessRight_flags___closed__9();
l_IO_AccessRight_flags___closed__10 = _init_l_IO_AccessRight_flags___closed__10();
l_IO_AccessRight_flags___closed__11 = _init_l_IO_AccessRight_flags___closed__11();
l_IO_AccessRight_flags___closed__12 = _init_l_IO_AccessRight_flags___closed__12();
l_IO_AccessRight_flags___closed__13 = _init_l_IO_AccessRight_flags___closed__13();
l_IO_FS_Stream_ofBuffer___closed__1 = _init_l_IO_FS_Stream_ofBuffer___closed__1();
lean_mark_persistent(l_IO_FS_Stream_ofBuffer___closed__1);
l_IO_FS_withIsolatedStreams___rarg___closed__1 = _init_l_IO_FS_withIsolatedStreams___rarg___closed__1();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___rarg___closed__1);
l_IO_FS_withIsolatedStreams___rarg___closed__2 = _init_l_IO_FS_withIsolatedStreams___rarg___closed__2();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___rarg___closed__2);
l_IO_FS_withIsolatedStreams___rarg___closed__3 = _init_l_IO_FS_withIsolatedStreams___rarg___closed__3();
lean_mark_persistent(l_IO_FS_withIsolatedStreams___rarg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
