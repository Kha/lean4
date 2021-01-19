// Lean compiler output
// Module: Lean.Server.Watchdog
// Imports: Init Init.System.IO Init.Data.ByteArray Std.Data.RBMap Lean.Elab.Import Lean.Data.Lsp Lean.Server.FileSource Lean.Server.Utils
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
lean_object* l_Lean_Server_Watchdog_mainLoop_match__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__2___rarg(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__15___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_startFileWorker(lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Server_Watchdog_runClientTask_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_shutdown_match__3___rarg(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__2(lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stdin(lean_object*);
lean_object* l_IO_FS_Stream_writeLspRequest___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_handleCancelRequest___spec__3(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_165____closed__3;
lean_object* l_Std_RBNode_insert___at_Lean_Server_Watchdog_updateFileWorkers___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidOpenTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_88_(lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_writeRequest___at_Lean_Server_Watchdog_handleRequest___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonTextDocumentPositionParams____x40_Lean_Data_Lsp_Basic___hyg_1299_(lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleDidChange___spec__3(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleDidOpen(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_quote___closed__1;
lean_object* l_Lean_Server_Watchdog_handleRequest___closed__1;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___closed__2;
lean_object* lean_io_wait_any(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1;
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleNotification___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_log___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__3;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest___closed__2;
lean_object* l_Lean_Server_Watchdog_handleNotification___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2;
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages___closed__1;
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_handleNotification___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_terminateFileWorker___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___closed__1;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__3;
lean_object* l_Lean_Server_Watchdog_handleDidChange___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__5;
extern lean_object* l_Lean_Lsp_Ipc_ipcStdioConfig___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Lsp_Ipc_collectDiagnostics___closed__1;
lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
lean_object* l_Lean_Server_Watchdog_findFileWorker_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_shutdown_match__4___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__6;
lean_object* l_Lean_Server_Watchdog_FileWorker_writeNotification___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest___closed__4;
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_collectDiagnostics___spec__3(lean_object*);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
lean_object* l_Lean_Server_Watchdog_shutdown_match__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleCancelRequest___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog_match__2(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1(lean_object*, lean_object*);
lean_object* lean_get_stderr(lean_object*);
lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__2;
lean_object* l_Lean_Server_Watchdog_shutdown___boxed(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__14___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_eraseFileWorker___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_getStdin___at_Lean_Server_Watchdog_watchdogMain___spec__1(lean_object*);
lean_object* l_IO_FS_Stream_readLspMessage(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_startFileWorker___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_runClientTask(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_watchdogMain___boxed__const__2;
lean_object* l_Lean_Elab_headerToImports(lean_object*);
lean_object* l_Lean_Server_Watchdog_terminateFileWorker___closed__1;
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*);
lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_writeNotification___at_Lean_Server_Watchdog_handleDidChange___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_writeRequest___at_Lean_Server_Watchdog_handleRequest___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__3;
lean_object* l_Lean_Server_Watchdog_mainLoop_match__4(lean_object*);
lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleDidChange_match__2(lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__2___rarg(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__3(lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__1___boxed(lean_object*, lean_object*);
lean_object* l_IO_throwServerError___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_writeNotification___at_Lean_Server_Watchdog_startFileWorker___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__5;
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_startFileWorker___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_writeRequest(lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__4;
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2;
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__8(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_parseImports___closed__1;
lean_object* l_Lean_Server_Watchdog_parseParams(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleDidChange_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest___closed__3;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_writeMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__10;
lean_object* l_Lean_Server_Watchdog_workerCfg;
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__4(lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__5;
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleDidChange(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_findFileWorker_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__5;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__3;
lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1(lean_object*, lean_object*);
lean_object* l_Std_RBNode_setBlack___rarg(lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop___closed__1;
lean_object* l_Lean_Server_Watchdog_terminateFileWorker(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__1___rarg(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleDidChange_match__1(lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleCancelRequest___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__3(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
extern lean_object* l_Lean_Parser_Command_initialize___elambda__1___closed__1;
lean_object* l_Lean_Server_Watchdog_runClientTask___closed__1;
lean_object* l_Lean_Server_Watchdog_handleDidClose(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__7;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_exit___elambda__1___closed__1;
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages___lambda__1(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__1(lean_object*, lean_object*);
extern lean_object* l_Task_Priority_dedicated;
extern lean_object* l_Lean_Lsp_msgToDiagnostic___closed__1;
lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_runClientTask___closed__2;
lean_object* l_Lean_Server_Watchdog_shutdown_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop___closed__2;
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__7;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__2;
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4;
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__4;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__4___boxed(lean_object*);
extern lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_165____closed__9;
extern lean_object* l_IO_FS_Stream_readLspNotificationAs___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__7(size_t, size_t, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleDidChange___closed__1;
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_eraseFileWorker(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_shutdown_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleDidClose___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_165____closed__4;
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_RBNode_appendTrees___rarg(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_handleCancelRequest___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
lean_object* l_Lean_Server_Watchdog_mainLoop_match__3(lean_object*);
lean_object* l_Std_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_writeMessage(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_RBNode_isBlack___rarg(lean_object*);
extern lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_165____closed__8;
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__4(lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__1(lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_59_(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_handleNotification___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__2___boxed(lean_object*, lean_object*);
extern lean_object* l_IO_FS_Stream_readRequestAs___closed__5;
lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__3(lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8___closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__8;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_watchdogMain___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_shutdown_match__3(lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__4(lean_object*);
lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_handleDidChange___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleCrash(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1;
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonTextDocumentPositionParams____x40_Lean_Data_Lsp_Basic___hyg_1265_(lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___closed__2;
lean_object* l_Lean_Server_Watchdog_mainLoop_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleCancelRequest___spec__7(size_t, size_t, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__14(size_t, size_t, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__1;
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___closed__1;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__2(lean_object*, lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_stream_of_handle(lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___closed__1;
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8___closed__2;
lean_object* l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonWaitForDiagnosticsParam____x40_Lean_Data_Lsp_Extra___hyg_32_(lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__2___rarg(lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_stdout(lean_object*);
lean_object* lean_server_watchdog_main(lean_object*, lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleNotification_match__1(lean_object*);
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonDocumentSymbolParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_125_(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_84_(lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Server_Watchdog_shutdown_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__2;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_handleRequest___spec__10(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__18(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
lean_object* l_Lean_FileMap_ofString(lean_object*);
lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleNotification(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidCloseTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_439_(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__19___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_watchdogMain___boxed__const__1;
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__3___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams_match__1(lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__1;
extern lean_object* l_IO_FS_Stream_readNotificationAs___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__3(lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__6;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__19(size_t, size_t, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(lean_object*, lean_object*);
lean_object* l_Std_RBNode_fold___at_Lean_Server_Watchdog_mainLoop___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__2;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_shutdown(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_writeNotification___at_Lean_Server_Watchdog_handleCancelRequest___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___closed__2;
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__7(lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__11(lean_object*);
lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities;
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_match__1(lean_object*);
lean_object* l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_writeNotification___at_Lean_Server_Watchdog_handleCancelRequest___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleNotification_match__1___rarg___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__12;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
lean_object* l_Lean_Server_Watchdog_FileWorker_writeRequest___at_Lean_Server_Watchdog_handleRequest___spec__16(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleDidChange_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_fold___at_Lean_Server_Watchdog_mainLoop___spec__1___lambda__1(lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_startFileWorker___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_RBNode_isRed___rarg(lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_toJsonDidChangeTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_275_(lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop_match__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_tryWriteMessage___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
lean_object* l_Lean_Server_Watchdog_handleRequest(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleDidChange___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest_match__1___rarg___closed__2;
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage_match__2(lean_object*);
lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__2(lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__2(lean_object*);
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_log___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleCancelRequest___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stdout(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__3___rarg(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest_match__1___rarg___closed__1;
lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
lean_object* l_Lean_Server_Watchdog_handleDidChange___closed__2;
lean_object* l_Lean_Server_Watchdog_watchdogMain___closed__1;
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__2(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_getBuiltinSearchPath___closed__4;
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__11;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleDidChange___spec__6___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_stdin(lean_object*);
lean_object* l_Lean_Server_Watchdog_shutdown_match__2(lean_object*);
extern lean_object* l_IO_FS_Stream_readRequestAs___closed__2;
lean_object* l_Lean_Server_Watchdog_updateFileWorkers(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleCrash___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__8;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___closed__1;
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop_match__2___rarg___closed__1;
extern lean_object* l_IO_FS_Stream_readRequestAs___closed__1;
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__15(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
extern lean_object* l_IO_FS_Stream_readLspRequestAs___closed__1;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___closed__2;
lean_object* l_Lean_Server_Watchdog_shutdown_match__4(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_findFileWorker___closed__1;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_runClientTask_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_foldDocumentChanges(lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChange___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_toJsonDidOpenTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_63_(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleDidChange___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__2;
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_startFileWorker___closed__1;
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_updateFileWorkers___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__3;
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__4;
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l_Lean_Server_Watchdog_FileWorker_writeNotification(lean_object*);
lean_object* l_Lean_Server_Watchdog_findFileWorker___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_165____closed__1;
extern lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___closed__1;
extern lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_165____closed__2;
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleDidChange___spec__6(size_t, size_t, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_maybeTee(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_app_dir(lean_object*);
lean_object* l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__1;
lean_object* l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_toJsonDocumentSymbolParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_155_(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_tryWriteMessage___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__13;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_exeSuffix;
lean_object* l_Lean_Server_Watchdog_handleCancelRequest(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_log(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__1;
lean_object* l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidChangeTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_309_(lean_object*);
lean_object* l_Lean_Server_Watchdog_mainLoop_match__2(lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___closed__2;
lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_handleRequest___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_ins___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChange___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_165_(lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_FileWorker_writeRequest___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_JsonRpc_instToJsonMessage___closed__9;
uint8_t l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__2;
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage_match__1(lean_object*);
lean_object* l_Lean_Server_Watchdog_shutdown_match__4___rarg(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleNotification_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_findFileWorker(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleDidChange___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleRequest_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_startFileWorker___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__3___rarg(lean_object*);
lean_object* l_Lean_Server_Watchdog_handleDidChange___lambda__1___closed__2;
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__2(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_writeLspNotification___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_handleDidChange___lambda__1___closed__1;
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2___closed__1;
lean_object* l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_395_(lean_object*);
uint8_t l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__1(lean_object*, lean_object*);
lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___closed__1;
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__1;
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__2___boxed(lean_object*);
static lean_object* _init_l_Lean_Server_Watchdog_workerCfg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Lsp_Ipc_ipcStdioConfig___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Elab_parseImports___closed__1;
x_4 = l_Lean_Parser_mkInputContext(x_1, x_3);
x_5 = l_Lean_Parser_parseHeader(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_stdin(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_stream_of_handle(x_3);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_stdout(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_stream_of_handle(x_3);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_readMessage_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_box(x_5);
x_9 = lean_apply_4(x_2, x_4, x_8, x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_readMessage_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_inc(x_1);
x_9 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_1, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
lean_inc(x_1);
lean_inc(x_6);
x_10 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_6, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = l_Std_RBNode_appendTrees___rarg(x_5, x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l_Std_RBNode_isBlack___rarg(x_8);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_8);
x_14 = 0;
lean_ctor_set(x_2, 3, x_13);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_14);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_2);
x_15 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_8);
x_16 = l_Std_RBNode_balRight___rarg(x_5, x_6, x_7, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = l_Std_RBNode_isBlack___rarg(x_5);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_5);
x_19 = 0;
lean_ctor_set(x_2, 0, x_18);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_19);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_2);
x_20 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_5);
x_21 = l_Std_RBNode_balLeft___rarg(x_20, x_6, x_7, x_8);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
lean_inc(x_23);
lean_inc(x_1);
x_26 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_1, x_23);
if (x_26 == 0)
{
uint8_t x_27; 
lean_inc(x_1);
lean_inc(x_23);
x_27 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_23, x_1);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_1);
x_28 = l_Std_RBNode_appendTrees___rarg(x_22, x_25);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = l_Std_RBNode_isBlack___rarg(x_25);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_25);
x_31 = 0;
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_25);
x_34 = l_Std_RBNode_balRight___rarg(x_22, x_23, x_24, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = l_Std_RBNode_isBlack___rarg(x_22);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_22);
x_37 = 0;
x_38 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_24);
lean_ctor_set(x_38, 3, x_25);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_22);
x_40 = l_Std_RBNode_balLeft___rarg(x_39, x_23, x_24, x_25);
return x_40;
}
}
}
}
}
}
lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_RBNode_del___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__2(x_1, x_2);
x_4 = l_Std_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 4);
x_7 = lean_st_ref_take(x_6, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Std_RBNode_erase___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__1(x_5, x_8);
x_11 = lean_st_ref_set(x_6, x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_3 = l_Lean_Server_Watchdog_FileWorker_stdout(x_1);
x_4 = l_IO_FS_Stream_readLspMessage(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_st_ref_take(x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Std_RBNode_erase___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__1(x_7, x_10);
x_13 = lean_st_ref_set(x_8, x_12, x_11);
lean_dec(x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Server_Watchdog_FileWorker_readMessage___lambda__1(x_5, x_1, x_14, x_15);
lean_dec(x_14);
lean_dec(x_1);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = l_Lean_Server_Watchdog_FileWorker_readMessage___lambda__1(x_5, x_1, x_18, x_17);
lean_dec(x_1);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
return x_4;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_readMessage___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_FileWorker_readMessage___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_writeMessage(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Server_Watchdog_FileWorker_stdin(x_1);
x_5 = l_IO_FS_Stream_writeLspMessage(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_writeMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_FileWorker_writeMessage(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_writeNotification___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Server_Watchdog_FileWorker_stdin(x_2);
x_6 = l_IO_FS_Stream_writeLspNotification___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_writeNotification(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_writeNotification___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_ins___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_2);
x_13 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_2, x_10);
if (x_13 == 0)
{
uint8_t x_14; 
lean_inc(x_2);
lean_inc(x_10);
x_14 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_10, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_10);
x_15 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__2(x_12, x_2, x_3);
x_17 = 0;
lean_ctor_set(x_1, 3, x_16);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_17);
return x_1;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__2(x_9, x_2, x_3);
x_19 = 0;
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
lean_inc(x_21);
lean_inc(x_2);
x_24 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_2, x_21);
if (x_24 == 0)
{
uint8_t x_25; 
lean_inc(x_2);
lean_inc(x_21);
x_25 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_21, x_2);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_21);
x_26 = 0;
x_27 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 2, x_3);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_26);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__2(x_23, x_2, x_3);
x_29 = 0;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__2(x_20, x_2, x_3);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
lean_inc(x_2);
x_39 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_2, x_36);
if (x_39 == 0)
{
uint8_t x_40; 
lean_inc(x_2);
lean_inc(x_36);
x_40 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_36, x_2);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_37);
lean_dec(x_36);
x_41 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_41);
return x_1;
}
else
{
uint8_t x_42; 
x_42 = l_Std_RBNode_isRed___rarg(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__2(x_38, x_2, x_3);
x_44 = 1;
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_44);
return x_1;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__2(x_38, x_2, x_3);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 3);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_45, 3);
lean_dec(x_49);
x_50 = lean_ctor_get(x_45, 0);
lean_dec(x_50);
x_51 = 0;
lean_ctor_set(x_45, 0, x_47);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_51);
x_52 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_52);
return x_1;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_45, 1);
x_54 = lean_ctor_get(x_45, 2);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_45);
x_55 = 0;
x_56 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_54);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_55);
x_57 = 1;
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_57);
return x_1;
}
}
else
{
uint8_t x_58; 
x_58 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_45);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_45, 1);
x_61 = lean_ctor_get(x_45, 2);
x_62 = lean_ctor_get(x_45, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_45, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_47);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_47, 0);
x_66 = lean_ctor_get(x_47, 1);
x_67 = lean_ctor_get(x_47, 2);
x_68 = lean_ctor_get(x_47, 3);
x_69 = 1;
lean_ctor_set(x_47, 3, x_46);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_69);
lean_ctor_set(x_45, 3, x_68);
lean_ctor_set(x_45, 2, x_67);
lean_ctor_set(x_45, 1, x_66);
lean_ctor_set(x_45, 0, x_65);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_69);
x_70 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_61);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_70);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; 
x_71 = lean_ctor_get(x_47, 0);
x_72 = lean_ctor_get(x_47, 1);
x_73 = lean_ctor_get(x_47, 2);
x_74 = lean_ctor_get(x_47, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_47);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_35);
lean_ctor_set(x_76, 1, x_36);
lean_ctor_set(x_76, 2, x_37);
lean_ctor_set(x_76, 3, x_46);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_45, 3, x_74);
lean_ctor_set(x_45, 2, x_73);
lean_ctor_set(x_45, 1, x_72);
lean_ctor_set(x_45, 0, x_71);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_75);
x_77 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_61);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_77);
return x_1;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_78 = lean_ctor_get(x_45, 1);
x_79 = lean_ctor_get(x_45, 2);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_45);
x_80 = lean_ctor_get(x_47, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_47, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_47, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_47, 3);
lean_inc(x_83);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_84 = x_47;
} else {
 lean_dec_ref(x_47);
 x_84 = lean_box(0);
}
x_85 = 1;
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(1, 4, 1);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_35);
lean_ctor_set(x_86, 1, x_36);
lean_ctor_set(x_86, 2, x_37);
lean_ctor_set(x_86, 3, x_46);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_85);
x_87 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set(x_87, 2, x_82);
lean_ctor_set(x_87, 3, x_83);
lean_ctor_set_uint8(x_87, sizeof(void*)*4, x_85);
x_88 = 0;
lean_ctor_set(x_1, 3, x_87);
lean_ctor_set(x_1, 2, x_79);
lean_ctor_set(x_1, 1, x_78);
lean_ctor_set(x_1, 0, x_86);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_88);
return x_1;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_45);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_45, 3);
lean_dec(x_90);
x_91 = lean_ctor_get(x_45, 0);
lean_dec(x_91);
x_92 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_92);
x_93 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_93);
return x_1;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_45, 1);
x_95 = lean_ctor_get(x_45, 2);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_45);
x_96 = 0;
x_97 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_97, 0, x_46);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_47);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_96);
x_98 = 1;
lean_ctor_set(x_1, 3, x_97);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_98);
return x_1;
}
}
}
}
else
{
uint8_t x_99; 
x_99 = lean_ctor_get_uint8(x_46, sizeof(void*)*4);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_45);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_45, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_46);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; 
x_103 = lean_ctor_get(x_46, 0);
x_104 = lean_ctor_get(x_46, 1);
x_105 = lean_ctor_get(x_46, 2);
x_106 = lean_ctor_get(x_46, 3);
x_107 = 1;
lean_ctor_set(x_46, 3, x_103);
lean_ctor_set(x_46, 2, x_37);
lean_ctor_set(x_46, 1, x_36);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_107);
lean_ctor_set(x_45, 0, x_106);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_107);
x_108 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_105);
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_108);
return x_1;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; uint8_t x_115; 
x_109 = lean_ctor_get(x_46, 0);
x_110 = lean_ctor_get(x_46, 1);
x_111 = lean_ctor_get(x_46, 2);
x_112 = lean_ctor_get(x_46, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_46);
x_113 = 1;
x_114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_114, 0, x_35);
lean_ctor_set(x_114, 1, x_36);
lean_ctor_set(x_114, 2, x_37);
lean_ctor_set(x_114, 3, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
lean_ctor_set(x_45, 0, x_112);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_113);
x_115 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_1, 1, x_110);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_115);
return x_1;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_116 = lean_ctor_get(x_45, 1);
x_117 = lean_ctor_get(x_45, 2);
x_118 = lean_ctor_get(x_45, 3);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_45);
x_119 = lean_ctor_get(x_46, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_46, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_46, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_46, 3);
lean_inc(x_122);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_123 = x_46;
} else {
 lean_dec_ref(x_46);
 x_123 = lean_box(0);
}
x_124 = 1;
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(1, 4, 1);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_35);
lean_ctor_set(x_125, 1, x_36);
lean_ctor_set(x_125, 2, x_37);
lean_ctor_set(x_125, 3, x_119);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_116);
lean_ctor_set(x_126, 2, x_117);
lean_ctor_set(x_126, 3, x_118);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_124);
x_127 = 0;
lean_ctor_set(x_1, 3, x_126);
lean_ctor_set(x_1, 2, x_121);
lean_ctor_set(x_1, 1, x_120);
lean_ctor_set(x_1, 0, x_125);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
return x_1;
}
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_45, 3);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_45);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_45, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_45, 0);
lean_dec(x_131);
x_132 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_132);
x_133 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; uint8_t x_138; 
x_134 = lean_ctor_get(x_45, 1);
x_135 = lean_ctor_get(x_45, 2);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_45);
x_136 = 0;
x_137 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_137, 0, x_46);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_137, 2, x_135);
lean_ctor_set(x_137, 3, x_128);
lean_ctor_set_uint8(x_137, sizeof(void*)*4, x_136);
x_138 = 1;
lean_ctor_set(x_1, 3, x_137);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_138);
return x_1;
}
}
else
{
uint8_t x_139; 
x_139 = lean_ctor_get_uint8(x_128, sizeof(void*)*4);
if (x_139 == 0)
{
uint8_t x_140; 
lean_free_object(x_1);
x_140 = !lean_is_exclusive(x_45);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_45, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_45, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_128);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_128, 0);
x_145 = lean_ctor_get(x_128, 1);
x_146 = lean_ctor_get(x_128, 2);
x_147 = lean_ctor_get(x_128, 3);
x_148 = 1;
lean_inc(x_46);
lean_ctor_set(x_128, 3, x_46);
lean_ctor_set(x_128, 2, x_37);
lean_ctor_set(x_128, 1, x_36);
lean_ctor_set(x_128, 0, x_35);
x_149 = !lean_is_exclusive(x_46);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_150 = lean_ctor_get(x_46, 3);
lean_dec(x_150);
x_151 = lean_ctor_get(x_46, 2);
lean_dec(x_151);
x_152 = lean_ctor_get(x_46, 1);
lean_dec(x_152);
x_153 = lean_ctor_get(x_46, 0);
lean_dec(x_153);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_148);
lean_ctor_set(x_46, 3, x_147);
lean_ctor_set(x_46, 2, x_146);
lean_ctor_set(x_46, 1, x_145);
lean_ctor_set(x_46, 0, x_144);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_148);
x_154 = 0;
lean_ctor_set(x_45, 3, x_46);
lean_ctor_set(x_45, 0, x_128);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_154);
return x_45;
}
else
{
lean_object* x_155; uint8_t x_156; 
lean_dec(x_46);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_148);
x_155 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_155, 0, x_144);
lean_ctor_set(x_155, 1, x_145);
lean_ctor_set(x_155, 2, x_146);
lean_ctor_set(x_155, 3, x_147);
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_148);
x_156 = 0;
lean_ctor_set(x_45, 3, x_155);
lean_ctor_set(x_45, 0, x_128);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_156);
return x_45;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_157 = lean_ctor_get(x_128, 0);
x_158 = lean_ctor_get(x_128, 1);
x_159 = lean_ctor_get(x_128, 2);
x_160 = lean_ctor_get(x_128, 3);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_128);
x_161 = 1;
lean_inc(x_46);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_35);
lean_ctor_set(x_162, 1, x_36);
lean_ctor_set(x_162, 2, x_37);
lean_ctor_set(x_162, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_163 = x_46;
} else {
 lean_dec_ref(x_46);
 x_163 = lean_box(0);
}
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_161);
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 4, 1);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_158);
lean_ctor_set(x_164, 2, x_159);
lean_ctor_set(x_164, 3, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_161);
x_165 = 0;
lean_ctor_set(x_45, 3, x_164);
lean_ctor_set(x_45, 0, x_162);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_165);
return x_45;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; 
x_166 = lean_ctor_get(x_45, 1);
x_167 = lean_ctor_get(x_45, 2);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_45);
x_168 = lean_ctor_get(x_128, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_128, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_128, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_128, 3);
lean_inc(x_171);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 x_172 = x_128;
} else {
 lean_dec_ref(x_128);
 x_172 = lean_box(0);
}
x_173 = 1;
lean_inc(x_46);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(1, 4, 1);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_35);
lean_ctor_set(x_174, 1, x_36);
lean_ctor_set(x_174, 2, x_37);
lean_ctor_set(x_174, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_175 = x_46;
} else {
 lean_dec_ref(x_46);
 x_175 = lean_box(0);
}
lean_ctor_set_uint8(x_174, sizeof(void*)*4, x_173);
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 4, 1);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_169);
lean_ctor_set(x_176, 2, x_170);
lean_ctor_set(x_176, 3, x_171);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_173);
x_177 = 0;
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_166);
lean_ctor_set(x_178, 2, x_167);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_177);
return x_178;
}
}
else
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_45);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_45, 3);
lean_dec(x_180);
x_181 = lean_ctor_get(x_45, 0);
lean_dec(x_181);
x_182 = !lean_is_exclusive(x_46);
if (x_182 == 0)
{
uint8_t x_183; uint8_t x_184; 
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_139);
x_183 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_183);
x_184 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_184);
return x_1;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; 
x_185 = lean_ctor_get(x_46, 0);
x_186 = lean_ctor_get(x_46, 1);
x_187 = lean_ctor_get(x_46, 2);
x_188 = lean_ctor_get(x_46, 3);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_46);
x_189 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_189, 1, x_186);
lean_ctor_set(x_189, 2, x_187);
lean_ctor_set(x_189, 3, x_188);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_139);
x_190 = 0;
lean_ctor_set(x_45, 0, x_189);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_190);
x_191 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_191);
return x_1;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; uint8_t x_202; 
x_192 = lean_ctor_get(x_45, 1);
x_193 = lean_ctor_get(x_45, 2);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_45);
x_194 = lean_ctor_get(x_46, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_46, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_46, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_46, 3);
lean_inc(x_197);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_198 = x_46;
} else {
 lean_dec_ref(x_46);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 4, 1);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_194);
lean_ctor_set(x_199, 1, x_195);
lean_ctor_set(x_199, 2, x_196);
lean_ctor_set(x_199, 3, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_139);
x_200 = 0;
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_192);
lean_ctor_set(x_201, 2, x_193);
lean_ctor_set(x_201, 3, x_128);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_200);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
}
}
}
}
}
}
else
{
uint8_t x_203; 
x_203 = l_Std_RBNode_isRed___rarg(x_35);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__2(x_35, x_2, x_3);
x_205 = 1;
lean_ctor_set(x_1, 0, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_205);
return x_1;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__2(x_35, x_2, x_3);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_206, 3);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_206);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_206, 3);
lean_dec(x_210);
x_211 = lean_ctor_get(x_206, 0);
lean_dec(x_211);
x_212 = 0;
lean_ctor_set(x_206, 0, x_208);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_212);
x_213 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_213);
return x_1;
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_206, 1);
x_215 = lean_ctor_get(x_206, 2);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_206);
x_216 = 0;
x_217 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_217, 0, x_208);
lean_ctor_set(x_217, 1, x_214);
lean_ctor_set(x_217, 2, x_215);
lean_ctor_set(x_217, 3, x_208);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_216);
x_218 = 1;
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_218);
return x_1;
}
}
else
{
uint8_t x_219; 
x_219 = lean_ctor_get_uint8(x_208, sizeof(void*)*4);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_206);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_206, 1);
x_222 = lean_ctor_get(x_206, 2);
x_223 = lean_ctor_get(x_206, 3);
lean_dec(x_223);
x_224 = lean_ctor_get(x_206, 0);
lean_dec(x_224);
x_225 = !lean_is_exclusive(x_208);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; 
x_226 = lean_ctor_get(x_208, 0);
x_227 = lean_ctor_get(x_208, 1);
x_228 = lean_ctor_get(x_208, 2);
x_229 = lean_ctor_get(x_208, 3);
x_230 = 1;
lean_ctor_set(x_208, 3, x_226);
lean_ctor_set(x_208, 2, x_222);
lean_ctor_set(x_208, 1, x_221);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_230);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_229);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_230);
x_231 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_231);
return x_1;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; uint8_t x_238; 
x_232 = lean_ctor_get(x_208, 0);
x_233 = lean_ctor_get(x_208, 1);
x_234 = lean_ctor_get(x_208, 2);
x_235 = lean_ctor_get(x_208, 3);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_208);
x_236 = 1;
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_207);
lean_ctor_set(x_237, 1, x_221);
lean_ctor_set(x_237, 2, x_222);
lean_ctor_set(x_237, 3, x_232);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_236);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_235);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_236);
x_238 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_234);
lean_ctor_set(x_1, 1, x_233);
lean_ctor_set(x_1, 0, x_237);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_238);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_239 = lean_ctor_get(x_206, 1);
x_240 = lean_ctor_get(x_206, 2);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_206);
x_241 = lean_ctor_get(x_208, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_208, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_208, 2);
lean_inc(x_243);
x_244 = lean_ctor_get(x_208, 3);
lean_inc(x_244);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 lean_ctor_release(x_208, 3);
 x_245 = x_208;
} else {
 lean_dec_ref(x_208);
 x_245 = lean_box(0);
}
x_246 = 1;
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(1, 4, 1);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_207);
lean_ctor_set(x_247, 1, x_239);
lean_ctor_set(x_247, 2, x_240);
lean_ctor_set(x_247, 3, x_241);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
x_248 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_248, 0, x_244);
lean_ctor_set(x_248, 1, x_36);
lean_ctor_set(x_248, 2, x_37);
lean_ctor_set(x_248, 3, x_38);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_246);
x_249 = 0;
lean_ctor_set(x_1, 3, x_248);
lean_ctor_set(x_1, 2, x_243);
lean_ctor_set(x_1, 1, x_242);
lean_ctor_set(x_1, 0, x_247);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_249);
return x_1;
}
}
else
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_206);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_254; 
x_251 = lean_ctor_get(x_206, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_206, 0);
lean_dec(x_252);
x_253 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_253);
x_254 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_254);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_255 = lean_ctor_get(x_206, 1);
x_256 = lean_ctor_get(x_206, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_206);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_207);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_208);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
x_259 = 1;
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
else
{
uint8_t x_260; 
x_260 = lean_ctor_get_uint8(x_207, sizeof(void*)*4);
if (x_260 == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_206);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_262 = lean_ctor_get(x_206, 1);
x_263 = lean_ctor_get(x_206, 2);
x_264 = lean_ctor_get(x_206, 3);
x_265 = lean_ctor_get(x_206, 0);
lean_dec(x_265);
x_266 = !lean_is_exclusive(x_207);
if (x_266 == 0)
{
uint8_t x_267; uint8_t x_268; 
x_267 = 1;
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_267);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_267);
x_268 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_207);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_268);
return x_1;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; uint8_t x_275; 
x_269 = lean_ctor_get(x_207, 0);
x_270 = lean_ctor_get(x_207, 1);
x_271 = lean_ctor_get(x_207, 2);
x_272 = lean_ctor_get(x_207, 3);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_207);
x_273 = 1;
x_274 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set(x_274, 1, x_270);
lean_ctor_set(x_274, 2, x_271);
lean_ctor_set(x_274, 3, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*4, x_273);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_273);
x_275 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_274);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_275);
return x_1;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_276 = lean_ctor_get(x_206, 1);
x_277 = lean_ctor_get(x_206, 2);
x_278 = lean_ctor_get(x_206, 3);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_206);
x_279 = lean_ctor_get(x_207, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_207, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_207, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_207, 3);
lean_inc(x_282);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_283 = x_207;
} else {
 lean_dec_ref(x_207);
 x_283 = lean_box(0);
}
x_284 = 1;
if (lean_is_scalar(x_283)) {
 x_285 = lean_alloc_ctor(1, 4, 1);
} else {
 x_285 = x_283;
}
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_280);
lean_ctor_set(x_285, 2, x_281);
lean_ctor_set(x_285, 3, x_282);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_284);
x_286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_286, 0, x_278);
lean_ctor_set(x_286, 1, x_36);
lean_ctor_set(x_286, 2, x_37);
lean_ctor_set(x_286, 3, x_38);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_284);
x_287 = 0;
lean_ctor_set(x_1, 3, x_286);
lean_ctor_set(x_1, 2, x_277);
lean_ctor_set(x_1, 1, x_276);
lean_ctor_set(x_1, 0, x_285);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_287);
return x_1;
}
}
else
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_206, 3);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_206);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; 
x_290 = lean_ctor_get(x_206, 3);
lean_dec(x_290);
x_291 = lean_ctor_get(x_206, 0);
lean_dec(x_291);
x_292 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_292);
x_293 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_293);
return x_1;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_206, 1);
x_295 = lean_ctor_get(x_206, 2);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_206);
x_296 = 0;
x_297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_297, 0, x_207);
lean_ctor_set(x_297, 1, x_294);
lean_ctor_set(x_297, 2, x_295);
lean_ctor_set(x_297, 3, x_288);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_296);
x_298 = 1;
lean_ctor_set(x_1, 0, x_297);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_298);
return x_1;
}
}
else
{
uint8_t x_299; 
x_299 = lean_ctor_get_uint8(x_288, sizeof(void*)*4);
if (x_299 == 0)
{
uint8_t x_300; 
lean_free_object(x_1);
x_300 = !lean_is_exclusive(x_206);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_301 = lean_ctor_get(x_206, 1);
x_302 = lean_ctor_get(x_206, 2);
x_303 = lean_ctor_get(x_206, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_206, 0);
lean_dec(x_304);
x_305 = !lean_is_exclusive(x_288);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_311; 
x_306 = lean_ctor_get(x_288, 0);
x_307 = lean_ctor_get(x_288, 1);
x_308 = lean_ctor_get(x_288, 2);
x_309 = lean_ctor_get(x_288, 3);
x_310 = 1;
lean_inc(x_207);
lean_ctor_set(x_288, 3, x_306);
lean_ctor_set(x_288, 2, x_302);
lean_ctor_set(x_288, 1, x_301);
lean_ctor_set(x_288, 0, x_207);
x_311 = !lean_is_exclusive(x_207);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_312 = lean_ctor_get(x_207, 3);
lean_dec(x_312);
x_313 = lean_ctor_get(x_207, 2);
lean_dec(x_313);
x_314 = lean_ctor_get(x_207, 1);
lean_dec(x_314);
x_315 = lean_ctor_get(x_207, 0);
lean_dec(x_315);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
lean_ctor_set(x_207, 3, x_38);
lean_ctor_set(x_207, 2, x_37);
lean_ctor_set(x_207, 1, x_36);
lean_ctor_set(x_207, 0, x_309);
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_310);
x_316 = 0;
lean_ctor_set(x_206, 3, x_207);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_316);
return x_206;
}
else
{
lean_object* x_317; uint8_t x_318; 
lean_dec(x_207);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
x_317 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_36);
lean_ctor_set(x_317, 2, x_37);
lean_ctor_set(x_317, 3, x_38);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_310);
x_318 = 0;
lean_ctor_set(x_206, 3, x_317);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_318);
return x_206;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_319 = lean_ctor_get(x_288, 0);
x_320 = lean_ctor_get(x_288, 1);
x_321 = lean_ctor_get(x_288, 2);
x_322 = lean_ctor_get(x_288, 3);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_288);
x_323 = 1;
lean_inc(x_207);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_207);
lean_ctor_set(x_324, 1, x_301);
lean_ctor_set(x_324, 2, x_302);
lean_ctor_set(x_324, 3, x_319);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_325 = x_207;
} else {
 lean_dec_ref(x_207);
 x_325 = lean_box(0);
}
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_323);
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 4, 1);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_322);
lean_ctor_set(x_326, 1, x_36);
lean_ctor_set(x_326, 2, x_37);
lean_ctor_set(x_326, 3, x_38);
lean_ctor_set_uint8(x_326, sizeof(void*)*4, x_323);
x_327 = 0;
lean_ctor_set(x_206, 3, x_326);
lean_ctor_set(x_206, 2, x_321);
lean_ctor_set(x_206, 1, x_320);
lean_ctor_set(x_206, 0, x_324);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_327);
return x_206;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; 
x_328 = lean_ctor_get(x_206, 1);
x_329 = lean_ctor_get(x_206, 2);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_206);
x_330 = lean_ctor_get(x_288, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_288, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_288, 2);
lean_inc(x_332);
x_333 = lean_ctor_get(x_288, 3);
lean_inc(x_333);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 lean_ctor_release(x_288, 2);
 lean_ctor_release(x_288, 3);
 x_334 = x_288;
} else {
 lean_dec_ref(x_288);
 x_334 = lean_box(0);
}
x_335 = 1;
lean_inc(x_207);
if (lean_is_scalar(x_334)) {
 x_336 = lean_alloc_ctor(1, 4, 1);
} else {
 x_336 = x_334;
}
lean_ctor_set(x_336, 0, x_207);
lean_ctor_set(x_336, 1, x_328);
lean_ctor_set(x_336, 2, x_329);
lean_ctor_set(x_336, 3, x_330);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_337 = x_207;
} else {
 lean_dec_ref(x_207);
 x_337 = lean_box(0);
}
lean_ctor_set_uint8(x_336, sizeof(void*)*4, x_335);
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_36);
lean_ctor_set(x_338, 2, x_37);
lean_ctor_set(x_338, 3, x_38);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_335);
x_339 = 0;
x_340 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_340, 0, x_336);
lean_ctor_set(x_340, 1, x_331);
lean_ctor_set(x_340, 2, x_332);
lean_ctor_set(x_340, 3, x_338);
lean_ctor_set_uint8(x_340, sizeof(void*)*4, x_339);
return x_340;
}
}
else
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_206);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_342 = lean_ctor_get(x_206, 3);
lean_dec(x_342);
x_343 = lean_ctor_get(x_206, 0);
lean_dec(x_343);
x_344 = !lean_is_exclusive(x_207);
if (x_344 == 0)
{
uint8_t x_345; uint8_t x_346; 
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_299);
x_345 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_345);
x_346 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_346);
return x_1;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; uint8_t x_353; 
x_347 = lean_ctor_get(x_207, 0);
x_348 = lean_ctor_get(x_207, 1);
x_349 = lean_ctor_get(x_207, 2);
x_350 = lean_ctor_get(x_207, 3);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_207);
x_351 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_351, 0, x_347);
lean_ctor_set(x_351, 1, x_348);
lean_ctor_set(x_351, 2, x_349);
lean_ctor_set(x_351, 3, x_350);
lean_ctor_set_uint8(x_351, sizeof(void*)*4, x_299);
x_352 = 0;
lean_ctor_set(x_206, 0, x_351);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_352);
x_353 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_353);
return x_1;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; uint8_t x_364; 
x_354 = lean_ctor_get(x_206, 1);
x_355 = lean_ctor_get(x_206, 2);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_206);
x_356 = lean_ctor_get(x_207, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_207, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_207, 2);
lean_inc(x_358);
x_359 = lean_ctor_get(x_207, 3);
lean_inc(x_359);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_360 = x_207;
} else {
 lean_dec_ref(x_207);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 4, 1);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_356);
lean_ctor_set(x_361, 1, x_357);
lean_ctor_set(x_361, 2, x_358);
lean_ctor_set(x_361, 3, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_299);
x_362 = 0;
x_363 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_354);
lean_ctor_set(x_363, 2, x_355);
lean_ctor_set(x_363, 3, x_288);
lean_ctor_set_uint8(x_363, sizeof(void*)*4, x_362);
x_364 = 1;
lean_ctor_set(x_1, 0, x_363);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_364);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_365 = lean_ctor_get(x_1, 0);
x_366 = lean_ctor_get(x_1, 1);
x_367 = lean_ctor_get(x_1, 2);
x_368 = lean_ctor_get(x_1, 3);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_1);
lean_inc(x_366);
lean_inc(x_2);
x_369 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_2, x_366);
if (x_369 == 0)
{
uint8_t x_370; 
lean_inc(x_2);
lean_inc(x_366);
x_370 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_366, x_2);
if (x_370 == 0)
{
uint8_t x_371; lean_object* x_372; 
lean_dec(x_367);
lean_dec(x_366);
x_371 = 1;
x_372 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_372, 0, x_365);
lean_ctor_set(x_372, 1, x_2);
lean_ctor_set(x_372, 2, x_3);
lean_ctor_set(x_372, 3, x_368);
lean_ctor_set_uint8(x_372, sizeof(void*)*4, x_371);
return x_372;
}
else
{
uint8_t x_373; 
x_373 = l_Std_RBNode_isRed___rarg(x_368);
if (x_373 == 0)
{
lean_object* x_374; uint8_t x_375; lean_object* x_376; 
x_374 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__2(x_368, x_2, x_3);
x_375 = 1;
x_376 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_376, 0, x_365);
lean_ctor_set(x_376, 1, x_366);
lean_ctor_set(x_376, 2, x_367);
lean_ctor_set(x_376, 3, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_375);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; 
x_377 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__2(x_368, x_2, x_3);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_377, 3);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; 
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_377, 2);
lean_inc(x_381);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_382 = x_377;
} else {
 lean_dec_ref(x_377);
 x_382 = lean_box(0);
}
x_383 = 0;
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_379);
lean_ctor_set(x_384, 1, x_380);
lean_ctor_set(x_384, 2, x_381);
lean_ctor_set(x_384, 3, x_379);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_383);
x_385 = 1;
x_386 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_386, 0, x_365);
lean_ctor_set(x_386, 1, x_366);
lean_ctor_set(x_386, 2, x_367);
lean_ctor_set(x_386, 3, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
return x_386;
}
else
{
uint8_t x_387; 
x_387 = lean_ctor_get_uint8(x_379, sizeof(void*)*4);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; lean_object* x_400; 
x_388 = lean_ctor_get(x_377, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_377, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_390 = x_377;
} else {
 lean_dec_ref(x_377);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_379, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_379, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_379, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_379, 3);
lean_inc(x_394);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 lean_ctor_release(x_379, 3);
 x_395 = x_379;
} else {
 lean_dec_ref(x_379);
 x_395 = lean_box(0);
}
x_396 = 1;
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_395;
}
lean_ctor_set(x_397, 0, x_365);
lean_ctor_set(x_397, 1, x_366);
lean_ctor_set(x_397, 2, x_367);
lean_ctor_set(x_397, 3, x_378);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_396);
if (lean_is_scalar(x_390)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_390;
}
lean_ctor_set(x_398, 0, x_391);
lean_ctor_set(x_398, 1, x_392);
lean_ctor_set(x_398, 2, x_393);
lean_ctor_set(x_398, 3, x_394);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_396);
x_399 = 0;
x_400 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_388);
lean_ctor_set(x_400, 2, x_389);
lean_ctor_set(x_400, 3, x_398);
lean_ctor_set_uint8(x_400, sizeof(void*)*4, x_399);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_401 = lean_ctor_get(x_377, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_377, 2);
lean_inc(x_402);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_403 = x_377;
} else {
 lean_dec_ref(x_377);
 x_403 = lean_box(0);
}
x_404 = 0;
if (lean_is_scalar(x_403)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_403;
}
lean_ctor_set(x_405, 0, x_378);
lean_ctor_set(x_405, 1, x_401);
lean_ctor_set(x_405, 2, x_402);
lean_ctor_set(x_405, 3, x_379);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_404);
x_406 = 1;
x_407 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_407, 0, x_365);
lean_ctor_set(x_407, 1, x_366);
lean_ctor_set(x_407, 2, x_367);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
}
}
else
{
uint8_t x_408; 
x_408 = lean_ctor_get_uint8(x_378, sizeof(void*)*4);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; 
x_409 = lean_ctor_get(x_377, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_377, 2);
lean_inc(x_410);
x_411 = lean_ctor_get(x_377, 3);
lean_inc(x_411);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_412 = x_377;
} else {
 lean_dec_ref(x_377);
 x_412 = lean_box(0);
}
x_413 = lean_ctor_get(x_378, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_378, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_378, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_378, 3);
lean_inc(x_416);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_417 = x_378;
} else {
 lean_dec_ref(x_378);
 x_417 = lean_box(0);
}
x_418 = 1;
if (lean_is_scalar(x_417)) {
 x_419 = lean_alloc_ctor(1, 4, 1);
} else {
 x_419 = x_417;
}
lean_ctor_set(x_419, 0, x_365);
lean_ctor_set(x_419, 1, x_366);
lean_ctor_set(x_419, 2, x_367);
lean_ctor_set(x_419, 3, x_413);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
if (lean_is_scalar(x_412)) {
 x_420 = lean_alloc_ctor(1, 4, 1);
} else {
 x_420 = x_412;
}
lean_ctor_set(x_420, 0, x_416);
lean_ctor_set(x_420, 1, x_409);
lean_ctor_set(x_420, 2, x_410);
lean_ctor_set(x_420, 3, x_411);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_418);
x_421 = 0;
x_422 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_414);
lean_ctor_set(x_422, 2, x_415);
lean_ctor_set(x_422, 3, x_420);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
return x_422;
}
else
{
lean_object* x_423; 
x_423 = lean_ctor_get(x_377, 3);
lean_inc(x_423);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; 
x_424 = lean_ctor_get(x_377, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_377, 2);
lean_inc(x_425);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_426 = x_377;
} else {
 lean_dec_ref(x_377);
 x_426 = lean_box(0);
}
x_427 = 0;
if (lean_is_scalar(x_426)) {
 x_428 = lean_alloc_ctor(1, 4, 1);
} else {
 x_428 = x_426;
}
lean_ctor_set(x_428, 0, x_378);
lean_ctor_set(x_428, 1, x_424);
lean_ctor_set(x_428, 2, x_425);
lean_ctor_set(x_428, 3, x_423);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
x_429 = 1;
x_430 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_430, 0, x_365);
lean_ctor_set(x_430, 1, x_366);
lean_ctor_set(x_430, 2, x_367);
lean_ctor_set(x_430, 3, x_428);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_429);
return x_430;
}
else
{
uint8_t x_431; 
x_431 = lean_ctor_get_uint8(x_423, sizeof(void*)*4);
if (x_431 == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; 
x_432 = lean_ctor_get(x_377, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_377, 2);
lean_inc(x_433);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_434 = x_377;
} else {
 lean_dec_ref(x_377);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_423, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_423, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_423, 2);
lean_inc(x_437);
x_438 = lean_ctor_get(x_423, 3);
lean_inc(x_438);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 lean_ctor_release(x_423, 2);
 lean_ctor_release(x_423, 3);
 x_439 = x_423;
} else {
 lean_dec_ref(x_423);
 x_439 = lean_box(0);
}
x_440 = 1;
lean_inc(x_378);
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(1, 4, 1);
} else {
 x_441 = x_439;
}
lean_ctor_set(x_441, 0, x_365);
lean_ctor_set(x_441, 1, x_366);
lean_ctor_set(x_441, 2, x_367);
lean_ctor_set(x_441, 3, x_378);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_442 = x_378;
} else {
 lean_dec_ref(x_378);
 x_442 = lean_box(0);
}
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_440);
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_435);
lean_ctor_set(x_443, 1, x_436);
lean_ctor_set(x_443, 2, x_437);
lean_ctor_set(x_443, 3, x_438);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_440);
x_444 = 0;
if (lean_is_scalar(x_434)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_434;
}
lean_ctor_set(x_445, 0, x_441);
lean_ctor_set(x_445, 1, x_432);
lean_ctor_set(x_445, 2, x_433);
lean_ctor_set(x_445, 3, x_443);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_444);
return x_445;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_446 = lean_ctor_get(x_377, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_377, 2);
lean_inc(x_447);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_448 = x_377;
} else {
 lean_dec_ref(x_377);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_378, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_378, 1);
lean_inc(x_450);
x_451 = lean_ctor_get(x_378, 2);
lean_inc(x_451);
x_452 = lean_ctor_get(x_378, 3);
lean_inc(x_452);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_453 = x_378;
} else {
 lean_dec_ref(x_378);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_449);
lean_ctor_set(x_454, 1, x_450);
lean_ctor_set(x_454, 2, x_451);
lean_ctor_set(x_454, 3, x_452);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_431);
x_455 = 0;
if (lean_is_scalar(x_448)) {
 x_456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_456 = x_448;
}
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_446);
lean_ctor_set(x_456, 2, x_447);
lean_ctor_set(x_456, 3, x_423);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_365);
lean_ctor_set(x_458, 1, x_366);
lean_ctor_set(x_458, 2, x_367);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
}
}
}
}
}
}
else
{
uint8_t x_459; 
x_459 = l_Std_RBNode_isRed___rarg(x_365);
if (x_459 == 0)
{
lean_object* x_460; uint8_t x_461; lean_object* x_462; 
x_460 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__2(x_365, x_2, x_3);
x_461 = 1;
x_462 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_366);
lean_ctor_set(x_462, 2, x_367);
lean_ctor_set(x_462, 3, x_368);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
return x_462;
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__2(x_365, x_2, x_3);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; 
x_465 = lean_ctor_get(x_463, 3);
lean_inc(x_465);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; 
x_466 = lean_ctor_get(x_463, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_463, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_468 = x_463;
} else {
 lean_dec_ref(x_463);
 x_468 = lean_box(0);
}
x_469 = 0;
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(1, 4, 1);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_465);
lean_ctor_set(x_470, 1, x_466);
lean_ctor_set(x_470, 2, x_467);
lean_ctor_set(x_470, 3, x_465);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
x_471 = 1;
x_472 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_366);
lean_ctor_set(x_472, 2, x_367);
lean_ctor_set(x_472, 3, x_368);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_471);
return x_472;
}
else
{
uint8_t x_473; 
x_473 = lean_ctor_get_uint8(x_465, sizeof(void*)*4);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; 
x_474 = lean_ctor_get(x_463, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_463, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_476 = x_463;
} else {
 lean_dec_ref(x_463);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_465, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_465, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_465, 2);
lean_inc(x_479);
x_480 = lean_ctor_get(x_465, 3);
lean_inc(x_480);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 lean_ctor_release(x_465, 3);
 x_481 = x_465;
} else {
 lean_dec_ref(x_465);
 x_481 = lean_box(0);
}
x_482 = 1;
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_464);
lean_ctor_set(x_483, 1, x_474);
lean_ctor_set(x_483, 2, x_475);
lean_ctor_set(x_483, 3, x_477);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_482);
if (lean_is_scalar(x_476)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_476;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_366);
lean_ctor_set(x_484, 2, x_367);
lean_ctor_set(x_484, 3, x_368);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_482);
x_485 = 0;
x_486 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_478);
lean_ctor_set(x_486, 2, x_479);
lean_ctor_set(x_486, 3, x_484);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_485);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; 
x_487 = lean_ctor_get(x_463, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_463, 2);
lean_inc(x_488);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_489 = x_463;
} else {
 lean_dec_ref(x_463);
 x_489 = lean_box(0);
}
x_490 = 0;
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(1, 4, 1);
} else {
 x_491 = x_489;
}
lean_ctor_set(x_491, 0, x_464);
lean_ctor_set(x_491, 1, x_487);
lean_ctor_set(x_491, 2, x_488);
lean_ctor_set(x_491, 3, x_465);
lean_ctor_set_uint8(x_491, sizeof(void*)*4, x_490);
x_492 = 1;
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_366);
lean_ctor_set(x_493, 2, x_367);
lean_ctor_set(x_493, 3, x_368);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_492);
return x_493;
}
}
}
else
{
uint8_t x_494; 
x_494 = lean_ctor_get_uint8(x_464, sizeof(void*)*4);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; 
x_495 = lean_ctor_get(x_463, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_463, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_463, 3);
lean_inc(x_497);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_498 = x_463;
} else {
 lean_dec_ref(x_463);
 x_498 = lean_box(0);
}
x_499 = lean_ctor_get(x_464, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_464, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_464, 2);
lean_inc(x_501);
x_502 = lean_ctor_get(x_464, 3);
lean_inc(x_502);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_503 = x_464;
} else {
 lean_dec_ref(x_464);
 x_503 = lean_box(0);
}
x_504 = 1;
if (lean_is_scalar(x_503)) {
 x_505 = lean_alloc_ctor(1, 4, 1);
} else {
 x_505 = x_503;
}
lean_ctor_set(x_505, 0, x_499);
lean_ctor_set(x_505, 1, x_500);
lean_ctor_set(x_505, 2, x_501);
lean_ctor_set(x_505, 3, x_502);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
if (lean_is_scalar(x_498)) {
 x_506 = lean_alloc_ctor(1, 4, 1);
} else {
 x_506 = x_498;
}
lean_ctor_set(x_506, 0, x_497);
lean_ctor_set(x_506, 1, x_366);
lean_ctor_set(x_506, 2, x_367);
lean_ctor_set(x_506, 3, x_368);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_504);
x_507 = 0;
x_508 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_495);
lean_ctor_set(x_508, 2, x_496);
lean_ctor_set(x_508, 3, x_506);
lean_ctor_set_uint8(x_508, sizeof(void*)*4, x_507);
return x_508;
}
else
{
lean_object* x_509; 
x_509 = lean_ctor_get(x_463, 3);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; 
x_510 = lean_ctor_get(x_463, 1);
lean_inc(x_510);
x_511 = lean_ctor_get(x_463, 2);
lean_inc(x_511);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_512 = x_463;
} else {
 lean_dec_ref(x_463);
 x_512 = lean_box(0);
}
x_513 = 0;
if (lean_is_scalar(x_512)) {
 x_514 = lean_alloc_ctor(1, 4, 1);
} else {
 x_514 = x_512;
}
lean_ctor_set(x_514, 0, x_464);
lean_ctor_set(x_514, 1, x_510);
lean_ctor_set(x_514, 2, x_511);
lean_ctor_set(x_514, 3, x_509);
lean_ctor_set_uint8(x_514, sizeof(void*)*4, x_513);
x_515 = 1;
x_516 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_366);
lean_ctor_set(x_516, 2, x_367);
lean_ctor_set(x_516, 3, x_368);
lean_ctor_set_uint8(x_516, sizeof(void*)*4, x_515);
return x_516;
}
else
{
uint8_t x_517; 
x_517 = lean_ctor_get_uint8(x_509, sizeof(void*)*4);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; lean_object* x_531; 
x_518 = lean_ctor_get(x_463, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_463, 2);
lean_inc(x_519);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_520 = x_463;
} else {
 lean_dec_ref(x_463);
 x_520 = lean_box(0);
}
x_521 = lean_ctor_get(x_509, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_509, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_509, 2);
lean_inc(x_523);
x_524 = lean_ctor_get(x_509, 3);
lean_inc(x_524);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 lean_ctor_release(x_509, 2);
 lean_ctor_release(x_509, 3);
 x_525 = x_509;
} else {
 lean_dec_ref(x_509);
 x_525 = lean_box(0);
}
x_526 = 1;
lean_inc(x_464);
if (lean_is_scalar(x_525)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_525;
}
lean_ctor_set(x_527, 0, x_464);
lean_ctor_set(x_527, 1, x_518);
lean_ctor_set(x_527, 2, x_519);
lean_ctor_set(x_527, 3, x_521);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_528 = x_464;
} else {
 lean_dec_ref(x_464);
 x_528 = lean_box(0);
}
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 4, 1);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_524);
lean_ctor_set(x_529, 1, x_366);
lean_ctor_set(x_529, 2, x_367);
lean_ctor_set(x_529, 3, x_368);
lean_ctor_set_uint8(x_529, sizeof(void*)*4, x_526);
x_530 = 0;
if (lean_is_scalar(x_520)) {
 x_531 = lean_alloc_ctor(1, 4, 1);
} else {
 x_531 = x_520;
}
lean_ctor_set(x_531, 0, x_527);
lean_ctor_set(x_531, 1, x_522);
lean_ctor_set(x_531, 2, x_523);
lean_ctor_set(x_531, 3, x_529);
lean_ctor_set_uint8(x_531, sizeof(void*)*4, x_530);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; 
x_532 = lean_ctor_get(x_463, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_463, 2);
lean_inc(x_533);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_534 = x_463;
} else {
 lean_dec_ref(x_463);
 x_534 = lean_box(0);
}
x_535 = lean_ctor_get(x_464, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_464, 1);
lean_inc(x_536);
x_537 = lean_ctor_get(x_464, 2);
lean_inc(x_537);
x_538 = lean_ctor_get(x_464, 3);
lean_inc(x_538);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_539 = x_464;
} else {
 lean_dec_ref(x_464);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 4, 1);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_535);
lean_ctor_set(x_540, 1, x_536);
lean_ctor_set(x_540, 2, x_537);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_517);
x_541 = 0;
if (lean_is_scalar(x_534)) {
 x_542 = lean_alloc_ctor(1, 4, 1);
} else {
 x_542 = x_534;
}
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_532);
lean_ctor_set(x_542, 2, x_533);
lean_ctor_set(x_542, 3, x_509);
lean_ctor_set_uint8(x_542, sizeof(void*)*4, x_541);
x_543 = 1;
x_544 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_366);
lean_ctor_set(x_544, 2, x_367);
lean_ctor_set(x_544, 3, x_368);
lean_ctor_set_uint8(x_544, sizeof(void*)*4, x_543);
return x_544;
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
}
lean_object* l_Std_RBNode_insert___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__2(x_1, x_2, x_3);
x_7 = l_Std_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_writeRequest___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
x_5 = l_Lean_Server_Watchdog_FileWorker_stdin(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_IO_FS_Stream_writeLspRequest___rarg(x_1, x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_st_ref_take(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l_Lean_Json_toStructured_x3f___rarg(x_1, x_14);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_15);
x_17 = l_Std_RBNode_insert___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__1(x_10, x_12, x_16);
x_18 = lean_st_ref_set(x_8, x_17, x_11);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_writeRequest(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_writeRequest___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__2___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__2___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests_match__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1(x_1, x_2, x_3, x_9, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_box(0);
lean_inc(x_3);
lean_inc(x_10);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_2);
lean_inc(x_1);
x_21 = l_IO_FS_Stream_writeLspResponseError(x_1, x_20, x_18);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_4 = x_11;
x_5 = x_23;
x_6 = x_22;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_1, 4);
x_7 = lean_st_ref_take(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = lean_st_ref_set(x_6, x_10, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1(x_2, x_3, x_4, x_8, x_13, x_12);
lean_dec(x_8);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_FileWorker_errorPendingRequests___spec__1(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_8;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_errorPendingRequests___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_string_dec_lt(x_2, x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_string_dec_lt(x_10, x_2);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_10);
x_15 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_12, x_2, x_3);
x_17 = 0;
lean_ctor_set(x_1, 3, x_16);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_17);
return x_1;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_9, x_2, x_3);
x_19 = 0;
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_string_dec_lt(x_2, x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_string_dec_lt(x_21, x_2);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_21);
x_26 = 0;
x_27 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 2, x_3);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_26);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_23, x_2, x_3);
x_29 = 0;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_21);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_20, x_2, x_3);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_string_dec_lt(x_2, x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = lean_string_dec_lt(x_36, x_2);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_37);
lean_dec(x_36);
x_41 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_41);
return x_1;
}
else
{
uint8_t x_42; 
x_42 = l_Std_RBNode_isRed___rarg(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_38, x_2, x_3);
x_44 = 1;
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_44);
return x_1;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_38, x_2, x_3);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 3);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_45, 3);
lean_dec(x_49);
x_50 = lean_ctor_get(x_45, 0);
lean_dec(x_50);
x_51 = 0;
lean_ctor_set(x_45, 0, x_47);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_51);
x_52 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_52);
return x_1;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_45, 1);
x_54 = lean_ctor_get(x_45, 2);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_45);
x_55 = 0;
x_56 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_54);
lean_ctor_set(x_56, 3, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_55);
x_57 = 1;
lean_ctor_set(x_1, 3, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_57);
return x_1;
}
}
else
{
uint8_t x_58; 
x_58 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_45);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_45, 1);
x_61 = lean_ctor_get(x_45, 2);
x_62 = lean_ctor_get(x_45, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_45, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_47);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_47, 0);
x_66 = lean_ctor_get(x_47, 1);
x_67 = lean_ctor_get(x_47, 2);
x_68 = lean_ctor_get(x_47, 3);
x_69 = 1;
lean_ctor_set(x_47, 3, x_46);
lean_ctor_set(x_47, 2, x_37);
lean_ctor_set(x_47, 1, x_36);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_69);
lean_ctor_set(x_45, 3, x_68);
lean_ctor_set(x_45, 2, x_67);
lean_ctor_set(x_45, 1, x_66);
lean_ctor_set(x_45, 0, x_65);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_69);
x_70 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_61);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_70);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; 
x_71 = lean_ctor_get(x_47, 0);
x_72 = lean_ctor_get(x_47, 1);
x_73 = lean_ctor_get(x_47, 2);
x_74 = lean_ctor_get(x_47, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_47);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_35);
lean_ctor_set(x_76, 1, x_36);
lean_ctor_set(x_76, 2, x_37);
lean_ctor_set(x_76, 3, x_46);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_45, 3, x_74);
lean_ctor_set(x_45, 2, x_73);
lean_ctor_set(x_45, 1, x_72);
lean_ctor_set(x_45, 0, x_71);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_75);
x_77 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_61);
lean_ctor_set(x_1, 1, x_60);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_77);
return x_1;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_78 = lean_ctor_get(x_45, 1);
x_79 = lean_ctor_get(x_45, 2);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_45);
x_80 = lean_ctor_get(x_47, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_47, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_47, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_47, 3);
lean_inc(x_83);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_84 = x_47;
} else {
 lean_dec_ref(x_47);
 x_84 = lean_box(0);
}
x_85 = 1;
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(1, 4, 1);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_35);
lean_ctor_set(x_86, 1, x_36);
lean_ctor_set(x_86, 2, x_37);
lean_ctor_set(x_86, 3, x_46);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_85);
x_87 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set(x_87, 2, x_82);
lean_ctor_set(x_87, 3, x_83);
lean_ctor_set_uint8(x_87, sizeof(void*)*4, x_85);
x_88 = 0;
lean_ctor_set(x_1, 3, x_87);
lean_ctor_set(x_1, 2, x_79);
lean_ctor_set(x_1, 1, x_78);
lean_ctor_set(x_1, 0, x_86);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_88);
return x_1;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_45);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_45, 3);
lean_dec(x_90);
x_91 = lean_ctor_get(x_45, 0);
lean_dec(x_91);
x_92 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_92);
x_93 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_93);
return x_1;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_45, 1);
x_95 = lean_ctor_get(x_45, 2);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_45);
x_96 = 0;
x_97 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_97, 0, x_46);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_47);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_96);
x_98 = 1;
lean_ctor_set(x_1, 3, x_97);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_98);
return x_1;
}
}
}
}
else
{
uint8_t x_99; 
x_99 = lean_ctor_get_uint8(x_46, sizeof(void*)*4);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_45);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_45, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_46);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; 
x_103 = lean_ctor_get(x_46, 0);
x_104 = lean_ctor_get(x_46, 1);
x_105 = lean_ctor_get(x_46, 2);
x_106 = lean_ctor_get(x_46, 3);
x_107 = 1;
lean_ctor_set(x_46, 3, x_103);
lean_ctor_set(x_46, 2, x_37);
lean_ctor_set(x_46, 1, x_36);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_107);
lean_ctor_set(x_45, 0, x_106);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_107);
x_108 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_105);
lean_ctor_set(x_1, 1, x_104);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_108);
return x_1;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; uint8_t x_115; 
x_109 = lean_ctor_get(x_46, 0);
x_110 = lean_ctor_get(x_46, 1);
x_111 = lean_ctor_get(x_46, 2);
x_112 = lean_ctor_get(x_46, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_46);
x_113 = 1;
x_114 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_114, 0, x_35);
lean_ctor_set(x_114, 1, x_36);
lean_ctor_set(x_114, 2, x_37);
lean_ctor_set(x_114, 3, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
lean_ctor_set(x_45, 0, x_112);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_113);
x_115 = 0;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set(x_1, 2, x_111);
lean_ctor_set(x_1, 1, x_110);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_115);
return x_1;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_116 = lean_ctor_get(x_45, 1);
x_117 = lean_ctor_get(x_45, 2);
x_118 = lean_ctor_get(x_45, 3);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_45);
x_119 = lean_ctor_get(x_46, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_46, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_46, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_46, 3);
lean_inc(x_122);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_123 = x_46;
} else {
 lean_dec_ref(x_46);
 x_123 = lean_box(0);
}
x_124 = 1;
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(1, 4, 1);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_35);
lean_ctor_set(x_125, 1, x_36);
lean_ctor_set(x_125, 2, x_37);
lean_ctor_set(x_125, 3, x_119);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_116);
lean_ctor_set(x_126, 2, x_117);
lean_ctor_set(x_126, 3, x_118);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_124);
x_127 = 0;
lean_ctor_set(x_1, 3, x_126);
lean_ctor_set(x_1, 2, x_121);
lean_ctor_set(x_1, 1, x_120);
lean_ctor_set(x_1, 0, x_125);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
return x_1;
}
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_45, 3);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_45);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_45, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_45, 0);
lean_dec(x_131);
x_132 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_132);
x_133 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_133);
return x_1;
}
else
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; uint8_t x_138; 
x_134 = lean_ctor_get(x_45, 1);
x_135 = lean_ctor_get(x_45, 2);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_45);
x_136 = 0;
x_137 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_137, 0, x_46);
lean_ctor_set(x_137, 1, x_134);
lean_ctor_set(x_137, 2, x_135);
lean_ctor_set(x_137, 3, x_128);
lean_ctor_set_uint8(x_137, sizeof(void*)*4, x_136);
x_138 = 1;
lean_ctor_set(x_1, 3, x_137);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_138);
return x_1;
}
}
else
{
uint8_t x_139; 
x_139 = lean_ctor_get_uint8(x_128, sizeof(void*)*4);
if (x_139 == 0)
{
uint8_t x_140; 
lean_free_object(x_1);
x_140 = !lean_is_exclusive(x_45);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_45, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_45, 0);
lean_dec(x_142);
x_143 = !lean_is_exclusive(x_128);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_149; 
x_144 = lean_ctor_get(x_128, 0);
x_145 = lean_ctor_get(x_128, 1);
x_146 = lean_ctor_get(x_128, 2);
x_147 = lean_ctor_get(x_128, 3);
x_148 = 1;
lean_inc(x_46);
lean_ctor_set(x_128, 3, x_46);
lean_ctor_set(x_128, 2, x_37);
lean_ctor_set(x_128, 1, x_36);
lean_ctor_set(x_128, 0, x_35);
x_149 = !lean_is_exclusive(x_46);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_150 = lean_ctor_get(x_46, 3);
lean_dec(x_150);
x_151 = lean_ctor_get(x_46, 2);
lean_dec(x_151);
x_152 = lean_ctor_get(x_46, 1);
lean_dec(x_152);
x_153 = lean_ctor_get(x_46, 0);
lean_dec(x_153);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_148);
lean_ctor_set(x_46, 3, x_147);
lean_ctor_set(x_46, 2, x_146);
lean_ctor_set(x_46, 1, x_145);
lean_ctor_set(x_46, 0, x_144);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_148);
x_154 = 0;
lean_ctor_set(x_45, 3, x_46);
lean_ctor_set(x_45, 0, x_128);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_154);
return x_45;
}
else
{
lean_object* x_155; uint8_t x_156; 
lean_dec(x_46);
lean_ctor_set_uint8(x_128, sizeof(void*)*4, x_148);
x_155 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_155, 0, x_144);
lean_ctor_set(x_155, 1, x_145);
lean_ctor_set(x_155, 2, x_146);
lean_ctor_set(x_155, 3, x_147);
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_148);
x_156 = 0;
lean_ctor_set(x_45, 3, x_155);
lean_ctor_set(x_45, 0, x_128);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_156);
return x_45;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_157 = lean_ctor_get(x_128, 0);
x_158 = lean_ctor_get(x_128, 1);
x_159 = lean_ctor_get(x_128, 2);
x_160 = lean_ctor_get(x_128, 3);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_128);
x_161 = 1;
lean_inc(x_46);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_35);
lean_ctor_set(x_162, 1, x_36);
lean_ctor_set(x_162, 2, x_37);
lean_ctor_set(x_162, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_163 = x_46;
} else {
 lean_dec_ref(x_46);
 x_163 = lean_box(0);
}
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_161);
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 4, 1);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_157);
lean_ctor_set(x_164, 1, x_158);
lean_ctor_set(x_164, 2, x_159);
lean_ctor_set(x_164, 3, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_161);
x_165 = 0;
lean_ctor_set(x_45, 3, x_164);
lean_ctor_set(x_45, 0, x_162);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_165);
return x_45;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; 
x_166 = lean_ctor_get(x_45, 1);
x_167 = lean_ctor_get(x_45, 2);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_45);
x_168 = lean_ctor_get(x_128, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_128, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_128, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_128, 3);
lean_inc(x_171);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 x_172 = x_128;
} else {
 lean_dec_ref(x_128);
 x_172 = lean_box(0);
}
x_173 = 1;
lean_inc(x_46);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(1, 4, 1);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_35);
lean_ctor_set(x_174, 1, x_36);
lean_ctor_set(x_174, 2, x_37);
lean_ctor_set(x_174, 3, x_46);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_175 = x_46;
} else {
 lean_dec_ref(x_46);
 x_175 = lean_box(0);
}
lean_ctor_set_uint8(x_174, sizeof(void*)*4, x_173);
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 4, 1);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_169);
lean_ctor_set(x_176, 2, x_170);
lean_ctor_set(x_176, 3, x_171);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_173);
x_177 = 0;
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_166);
lean_ctor_set(x_178, 2, x_167);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_177);
return x_178;
}
}
else
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_45);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_45, 3);
lean_dec(x_180);
x_181 = lean_ctor_get(x_45, 0);
lean_dec(x_181);
x_182 = !lean_is_exclusive(x_46);
if (x_182 == 0)
{
uint8_t x_183; uint8_t x_184; 
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_139);
x_183 = 0;
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_183);
x_184 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_184);
return x_1;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; 
x_185 = lean_ctor_get(x_46, 0);
x_186 = lean_ctor_get(x_46, 1);
x_187 = lean_ctor_get(x_46, 2);
x_188 = lean_ctor_get(x_46, 3);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_46);
x_189 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_189, 1, x_186);
lean_ctor_set(x_189, 2, x_187);
lean_ctor_set(x_189, 3, x_188);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_139);
x_190 = 0;
lean_ctor_set(x_45, 0, x_189);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_190);
x_191 = 1;
lean_ctor_set(x_1, 3, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_191);
return x_1;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; uint8_t x_202; 
x_192 = lean_ctor_get(x_45, 1);
x_193 = lean_ctor_get(x_45, 2);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_45);
x_194 = lean_ctor_get(x_46, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_46, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_46, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_46, 3);
lean_inc(x_197);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_198 = x_46;
} else {
 lean_dec_ref(x_46);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 4, 1);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_194);
lean_ctor_set(x_199, 1, x_195);
lean_ctor_set(x_199, 2, x_196);
lean_ctor_set(x_199, 3, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*4, x_139);
x_200 = 0;
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_192);
lean_ctor_set(x_201, 2, x_193);
lean_ctor_set(x_201, 3, x_128);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_200);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
}
}
}
}
}
}
else
{
uint8_t x_203; 
x_203 = l_Std_RBNode_isRed___rarg(x_35);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_35, x_2, x_3);
x_205 = 1;
lean_ctor_set(x_1, 0, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_205);
return x_1;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_35, x_2, x_3);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_206, 3);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_206);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_206, 3);
lean_dec(x_210);
x_211 = lean_ctor_get(x_206, 0);
lean_dec(x_211);
x_212 = 0;
lean_ctor_set(x_206, 0, x_208);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_212);
x_213 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_213);
return x_1;
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_206, 1);
x_215 = lean_ctor_get(x_206, 2);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_206);
x_216 = 0;
x_217 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_217, 0, x_208);
lean_ctor_set(x_217, 1, x_214);
lean_ctor_set(x_217, 2, x_215);
lean_ctor_set(x_217, 3, x_208);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_216);
x_218 = 1;
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_218);
return x_1;
}
}
else
{
uint8_t x_219; 
x_219 = lean_ctor_get_uint8(x_208, sizeof(void*)*4);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_206);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_206, 1);
x_222 = lean_ctor_get(x_206, 2);
x_223 = lean_ctor_get(x_206, 3);
lean_dec(x_223);
x_224 = lean_ctor_get(x_206, 0);
lean_dec(x_224);
x_225 = !lean_is_exclusive(x_208);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; 
x_226 = lean_ctor_get(x_208, 0);
x_227 = lean_ctor_get(x_208, 1);
x_228 = lean_ctor_get(x_208, 2);
x_229 = lean_ctor_get(x_208, 3);
x_230 = 1;
lean_ctor_set(x_208, 3, x_226);
lean_ctor_set(x_208, 2, x_222);
lean_ctor_set(x_208, 1, x_221);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_230);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_229);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_230);
x_231 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_231);
return x_1;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; uint8_t x_238; 
x_232 = lean_ctor_get(x_208, 0);
x_233 = lean_ctor_get(x_208, 1);
x_234 = lean_ctor_get(x_208, 2);
x_235 = lean_ctor_get(x_208, 3);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_208);
x_236 = 1;
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_207);
lean_ctor_set(x_237, 1, x_221);
lean_ctor_set(x_237, 2, x_222);
lean_ctor_set(x_237, 3, x_232);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_236);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_235);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_236);
x_238 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_234);
lean_ctor_set(x_1, 1, x_233);
lean_ctor_set(x_1, 0, x_237);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_238);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_239 = lean_ctor_get(x_206, 1);
x_240 = lean_ctor_get(x_206, 2);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_206);
x_241 = lean_ctor_get(x_208, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_208, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_208, 2);
lean_inc(x_243);
x_244 = lean_ctor_get(x_208, 3);
lean_inc(x_244);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 lean_ctor_release(x_208, 3);
 x_245 = x_208;
} else {
 lean_dec_ref(x_208);
 x_245 = lean_box(0);
}
x_246 = 1;
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(1, 4, 1);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_207);
lean_ctor_set(x_247, 1, x_239);
lean_ctor_set(x_247, 2, x_240);
lean_ctor_set(x_247, 3, x_241);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
x_248 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_248, 0, x_244);
lean_ctor_set(x_248, 1, x_36);
lean_ctor_set(x_248, 2, x_37);
lean_ctor_set(x_248, 3, x_38);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_246);
x_249 = 0;
lean_ctor_set(x_1, 3, x_248);
lean_ctor_set(x_1, 2, x_243);
lean_ctor_set(x_1, 1, x_242);
lean_ctor_set(x_1, 0, x_247);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_249);
return x_1;
}
}
else
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_206);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_254; 
x_251 = lean_ctor_get(x_206, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_206, 0);
lean_dec(x_252);
x_253 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_253);
x_254 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_254);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_255 = lean_ctor_get(x_206, 1);
x_256 = lean_ctor_get(x_206, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_206);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_207);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_208);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
x_259 = 1;
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
else
{
uint8_t x_260; 
x_260 = lean_ctor_get_uint8(x_207, sizeof(void*)*4);
if (x_260 == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_206);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_262 = lean_ctor_get(x_206, 1);
x_263 = lean_ctor_get(x_206, 2);
x_264 = lean_ctor_get(x_206, 3);
x_265 = lean_ctor_get(x_206, 0);
lean_dec(x_265);
x_266 = !lean_is_exclusive(x_207);
if (x_266 == 0)
{
uint8_t x_267; uint8_t x_268; 
x_267 = 1;
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_267);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_267);
x_268 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_207);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_268);
return x_1;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; uint8_t x_275; 
x_269 = lean_ctor_get(x_207, 0);
x_270 = lean_ctor_get(x_207, 1);
x_271 = lean_ctor_get(x_207, 2);
x_272 = lean_ctor_get(x_207, 3);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_207);
x_273 = 1;
x_274 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set(x_274, 1, x_270);
lean_ctor_set(x_274, 2, x_271);
lean_ctor_set(x_274, 3, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*4, x_273);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_273);
x_275 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_274);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_275);
return x_1;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_276 = lean_ctor_get(x_206, 1);
x_277 = lean_ctor_get(x_206, 2);
x_278 = lean_ctor_get(x_206, 3);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_206);
x_279 = lean_ctor_get(x_207, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_207, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_207, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_207, 3);
lean_inc(x_282);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_283 = x_207;
} else {
 lean_dec_ref(x_207);
 x_283 = lean_box(0);
}
x_284 = 1;
if (lean_is_scalar(x_283)) {
 x_285 = lean_alloc_ctor(1, 4, 1);
} else {
 x_285 = x_283;
}
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_280);
lean_ctor_set(x_285, 2, x_281);
lean_ctor_set(x_285, 3, x_282);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_284);
x_286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_286, 0, x_278);
lean_ctor_set(x_286, 1, x_36);
lean_ctor_set(x_286, 2, x_37);
lean_ctor_set(x_286, 3, x_38);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_284);
x_287 = 0;
lean_ctor_set(x_1, 3, x_286);
lean_ctor_set(x_1, 2, x_277);
lean_ctor_set(x_1, 1, x_276);
lean_ctor_set(x_1, 0, x_285);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_287);
return x_1;
}
}
else
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_206, 3);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_206);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; 
x_290 = lean_ctor_get(x_206, 3);
lean_dec(x_290);
x_291 = lean_ctor_get(x_206, 0);
lean_dec(x_291);
x_292 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_292);
x_293 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_293);
return x_1;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_206, 1);
x_295 = lean_ctor_get(x_206, 2);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_206);
x_296 = 0;
x_297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_297, 0, x_207);
lean_ctor_set(x_297, 1, x_294);
lean_ctor_set(x_297, 2, x_295);
lean_ctor_set(x_297, 3, x_288);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_296);
x_298 = 1;
lean_ctor_set(x_1, 0, x_297);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_298);
return x_1;
}
}
else
{
uint8_t x_299; 
x_299 = lean_ctor_get_uint8(x_288, sizeof(void*)*4);
if (x_299 == 0)
{
uint8_t x_300; 
lean_free_object(x_1);
x_300 = !lean_is_exclusive(x_206);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_301 = lean_ctor_get(x_206, 1);
x_302 = lean_ctor_get(x_206, 2);
x_303 = lean_ctor_get(x_206, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_206, 0);
lean_dec(x_304);
x_305 = !lean_is_exclusive(x_288);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_311; 
x_306 = lean_ctor_get(x_288, 0);
x_307 = lean_ctor_get(x_288, 1);
x_308 = lean_ctor_get(x_288, 2);
x_309 = lean_ctor_get(x_288, 3);
x_310 = 1;
lean_inc(x_207);
lean_ctor_set(x_288, 3, x_306);
lean_ctor_set(x_288, 2, x_302);
lean_ctor_set(x_288, 1, x_301);
lean_ctor_set(x_288, 0, x_207);
x_311 = !lean_is_exclusive(x_207);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_312 = lean_ctor_get(x_207, 3);
lean_dec(x_312);
x_313 = lean_ctor_get(x_207, 2);
lean_dec(x_313);
x_314 = lean_ctor_get(x_207, 1);
lean_dec(x_314);
x_315 = lean_ctor_get(x_207, 0);
lean_dec(x_315);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
lean_ctor_set(x_207, 3, x_38);
lean_ctor_set(x_207, 2, x_37);
lean_ctor_set(x_207, 1, x_36);
lean_ctor_set(x_207, 0, x_309);
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_310);
x_316 = 0;
lean_ctor_set(x_206, 3, x_207);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_316);
return x_206;
}
else
{
lean_object* x_317; uint8_t x_318; 
lean_dec(x_207);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
x_317 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_36);
lean_ctor_set(x_317, 2, x_37);
lean_ctor_set(x_317, 3, x_38);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_310);
x_318 = 0;
lean_ctor_set(x_206, 3, x_317);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_318);
return x_206;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_319 = lean_ctor_get(x_288, 0);
x_320 = lean_ctor_get(x_288, 1);
x_321 = lean_ctor_get(x_288, 2);
x_322 = lean_ctor_get(x_288, 3);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_288);
x_323 = 1;
lean_inc(x_207);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_207);
lean_ctor_set(x_324, 1, x_301);
lean_ctor_set(x_324, 2, x_302);
lean_ctor_set(x_324, 3, x_319);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_325 = x_207;
} else {
 lean_dec_ref(x_207);
 x_325 = lean_box(0);
}
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_323);
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 4, 1);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_322);
lean_ctor_set(x_326, 1, x_36);
lean_ctor_set(x_326, 2, x_37);
lean_ctor_set(x_326, 3, x_38);
lean_ctor_set_uint8(x_326, sizeof(void*)*4, x_323);
x_327 = 0;
lean_ctor_set(x_206, 3, x_326);
lean_ctor_set(x_206, 2, x_321);
lean_ctor_set(x_206, 1, x_320);
lean_ctor_set(x_206, 0, x_324);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_327);
return x_206;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; 
x_328 = lean_ctor_get(x_206, 1);
x_329 = lean_ctor_get(x_206, 2);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_206);
x_330 = lean_ctor_get(x_288, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_288, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_288, 2);
lean_inc(x_332);
x_333 = lean_ctor_get(x_288, 3);
lean_inc(x_333);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 lean_ctor_release(x_288, 2);
 lean_ctor_release(x_288, 3);
 x_334 = x_288;
} else {
 lean_dec_ref(x_288);
 x_334 = lean_box(0);
}
x_335 = 1;
lean_inc(x_207);
if (lean_is_scalar(x_334)) {
 x_336 = lean_alloc_ctor(1, 4, 1);
} else {
 x_336 = x_334;
}
lean_ctor_set(x_336, 0, x_207);
lean_ctor_set(x_336, 1, x_328);
lean_ctor_set(x_336, 2, x_329);
lean_ctor_set(x_336, 3, x_330);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_337 = x_207;
} else {
 lean_dec_ref(x_207);
 x_337 = lean_box(0);
}
lean_ctor_set_uint8(x_336, sizeof(void*)*4, x_335);
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_36);
lean_ctor_set(x_338, 2, x_37);
lean_ctor_set(x_338, 3, x_38);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_335);
x_339 = 0;
x_340 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_340, 0, x_336);
lean_ctor_set(x_340, 1, x_331);
lean_ctor_set(x_340, 2, x_332);
lean_ctor_set(x_340, 3, x_338);
lean_ctor_set_uint8(x_340, sizeof(void*)*4, x_339);
return x_340;
}
}
else
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_206);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_342 = lean_ctor_get(x_206, 3);
lean_dec(x_342);
x_343 = lean_ctor_get(x_206, 0);
lean_dec(x_343);
x_344 = !lean_is_exclusive(x_207);
if (x_344 == 0)
{
uint8_t x_345; uint8_t x_346; 
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_299);
x_345 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_345);
x_346 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_346);
return x_1;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; uint8_t x_353; 
x_347 = lean_ctor_get(x_207, 0);
x_348 = lean_ctor_get(x_207, 1);
x_349 = lean_ctor_get(x_207, 2);
x_350 = lean_ctor_get(x_207, 3);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_207);
x_351 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_351, 0, x_347);
lean_ctor_set(x_351, 1, x_348);
lean_ctor_set(x_351, 2, x_349);
lean_ctor_set(x_351, 3, x_350);
lean_ctor_set_uint8(x_351, sizeof(void*)*4, x_299);
x_352 = 0;
lean_ctor_set(x_206, 0, x_351);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_352);
x_353 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_353);
return x_1;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; uint8_t x_364; 
x_354 = lean_ctor_get(x_206, 1);
x_355 = lean_ctor_get(x_206, 2);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_206);
x_356 = lean_ctor_get(x_207, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_207, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_207, 2);
lean_inc(x_358);
x_359 = lean_ctor_get(x_207, 3);
lean_inc(x_359);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_360 = x_207;
} else {
 lean_dec_ref(x_207);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 4, 1);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_356);
lean_ctor_set(x_361, 1, x_357);
lean_ctor_set(x_361, 2, x_358);
lean_ctor_set(x_361, 3, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_299);
x_362 = 0;
x_363 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_354);
lean_ctor_set(x_363, 2, x_355);
lean_ctor_set(x_363, 3, x_288);
lean_ctor_set_uint8(x_363, sizeof(void*)*4, x_362);
x_364 = 1;
lean_ctor_set(x_1, 0, x_363);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_364);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_365 = lean_ctor_get(x_1, 0);
x_366 = lean_ctor_get(x_1, 1);
x_367 = lean_ctor_get(x_1, 2);
x_368 = lean_ctor_get(x_1, 3);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_1);
x_369 = lean_string_dec_lt(x_2, x_366);
if (x_369 == 0)
{
uint8_t x_370; 
x_370 = lean_string_dec_lt(x_366, x_2);
if (x_370 == 0)
{
uint8_t x_371; lean_object* x_372; 
lean_dec(x_367);
lean_dec(x_366);
x_371 = 1;
x_372 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_372, 0, x_365);
lean_ctor_set(x_372, 1, x_2);
lean_ctor_set(x_372, 2, x_3);
lean_ctor_set(x_372, 3, x_368);
lean_ctor_set_uint8(x_372, sizeof(void*)*4, x_371);
return x_372;
}
else
{
uint8_t x_373; 
x_373 = l_Std_RBNode_isRed___rarg(x_368);
if (x_373 == 0)
{
lean_object* x_374; uint8_t x_375; lean_object* x_376; 
x_374 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_368, x_2, x_3);
x_375 = 1;
x_376 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_376, 0, x_365);
lean_ctor_set(x_376, 1, x_366);
lean_ctor_set(x_376, 2, x_367);
lean_ctor_set(x_376, 3, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_375);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; 
x_377 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_368, x_2, x_3);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_377, 3);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; 
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_377, 2);
lean_inc(x_381);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_382 = x_377;
} else {
 lean_dec_ref(x_377);
 x_382 = lean_box(0);
}
x_383 = 0;
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_379);
lean_ctor_set(x_384, 1, x_380);
lean_ctor_set(x_384, 2, x_381);
lean_ctor_set(x_384, 3, x_379);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_383);
x_385 = 1;
x_386 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_386, 0, x_365);
lean_ctor_set(x_386, 1, x_366);
lean_ctor_set(x_386, 2, x_367);
lean_ctor_set(x_386, 3, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
return x_386;
}
else
{
uint8_t x_387; 
x_387 = lean_ctor_get_uint8(x_379, sizeof(void*)*4);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; lean_object* x_400; 
x_388 = lean_ctor_get(x_377, 1);
lean_inc(x_388);
x_389 = lean_ctor_get(x_377, 2);
lean_inc(x_389);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_390 = x_377;
} else {
 lean_dec_ref(x_377);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_379, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_379, 1);
lean_inc(x_392);
x_393 = lean_ctor_get(x_379, 2);
lean_inc(x_393);
x_394 = lean_ctor_get(x_379, 3);
lean_inc(x_394);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 lean_ctor_release(x_379, 3);
 x_395 = x_379;
} else {
 lean_dec_ref(x_379);
 x_395 = lean_box(0);
}
x_396 = 1;
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_395;
}
lean_ctor_set(x_397, 0, x_365);
lean_ctor_set(x_397, 1, x_366);
lean_ctor_set(x_397, 2, x_367);
lean_ctor_set(x_397, 3, x_378);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_396);
if (lean_is_scalar(x_390)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_390;
}
lean_ctor_set(x_398, 0, x_391);
lean_ctor_set(x_398, 1, x_392);
lean_ctor_set(x_398, 2, x_393);
lean_ctor_set(x_398, 3, x_394);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_396);
x_399 = 0;
x_400 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_388);
lean_ctor_set(x_400, 2, x_389);
lean_ctor_set(x_400, 3, x_398);
lean_ctor_set_uint8(x_400, sizeof(void*)*4, x_399);
return x_400;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_401 = lean_ctor_get(x_377, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_377, 2);
lean_inc(x_402);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_403 = x_377;
} else {
 lean_dec_ref(x_377);
 x_403 = lean_box(0);
}
x_404 = 0;
if (lean_is_scalar(x_403)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_403;
}
lean_ctor_set(x_405, 0, x_378);
lean_ctor_set(x_405, 1, x_401);
lean_ctor_set(x_405, 2, x_402);
lean_ctor_set(x_405, 3, x_379);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_404);
x_406 = 1;
x_407 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_407, 0, x_365);
lean_ctor_set(x_407, 1, x_366);
lean_ctor_set(x_407, 2, x_367);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
}
}
else
{
uint8_t x_408; 
x_408 = lean_ctor_get_uint8(x_378, sizeof(void*)*4);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; 
x_409 = lean_ctor_get(x_377, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_377, 2);
lean_inc(x_410);
x_411 = lean_ctor_get(x_377, 3);
lean_inc(x_411);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_412 = x_377;
} else {
 lean_dec_ref(x_377);
 x_412 = lean_box(0);
}
x_413 = lean_ctor_get(x_378, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_378, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_378, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_378, 3);
lean_inc(x_416);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_417 = x_378;
} else {
 lean_dec_ref(x_378);
 x_417 = lean_box(0);
}
x_418 = 1;
if (lean_is_scalar(x_417)) {
 x_419 = lean_alloc_ctor(1, 4, 1);
} else {
 x_419 = x_417;
}
lean_ctor_set(x_419, 0, x_365);
lean_ctor_set(x_419, 1, x_366);
lean_ctor_set(x_419, 2, x_367);
lean_ctor_set(x_419, 3, x_413);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
if (lean_is_scalar(x_412)) {
 x_420 = lean_alloc_ctor(1, 4, 1);
} else {
 x_420 = x_412;
}
lean_ctor_set(x_420, 0, x_416);
lean_ctor_set(x_420, 1, x_409);
lean_ctor_set(x_420, 2, x_410);
lean_ctor_set(x_420, 3, x_411);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_418);
x_421 = 0;
x_422 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_414);
lean_ctor_set(x_422, 2, x_415);
lean_ctor_set(x_422, 3, x_420);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
return x_422;
}
else
{
lean_object* x_423; 
x_423 = lean_ctor_get(x_377, 3);
lean_inc(x_423);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; 
x_424 = lean_ctor_get(x_377, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_377, 2);
lean_inc(x_425);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_426 = x_377;
} else {
 lean_dec_ref(x_377);
 x_426 = lean_box(0);
}
x_427 = 0;
if (lean_is_scalar(x_426)) {
 x_428 = lean_alloc_ctor(1, 4, 1);
} else {
 x_428 = x_426;
}
lean_ctor_set(x_428, 0, x_378);
lean_ctor_set(x_428, 1, x_424);
lean_ctor_set(x_428, 2, x_425);
lean_ctor_set(x_428, 3, x_423);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
x_429 = 1;
x_430 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_430, 0, x_365);
lean_ctor_set(x_430, 1, x_366);
lean_ctor_set(x_430, 2, x_367);
lean_ctor_set(x_430, 3, x_428);
lean_ctor_set_uint8(x_430, sizeof(void*)*4, x_429);
return x_430;
}
else
{
uint8_t x_431; 
x_431 = lean_ctor_get_uint8(x_423, sizeof(void*)*4);
if (x_431 == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; 
x_432 = lean_ctor_get(x_377, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_377, 2);
lean_inc(x_433);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_434 = x_377;
} else {
 lean_dec_ref(x_377);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_423, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_423, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_423, 2);
lean_inc(x_437);
x_438 = lean_ctor_get(x_423, 3);
lean_inc(x_438);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 lean_ctor_release(x_423, 2);
 lean_ctor_release(x_423, 3);
 x_439 = x_423;
} else {
 lean_dec_ref(x_423);
 x_439 = lean_box(0);
}
x_440 = 1;
lean_inc(x_378);
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(1, 4, 1);
} else {
 x_441 = x_439;
}
lean_ctor_set(x_441, 0, x_365);
lean_ctor_set(x_441, 1, x_366);
lean_ctor_set(x_441, 2, x_367);
lean_ctor_set(x_441, 3, x_378);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_442 = x_378;
} else {
 lean_dec_ref(x_378);
 x_442 = lean_box(0);
}
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_440);
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_435);
lean_ctor_set(x_443, 1, x_436);
lean_ctor_set(x_443, 2, x_437);
lean_ctor_set(x_443, 3, x_438);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_440);
x_444 = 0;
if (lean_is_scalar(x_434)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_434;
}
lean_ctor_set(x_445, 0, x_441);
lean_ctor_set(x_445, 1, x_432);
lean_ctor_set(x_445, 2, x_433);
lean_ctor_set(x_445, 3, x_443);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_444);
return x_445;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; uint8_t x_457; lean_object* x_458; 
x_446 = lean_ctor_get(x_377, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_377, 2);
lean_inc(x_447);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_448 = x_377;
} else {
 lean_dec_ref(x_377);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_378, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_378, 1);
lean_inc(x_450);
x_451 = lean_ctor_get(x_378, 2);
lean_inc(x_451);
x_452 = lean_ctor_get(x_378, 3);
lean_inc(x_452);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 lean_ctor_release(x_378, 2);
 lean_ctor_release(x_378, 3);
 x_453 = x_378;
} else {
 lean_dec_ref(x_378);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_449);
lean_ctor_set(x_454, 1, x_450);
lean_ctor_set(x_454, 2, x_451);
lean_ctor_set(x_454, 3, x_452);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_431);
x_455 = 0;
if (lean_is_scalar(x_448)) {
 x_456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_456 = x_448;
}
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_446);
lean_ctor_set(x_456, 2, x_447);
lean_ctor_set(x_456, 3, x_423);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_365);
lean_ctor_set(x_458, 1, x_366);
lean_ctor_set(x_458, 2, x_367);
lean_ctor_set(x_458, 3, x_456);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
}
}
}
}
}
}
else
{
uint8_t x_459; 
x_459 = l_Std_RBNode_isRed___rarg(x_365);
if (x_459 == 0)
{
lean_object* x_460; uint8_t x_461; lean_object* x_462; 
x_460 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_365, x_2, x_3);
x_461 = 1;
x_462 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_366);
lean_ctor_set(x_462, 2, x_367);
lean_ctor_set(x_462, 3, x_368);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
return x_462;
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_365, x_2, x_3);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; 
x_465 = lean_ctor_get(x_463, 3);
lean_inc(x_465);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; 
x_466 = lean_ctor_get(x_463, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_463, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_468 = x_463;
} else {
 lean_dec_ref(x_463);
 x_468 = lean_box(0);
}
x_469 = 0;
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(1, 4, 1);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_465);
lean_ctor_set(x_470, 1, x_466);
lean_ctor_set(x_470, 2, x_467);
lean_ctor_set(x_470, 3, x_465);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
x_471 = 1;
x_472 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_366);
lean_ctor_set(x_472, 2, x_367);
lean_ctor_set(x_472, 3, x_368);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_471);
return x_472;
}
else
{
uint8_t x_473; 
x_473 = lean_ctor_get_uint8(x_465, sizeof(void*)*4);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; 
x_474 = lean_ctor_get(x_463, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_463, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_476 = x_463;
} else {
 lean_dec_ref(x_463);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_465, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_465, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_465, 2);
lean_inc(x_479);
x_480 = lean_ctor_get(x_465, 3);
lean_inc(x_480);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 lean_ctor_release(x_465, 3);
 x_481 = x_465;
} else {
 lean_dec_ref(x_465);
 x_481 = lean_box(0);
}
x_482 = 1;
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_464);
lean_ctor_set(x_483, 1, x_474);
lean_ctor_set(x_483, 2, x_475);
lean_ctor_set(x_483, 3, x_477);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_482);
if (lean_is_scalar(x_476)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_476;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_366);
lean_ctor_set(x_484, 2, x_367);
lean_ctor_set(x_484, 3, x_368);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_482);
x_485 = 0;
x_486 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_478);
lean_ctor_set(x_486, 2, x_479);
lean_ctor_set(x_486, 3, x_484);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_485);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; 
x_487 = lean_ctor_get(x_463, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_463, 2);
lean_inc(x_488);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_489 = x_463;
} else {
 lean_dec_ref(x_463);
 x_489 = lean_box(0);
}
x_490 = 0;
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(1, 4, 1);
} else {
 x_491 = x_489;
}
lean_ctor_set(x_491, 0, x_464);
lean_ctor_set(x_491, 1, x_487);
lean_ctor_set(x_491, 2, x_488);
lean_ctor_set(x_491, 3, x_465);
lean_ctor_set_uint8(x_491, sizeof(void*)*4, x_490);
x_492 = 1;
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_366);
lean_ctor_set(x_493, 2, x_367);
lean_ctor_set(x_493, 3, x_368);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_492);
return x_493;
}
}
}
else
{
uint8_t x_494; 
x_494 = lean_ctor_get_uint8(x_464, sizeof(void*)*4);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; 
x_495 = lean_ctor_get(x_463, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_463, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_463, 3);
lean_inc(x_497);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_498 = x_463;
} else {
 lean_dec_ref(x_463);
 x_498 = lean_box(0);
}
x_499 = lean_ctor_get(x_464, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_464, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_464, 2);
lean_inc(x_501);
x_502 = lean_ctor_get(x_464, 3);
lean_inc(x_502);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_503 = x_464;
} else {
 lean_dec_ref(x_464);
 x_503 = lean_box(0);
}
x_504 = 1;
if (lean_is_scalar(x_503)) {
 x_505 = lean_alloc_ctor(1, 4, 1);
} else {
 x_505 = x_503;
}
lean_ctor_set(x_505, 0, x_499);
lean_ctor_set(x_505, 1, x_500);
lean_ctor_set(x_505, 2, x_501);
lean_ctor_set(x_505, 3, x_502);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
if (lean_is_scalar(x_498)) {
 x_506 = lean_alloc_ctor(1, 4, 1);
} else {
 x_506 = x_498;
}
lean_ctor_set(x_506, 0, x_497);
lean_ctor_set(x_506, 1, x_366);
lean_ctor_set(x_506, 2, x_367);
lean_ctor_set(x_506, 3, x_368);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_504);
x_507 = 0;
x_508 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_495);
lean_ctor_set(x_508, 2, x_496);
lean_ctor_set(x_508, 3, x_506);
lean_ctor_set_uint8(x_508, sizeof(void*)*4, x_507);
return x_508;
}
else
{
lean_object* x_509; 
x_509 = lean_ctor_get(x_463, 3);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; 
x_510 = lean_ctor_get(x_463, 1);
lean_inc(x_510);
x_511 = lean_ctor_get(x_463, 2);
lean_inc(x_511);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_512 = x_463;
} else {
 lean_dec_ref(x_463);
 x_512 = lean_box(0);
}
x_513 = 0;
if (lean_is_scalar(x_512)) {
 x_514 = lean_alloc_ctor(1, 4, 1);
} else {
 x_514 = x_512;
}
lean_ctor_set(x_514, 0, x_464);
lean_ctor_set(x_514, 1, x_510);
lean_ctor_set(x_514, 2, x_511);
lean_ctor_set(x_514, 3, x_509);
lean_ctor_set_uint8(x_514, sizeof(void*)*4, x_513);
x_515 = 1;
x_516 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_366);
lean_ctor_set(x_516, 2, x_367);
lean_ctor_set(x_516, 3, x_368);
lean_ctor_set_uint8(x_516, sizeof(void*)*4, x_515);
return x_516;
}
else
{
uint8_t x_517; 
x_517 = lean_ctor_get_uint8(x_509, sizeof(void*)*4);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; lean_object* x_531; 
x_518 = lean_ctor_get(x_463, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_463, 2);
lean_inc(x_519);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_520 = x_463;
} else {
 lean_dec_ref(x_463);
 x_520 = lean_box(0);
}
x_521 = lean_ctor_get(x_509, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_509, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_509, 2);
lean_inc(x_523);
x_524 = lean_ctor_get(x_509, 3);
lean_inc(x_524);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 lean_ctor_release(x_509, 2);
 lean_ctor_release(x_509, 3);
 x_525 = x_509;
} else {
 lean_dec_ref(x_509);
 x_525 = lean_box(0);
}
x_526 = 1;
lean_inc(x_464);
if (lean_is_scalar(x_525)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_525;
}
lean_ctor_set(x_527, 0, x_464);
lean_ctor_set(x_527, 1, x_518);
lean_ctor_set(x_527, 2, x_519);
lean_ctor_set(x_527, 3, x_521);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_528 = x_464;
} else {
 lean_dec_ref(x_464);
 x_528 = lean_box(0);
}
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 4, 1);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_524);
lean_ctor_set(x_529, 1, x_366);
lean_ctor_set(x_529, 2, x_367);
lean_ctor_set(x_529, 3, x_368);
lean_ctor_set_uint8(x_529, sizeof(void*)*4, x_526);
x_530 = 0;
if (lean_is_scalar(x_520)) {
 x_531 = lean_alloc_ctor(1, 4, 1);
} else {
 x_531 = x_520;
}
lean_ctor_set(x_531, 0, x_527);
lean_ctor_set(x_531, 1, x_522);
lean_ctor_set(x_531, 2, x_523);
lean_ctor_set(x_531, 3, x_529);
lean_ctor_set_uint8(x_531, sizeof(void*)*4, x_530);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; 
x_532 = lean_ctor_get(x_463, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_463, 2);
lean_inc(x_533);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_534 = x_463;
} else {
 lean_dec_ref(x_463);
 x_534 = lean_box(0);
}
x_535 = lean_ctor_get(x_464, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_464, 1);
lean_inc(x_536);
x_537 = lean_ctor_get(x_464, 2);
lean_inc(x_537);
x_538 = lean_ctor_get(x_464, 3);
lean_inc(x_538);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_539 = x_464;
} else {
 lean_dec_ref(x_464);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 4, 1);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_535);
lean_ctor_set(x_540, 1, x_536);
lean_ctor_set(x_540, 2, x_537);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_517);
x_541 = 0;
if (lean_is_scalar(x_534)) {
 x_542 = lean_alloc_ctor(1, 4, 1);
} else {
 x_542 = x_534;
}
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_532);
lean_ctor_set(x_542, 2, x_533);
lean_ctor_set(x_542, 3, x_509);
lean_ctor_set_uint8(x_542, sizeof(void*)*4, x_541);
x_543 = 1;
x_544 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_366);
lean_ctor_set(x_544, 2, x_367);
lean_ctor_set(x_544, 3, x_368);
lean_ctor_set_uint8(x_544, sizeof(void*)*4, x_543);
return x_544;
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
}
lean_object* l_Std_RBNode_insert___at_Lean_Server_Watchdog_updateFileWorkers___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_RBNode_ins___at_Lean_Server_Watchdog_updateFileWorkers___spec__2(x_1, x_2, x_3);
x_7 = l_Std_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
lean_object* l_Lean_Server_Watchdog_updateFileWorkers(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 4);
x_5 = lean_st_ref_take(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Std_RBNode_insert___at_Lean_Server_Watchdog_updateFileWorkers___spec__1(x_6, x_10, x_1);
x_12 = lean_st_ref_set(x_4, x_11, x_7);
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
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
lean_object* l_Lean_Server_Watchdog_updateFileWorkers___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_updateFileWorkers(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_findFileWorker_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Server_Watchdog_findFileWorker_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_findFileWorker_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_string_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_string_dec_lt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_findFileWorker___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Got unknown document URI (");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_findFileWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 4);
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker___spec__1(x_7, x_1);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_free_object(x_5);
x_10 = l_Lean_Server_Watchdog_findFileWorker___closed__1;
x_11 = lean_string_append(x_10, x_1);
x_12 = l_prec_x28___x29___closed__7;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_IO_throwServerError___rarg(x_13, x_8);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker___spec__1(x_16, x_1);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = l_Lean_Server_Watchdog_findFileWorker___closed__1;
x_20 = lean_string_append(x_19, x_1);
x_21 = l_prec_x28___x29___closed__7;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_IO_throwServerError___rarg(x_22, x_17);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
}
}
}
lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_Server_Watchdog_findFileWorker___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_findFileWorker___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_string_dec_lt(x_1, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_string_dec_lt(x_6, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
x_11 = l_Std_RBNode_appendTrees___rarg(x_5, x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l_Std_RBNode_isBlack___rarg(x_8);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_8);
x_14 = 0;
lean_ctor_set(x_2, 3, x_13);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_14);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_2);
x_15 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_8);
x_16 = l_Std_RBNode_balRight___rarg(x_5, x_6, x_7, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = l_Std_RBNode_isBlack___rarg(x_5);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_5);
x_19 = 0;
lean_ctor_set(x_2, 0, x_18);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_19);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_2);
x_20 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_5);
x_21 = l_Std_RBNode_balLeft___rarg(x_20, x_6, x_7, x_8);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_26 = lean_string_dec_lt(x_1, x_23);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = lean_string_dec_lt(x_23, x_1);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_23);
x_28 = l_Std_RBNode_appendTrees___rarg(x_22, x_25);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = l_Std_RBNode_isBlack___rarg(x_25);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_25);
x_31 = 0;
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_24);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_25);
x_34 = l_Std_RBNode_balRight___rarg(x_22, x_23, x_24, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
x_35 = l_Std_RBNode_isBlack___rarg(x_22);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_22);
x_37 = 0;
x_38 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_24);
lean_ctor_set(x_38, 3, x_25);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_22);
x_40 = l_Std_RBNode_balLeft___rarg(x_39, x_23, x_24, x_25);
return x_40;
}
}
}
}
}
}
lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_2);
x_4 = l_Std_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_eraseFileWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 4);
x_5 = lean_st_ref_take(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1(x_1, x_6);
x_9 = lean_st_ref_set(x_4, x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
lean_object* l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_del___at_Lean_Server_Watchdog_eraseFileWorker___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_erase___at_Lean_Server_Watchdog_eraseFileWorker___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_eraseFileWorker___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_eraseFileWorker(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_log___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
lean_dec(x_1);
x_6 = 10;
x_7 = lean_string_push(x_2, x_6);
x_8 = lean_apply_2(x_5, x_7, x_4);
return x_8;
}
}
lean_object* l_Lean_Server_Watchdog_log(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_4);
x_5 = l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_log___spec__1(x_4, x_1, x_2, x_3);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_apply_1(x_7, x_6);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_4);
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
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_log___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_log___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__1___rarg), 1, 0);
return x_3;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__2___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__2___rarg), 1, 0);
return x_3;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Server process for ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" crashed, likely due to a stack overflow in user code.");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("The file worker has been terminated. Either the header has changed,");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" or the file was closed, or the server is shutting down.");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__3;
x_2 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_52; 
lean_inc(x_1);
x_52 = l_Lean_Server_Watchdog_FileWorker_readMessage(x_1, x_4);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_2);
x_55 = l_IO_FS_Stream_writeLspMessage(x_2, x_53, x_54);
lean_dec(x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
lean_inc(x_2);
lean_inc(x_1);
x_57 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop(x_1, x_2, x_3, x_56);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_5 = x_62;
x_6 = x_63;
goto block_51;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_55, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_55, 1);
lean_inc(x_65);
lean_dec(x_55);
x_5 = x_64;
x_6 = x_65;
goto block_51;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_52, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_52, 1);
lean_inc(x_67);
lean_dec(x_52);
x_5 = x_66;
x_6 = x_67;
goto block_51;
}
block_51:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l_Lean_Server_Watchdog_workerCfg;
x_9 = lean_io_process_child_wait(x_8, x_7, x_6);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint32_t x_12; uint32_t x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 0;
x_13 = lean_unbox_uint32(x_10);
lean_dec(x_10);
x_14 = x_13 == x_12;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = 4;
x_23 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_1, x_2, x_22, x_21, x_11);
lean_dec(x_1);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_5);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_5);
x_34 = 10;
x_35 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__5;
x_36 = l_Lean_Server_Watchdog_FileWorker_errorPendingRequests(x_1, x_2, x_34, x_35, x_11);
lean_dec(x_1);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_9);
if (x_47 == 0)
{
return x_9;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_9, 0);
x_49 = lean_ctor_get(x_9, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_9);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages___lambda__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
return x_4;
}
}
}
static lean_object* _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
x_6 = l_Task_Priority_dedicated;
x_7 = lean_io_as_task(x_5, x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages___closed__1;
x_11 = l_Task_Priority_default;
x_12 = lean_task_map(x_10, x_9, x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages___closed__1;
x_16 = l_Task_Priority_default;
x_17 = lean_task_map(x_15, x_13, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_startFileWorker___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Name_toString___closed__1;
x_12 = l_Lean_Name_toStringWithSep(x_11, x_10);
x_13 = 1;
x_14 = x_2 + x_13;
x_15 = x_12;
x_16 = lean_array_uset(x_8, x_2, x_15);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_mk_ref(x_1, x_3);
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
}
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_165_(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_startFileWorker___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__4(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
x_9 = l_IO_FS_Stream_writeLspMessage(x_1, x_8, x_3);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_toJsonDidOpenTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_63_(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_startFileWorker___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_startFileWorker___spec__7(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_IO_FS_Stream_writeLspMessage(x_1, x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_writeNotification___at_Lean_Server_Watchdog_startFileWorker___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Server_Watchdog_FileWorker_stdin(x_1);
x_5 = l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_startFileWorker___spec__6(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("--worker");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__2;
x_2 = l_Lean_Server_Watchdog_startFileWorker___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Lsp_instToJsonTextDocumentSyncKind___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_startFileWorker___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/didOpen");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_startFileWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_7);
x_8 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst(x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_2, 6);
lean_inc(x_11);
x_12 = l_Lean_Elab_headerToImports(x_9);
x_13 = l_List_redLength___rarg(x_12);
x_14 = lean_mk_empty_array_with_capacity(x_13);
lean_dec(x_13);
x_15 = l_List_toArrayAux___rarg(x_12, x_14);
x_16 = lean_array_get_size(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = x_15;
x_20 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_startFileWorker___spec__1(x_17, x_18, x_19);
x_21 = x_20;
x_22 = l_Lean_Server_Watchdog_startFileWorker___closed__2;
x_23 = l_Array_append___rarg(x_22, x_21);
lean_dec(x_21);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
x_25 = l_List_redLength___rarg(x_24);
x_26 = lean_mk_empty_array_with_capacity(x_25);
lean_dec(x_25);
x_27 = l_List_toArrayAux___rarg(x_24, x_26);
x_28 = l_Array_append___rarg(x_23, x_27);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Server_Watchdog_workerCfg;
x_31 = l_Array_empty___closed__1;
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_11);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_29);
lean_ctor_set(x_32, 4, x_31);
x_33 = lean_io_process_spawn(x_32, x_10);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_box(0);
x_37 = l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__2(x_36, x_2, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_9);
x_41 = l_Lean_Server_Watchdog_startFileWorker___closed__3;
x_42 = lean_box(1);
lean_inc(x_38);
lean_inc(x_34);
lean_inc(x_40);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_34);
lean_ctor_set(x_43, 2, x_41);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_43, 4, x_38);
lean_inc(x_2);
x_44 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages(x_43, x_2, x_39);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_34);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_42);
lean_ctor_set(x_47, 4, x_38);
lean_inc(x_47);
x_48 = l_Lean_Server_Watchdog_FileWorker_stdin(x_47);
x_49 = lean_ctor_get(x_2, 5);
lean_inc(x_49);
x_50 = l_Lean_Server_Watchdog_startFileWorker___closed__4;
x_51 = l_Lean_Parser_Command_initialize___elambda__1___closed__1;
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_49);
x_53 = l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_startFileWorker___spec__3(x_48, x_52, x_46);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_getBuiltinSearchPath___closed__4;
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_4);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_5);
lean_ctor_set(x_56, 3, x_7);
x_57 = l_Lean_Server_Watchdog_startFileWorker___closed__5;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
lean_inc(x_47);
x_59 = l_Lean_Server_Watchdog_FileWorker_writeNotification___at_Lean_Server_Watchdog_startFileWorker___spec__5(x_47, x_58, x_54);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Lean_Server_Watchdog_updateFileWorkers(x_47, x_2, x_60);
lean_dec(x_2);
return x_61;
}
else
{
uint8_t x_62; 
lean_dec(x_47);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_47);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_53);
if (x_66 == 0)
{
return x_53;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_53, 0);
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_53);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_44);
if (x_70 == 0)
{
return x_44;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_44, 0);
x_72 = lean_ctor_get(x_44, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_44);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_33);
if (x_74 == 0)
{
return x_33;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_33, 0);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_33);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_8);
if (x_78 == 0)
{
return x_8;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_8, 0);
x_80 = lean_ctor_get(x_8, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_8);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_startFileWorker___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_startFileWorker___spec__1(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_mkRef___at_Lean_Server_Watchdog_startFileWorker___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_terminateFileWorker___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Command_exit___elambda__1___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_terminateFileWorker(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Server_Watchdog_terminateFileWorker___closed__1;
x_8 = l_Lean_Server_Watchdog_FileWorker_writeMessage(x_5, x_7, x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Server_Watchdog_eraseFileWorker(x_1, x_2, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = l_Lean_Server_Watchdog_eraseFileWorker(x_1, x_2, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_terminateFileWorker___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_terminateFileWorker(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_handleCrash(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 3);
lean_dec(x_9);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_6, 3, x_10);
x_11 = l_Lean_Server_Watchdog_updateFileWorkers(x_6, x_3, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 2);
x_15 = lean_ctor_get(x_6, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_2);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_16);
lean_ctor_set(x_17, 4, x_15);
x_18 = l_Lean_Server_Watchdog_updateFileWorkers(x_17, x_3, x_7);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_handleCrash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_handleCrash(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_tryWriteMessage_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_tryWriteMessage___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_4 < x_3;
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
x_11 = l_Lean_Server_Watchdog_FileWorker_writeMessage(x_1, x_10, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 1;
x_14 = x_4 + x_13;
x_4 = x_14;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_array_push(x_5, x_10);
x_18 = 1;
x_19 = x_4 + x_18;
x_4 = x_19;
x_5 = x_17;
x_7 = x_16;
goto _start;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__2___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_10);
x_12 = 1;
x_13 = x_3 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_9, x_3, x_14);
x_3 = x_13;
x_4 = x_15;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__3___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_10);
x_12 = 1;
x_13 = x_3 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_9, x_3, x_14);
x_3 = x_13;
x_4 = x_15;
goto _start;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__3___rarg___boxed), 4, 0);
return x_2;
}
}
static uint8_t _init_l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 0;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 1;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Server_Watchdog_eraseFileWorker(x_1, x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_5);
x_11 = l_Lean_Server_Watchdog_startFileWorker(x_10, x_5, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_3);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_empty___closed__1;
x_20 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_tryWriteMessage___spec__1(x_14, x_3, x_17, x_18, x_19, x_5, x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Array_isEmpty___rarg(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__1;
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_5);
x_26 = lean_box(0);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; 
lean_free_object(x_20);
x_27 = l_Lean_Server_Watchdog_handleCrash(x_1, x_22, x_5, x_23);
lean_dec(x_5);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__2;
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_5);
x_29 = lean_box(0);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; 
lean_free_object(x_20);
x_30 = l_Lean_Server_Watchdog_handleCrash(x_1, x_22, x_5, x_23);
lean_dec(x_5);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = l_Array_isEmpty___rarg(x_31);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__1;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_5);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Server_Watchdog_handleCrash(x_1, x_31, x_5, x_32);
lean_dec(x_5);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__2;
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_31);
lean_dec(x_5);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Server_Watchdog_handleCrash(x_1, x_31, x_5, x_32);
lean_dec(x_5);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1(x_2, x_3, x_4, x_10, x_6, x_7);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__2() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__1;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = x_1;
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Server_Watchdog_findFileWorker(x_2, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__2(x_6, x_2, x_10, x_13, x_14, x_7, x_12);
lean_dec(x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_apply_1(x_1, x_3);
x_19 = lean_array_push(x_17, x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__2(x_6, x_2, x_10, x_19, x_20, x_7, x_16);
lean_dec(x_19);
return x_21;
}
}
else
{
if (x_5 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_apply_3(x_4, x_10, x_3, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_7);
lean_dec(x_1);
return x_23;
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__2;
x_27 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__3;
x_28 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__2___rarg(x_1, x_26, x_25, x_27);
x_29 = x_28;
x_30 = l_Lean_Server_Watchdog_handleCrash(x_2, x_29, x_7, x_24);
lean_dec(x_7);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_dec(x_9);
x_32 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_3);
x_33 = lean_array_push(x_32, x_3);
x_34 = lean_apply_3(x_4, x_10, x_3, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_dec(x_33);
lean_dec(x_7);
lean_dec(x_1);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_array_get_size(x_33);
x_37 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_38 = 0;
x_39 = x_33;
x_40 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__3___rarg(x_1, x_37, x_38, x_39);
x_41 = x_40;
x_42 = l_Lean_Server_Watchdog_handleCrash(x_2, x_41, x_7, x_35);
lean_dec(x_7);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_9);
if (x_43 == 0)
{
return x_9;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_9, 0);
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_9);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_tryWriteMessage___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_tryWriteMessage___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_tryWriteMessage___spec__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__2___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_tryWriteMessage___spec__3___rarg(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__2(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_Server_Watchdog_tryWriteMessage___rarg(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Server_Watchdog_handleDidOpen(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_FileMap_ofString(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
x_9 = l_Lean_Server_Watchdog_startFileWorker(x_8, x_2, x_3);
return x_9;
}
}
lean_object* l_Lean_Server_Watchdog_handleDidChange_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Server_Watchdog_handleDidChange_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_handleDidChange_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_handleDidChange_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Server_Watchdog_handleDidChange_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_handleDidChange_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleDidChange___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_toJsonDidChangeTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_275_(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_handleDidChange___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleDidChange___spec__3(x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_IO_FS_Stream_writeLspMessage(x_1, x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_writeNotification___at_Lean_Server_Watchdog_handleDidChange___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Server_Watchdog_FileWorker_stdin(x_1);
x_5 = l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_handleDidChange___spec__2(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChange___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_4 < x_3;
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
x_11 = l_Lean_Server_Watchdog_FileWorker_writeMessage(x_1, x_10, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 1;
x_14 = x_4 + x_13;
x_4 = x_14;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_array_push(x_5, x_10);
x_18 = 1;
x_19 = x_4 + x_18;
x_4 = x_19;
x_5 = x_17;
x_7 = x_16;
goto _start;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleDidChange___spec__6(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleDidChange___spec__3(x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = 1;
x_15 = x_2 + x_14;
x_16 = x_13;
x_17 = lean_array_uset(x_8, x_2, x_16);
x_2 = x_15;
x_3 = x_17;
goto _start;
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Server_Watchdog_eraseFileWorker(x_1, x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_5);
x_11 = l_Lean_Server_Watchdog_startFileWorker(x_10, x_5, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_3);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_empty___closed__1;
x_20 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChange___spec__5(x_14, x_3, x_17, x_18, x_19, x_5, x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Array_isEmpty___rarg(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__1;
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_5);
x_26 = lean_box(0);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; 
lean_free_object(x_20);
x_27 = l_Lean_Server_Watchdog_handleCrash(x_1, x_22, x_5, x_23);
lean_dec(x_5);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__2;
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_5);
x_29 = lean_box(0);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; 
lean_free_object(x_20);
x_30 = l_Lean_Server_Watchdog_handleCrash(x_1, x_22, x_5, x_23);
lean_dec(x_5);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = l_Array_isEmpty___rarg(x_31);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__1;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_5);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Server_Watchdog_handleCrash(x_1, x_31, x_5, x_32);
lean_dec(x_5);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__2;
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_31);
lean_dec(x_5);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Server_Watchdog_handleCrash(x_1, x_31, x_5, x_32);
lean_dec(x_5);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___lambda__1(x_2, x_3, x_4, x_10, x_6, x_7);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___closed__1() {
_start:
{
size_t x_1; size_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__2;
x_3 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__3;
x_4 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleDidChange___spec__6(x_2, x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___closed__1;
x_2 = x_1;
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___lambda__2(x_5, x_1, x_9, x_12, x_13, x_6, x_11);
lean_dec(x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleDidChange___spec__3(x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_array_push(x_16, x_20);
x_22 = lean_box(0);
x_23 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___lambda__2(x_5, x_1, x_9, x_21, x_22, x_6, x_15);
lean_dec(x_21);
return x_23;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_apply_3(x_3, x_9, x_2, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_6);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___closed__2;
x_28 = l_Lean_Server_Watchdog_handleCrash(x_1, x_27, x_6, x_26);
lean_dec(x_6);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2);
x_31 = lean_array_push(x_30, x_2);
x_32 = lean_apply_3(x_3, x_9, x_2, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_dec(x_31);
lean_dec(x_6);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_array_get_size(x_31);
x_35 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_36 = 0;
x_37 = x_31;
x_38 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleDidChange___spec__6(x_35, x_36, x_37);
x_39 = x_38;
x_40 = l_Lean_Server_Watchdog_handleCrash(x_1, x_39, x_6, x_33);
lean_dec(x_6);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
return x_8;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_8);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleDidChange___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/didChange");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleDidChange___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_writeNotification___at_Lean_Server_Watchdog_handleDidChange___spec__1), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_handleDidChange___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Server_foldDocumentChanges(x_2, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_15);
lean_inc(x_3);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst(x_17, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Syntax_structEq(x_19, x_12);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_6);
x_22 = l_Lean_Server_Watchdog_terminateFileWorker(x_3, x_8, x_20);
lean_dec(x_3);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Server_Watchdog_startFileWorker(x_16, x_8, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
lean_ctor_set(x_1, 0, x_16);
x_25 = lean_ctor_get(x_5, 1);
x_26 = lean_ctor_get(x_5, 2);
x_27 = lean_ctor_get(x_5, 3);
x_28 = lean_ctor_get(x_5, 4);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
x_30 = l_Lean_Server_Watchdog_updateFileWorkers(x_29, x_8, x_20);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Server_Watchdog_handleDidChange___lambda__1___closed__1;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_6);
x_34 = l_Lean_Server_Watchdog_handleDidChange___lambda__1___closed__2;
x_35 = 1;
x_36 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4(x_3, x_33, x_34, x_35, x_35, x_8, x_31);
lean_dec(x_3);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_16);
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_1);
x_43 = lean_ctor_get(x_41, 2);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Server_foldDocumentChanges(x_2, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
lean_inc(x_45);
lean_inc(x_3);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_3);
lean_ctor_set(x_46, 1, x_4);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_parseHeaderAst(x_47, x_9);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Syntax_structEq(x_49, x_42);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_42);
lean_dec(x_6);
x_52 = l_Lean_Server_Watchdog_terminateFileWorker(x_3, x_8, x_50);
lean_dec(x_3);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_Server_Watchdog_startFileWorker(x_46, x_8, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_42);
x_56 = lean_ctor_get(x_5, 1);
x_57 = lean_ctor_get(x_5, 2);
x_58 = lean_ctor_get(x_5, 3);
x_59 = lean_ctor_get(x_5, 4);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_56);
lean_ctor_set(x_60, 2, x_57);
lean_ctor_set(x_60, 3, x_58);
lean_ctor_set(x_60, 4, x_59);
x_61 = l_Lean_Server_Watchdog_updateFileWorkers(x_60, x_8, x_50);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_Server_Watchdog_handleDidChange___lambda__1___closed__1;
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_6);
x_65 = l_Lean_Server_Watchdog_handleDidChange___lambda__1___closed__2;
x_66 = 1;
x_67 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4(x_3, x_64, x_65, x_66, x_66, x_8, x_62);
lean_dec(x_3);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_46);
lean_dec(x_42);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_68 = lean_ctor_get(x_48, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_48, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_70 = x_48;
} else {
 lean_dec_ref(x_48);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_handleDidChange___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Array_isEmpty___rarg(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Server_Watchdog_handleDidChange___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleDidChange___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Expected version number");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleDidChange___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Got outdated version number");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_handleDidChange(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Lean_Server_Watchdog_findFileWorker(x_6, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Server_Watchdog_handleDidChange___closed__1;
x_11 = l_IO_throwServerError___rarg(x_10, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_nat_dec_le(x_15, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Server_Watchdog_handleDidChange___lambda__2(x_13, x_5, x_6, x_15, x_12, x_1, x_19, x_2, x_14);
lean_dec(x_12);
lean_dec(x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_Server_Watchdog_handleDidChange___closed__2;
x_22 = l_IO_throwServerError___rarg(x_21, x_14);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChange___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleDidChange___spec__5(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleDidChange___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleDidChange___spec__6(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___lambda__2(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Server_Watchdog_handleDidChange___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Server_Watchdog_handleDidChange___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Server_Watchdog_handleDidChange___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Server_Watchdog_handleDidChange___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Server_Watchdog_handleDidClose(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_terminateFileWorker(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_handleDidClose___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_handleDidClose(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_handleCancelRequest_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_handleCancelRequest_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__3___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_handleCancelRequest_match__3___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_handleCancelRequest_match__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_Watchdog_handleCancelRequest_match__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_RBNode_find___at_Lean_Server_Watchdog_handleCancelRequest___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_8 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
lean_inc(x_2);
x_9 = l___private_Lean_Data_JsonRpc_0__Lean_JsonRpc_RequestID_lt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
lean_dec(x_6);
x_1 = x_7;
goto _start;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1 = x_4;
goto _start;
}
}
}
}
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_59_(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_handleCancelRequest___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__4(x_5);
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_IO_FS_Stream_writeLspMessage(x_1, x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_writeNotification___at_Lean_Server_Watchdog_handleCancelRequest___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Server_Watchdog_FileWorker_stdin(x_1);
x_5 = l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_handleCancelRequest___spec__3(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleCancelRequest___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_4 < x_3;
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
x_11 = l_Lean_Server_Watchdog_FileWorker_writeMessage(x_1, x_10, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 1;
x_14 = x_4 + x_13;
x_4 = x_14;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_array_push(x_5, x_10);
x_18 = 1;
x_19 = x_4 + x_18;
x_4 = x_19;
x_5 = x_17;
x_7 = x_16;
goto _start;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleCancelRequest___spec__7(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__4(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = 1;
x_15 = x_2 + x_14;
x_16 = x_13;
x_17 = lean_array_uset(x_8, x_2, x_16);
x_2 = x_15;
x_3 = x_17;
goto _start;
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Server_Watchdog_eraseFileWorker(x_1, x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_5);
x_11 = l_Lean_Server_Watchdog_startFileWorker(x_10, x_5, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_3);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_empty___closed__1;
x_20 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleCancelRequest___spec__6(x_14, x_3, x_17, x_18, x_19, x_5, x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Array_isEmpty___rarg(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__1;
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_5);
x_26 = lean_box(0);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; 
lean_free_object(x_20);
x_27 = l_Lean_Server_Watchdog_handleCrash(x_1, x_22, x_5, x_23);
lean_dec(x_5);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__2;
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_5);
x_29 = lean_box(0);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; 
lean_free_object(x_20);
x_30 = l_Lean_Server_Watchdog_handleCrash(x_1, x_22, x_5, x_23);
lean_dec(x_5);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = l_Array_isEmpty___rarg(x_31);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__1;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_5);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Server_Watchdog_handleCrash(x_1, x_31, x_5, x_32);
lean_dec(x_5);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__2;
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_31);
lean_dec(x_5);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Server_Watchdog_handleCrash(x_1, x_31, x_5, x_32);
lean_dec(x_5);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___lambda__1(x_2, x_3, x_4, x_10, x_6, x_7);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___closed__1() {
_start:
{
size_t x_1; size_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__2;
x_3 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__3;
x_4 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleCancelRequest___spec__7(x_2, x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___closed__1;
x_2 = x_1;
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___lambda__2(x_5, x_1, x_9, x_12, x_13, x_6, x_11);
lean_dec(x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__4(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_array_push(x_16, x_20);
x_22 = lean_box(0);
x_23 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___lambda__2(x_5, x_1, x_9, x_21, x_22, x_6, x_15);
lean_dec(x_21);
return x_23;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_apply_3(x_3, x_9, x_2, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_6);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___closed__2;
x_28 = l_Lean_Server_Watchdog_handleCrash(x_1, x_27, x_6, x_26);
lean_dec(x_6);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2);
x_31 = lean_array_push(x_30, x_2);
x_32 = lean_apply_3(x_3, x_9, x_2, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_dec(x_31);
lean_dec(x_6);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_array_get_size(x_31);
x_35 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_36 = 0;
x_37 = x_31;
x_38 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleCancelRequest___spec__7(x_35, x_36, x_37);
x_39 = x_38;
x_40 = l_Lean_Server_Watchdog_handleCrash(x_1, x_39, x_6, x_33);
lean_dec(x_6);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
return x_8;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_8);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("$/cancelRequest");
return x_1;
}
}
static lean_object* _init_l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_writeNotification___at_Lean_Server_Watchdog_handleCancelRequest___spec__2___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
lean_inc(x_1);
x_12 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8(x_1, x_8, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_4);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_10, 4);
x_20 = lean_st_ref_take(x_19, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_1);
lean_inc(x_21);
x_23 = l_Std_RBNode_find___at_Lean_Server_Watchdog_handleCancelRequest___spec__1(x_21, x_1);
lean_inc(x_1);
x_24 = l_Std_RBNode_erase___at_Lean_Server_Watchdog_FileWorker_readMessage___spec__1(x_1, x_21);
x_25 = lean_st_ref_set(x_19, x_24, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_2 = x_11;
x_3 = x_27;
x_5 = x_26;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
lean_dec(x_23);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8___closed__1;
lean_inc(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_1);
x_32 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8___closed__2;
x_33 = 0;
lean_inc(x_4);
x_34 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5(x_9, x_31, x_32, x_33, x_33, x_4, x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_2 = x_11;
x_3 = x_36;
x_5 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_4);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_12);
if (x_42 == 0)
{
return x_12;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_12, 0);
x_44 = lean_ctor_get(x_12, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_12);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
lean_object* l_Lean_Server_Watchdog_handleCancelRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 4);
lean_inc(x_4);
x_5 = lean_st_ref_get(x_4, x_3);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8(x_1, x_6, x_8, x_2, x_7);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
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
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleCancelRequest___spec__4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_handleCancelRequest___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeLspNotification___at_Lean_Server_Watchdog_handleCancelRequest___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_writeNotification___at_Lean_Server_Watchdog_handleCancelRequest___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_FileWorker_writeNotification___at_Lean_Server_Watchdog_handleCancelRequest___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleCancelRequest___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleCancelRequest___spec__6(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleCancelRequest___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleCancelRequest___spec__7(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___lambda__2(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Server_Watchdog_parseParams_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_parseParams_match__1___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_parseParams___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Got param with wrong structure: ");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_Json_compress(x_2);
x_7 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_instInhabitedParserDescr___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_IO_throwServerError___rarg(x_10, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_parseParams___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_parseParams___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest_match__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/hover");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest_match__1___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/documentSymbol");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_handleRequest_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Lsp_Ipc_collectDiagnostics___closed__1;
x_7 = lean_string_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_2);
x_8 = l_Lean_Server_Watchdog_handleRequest_match__1___rarg___closed__1;
x_9 = lean_string_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
lean_dec(x_3);
x_10 = l_Lean_Server_Watchdog_handleRequest_match__1___rarg___closed__2;
x_11 = lean_string_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_4);
x_12 = lean_apply_1(x_5, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_4, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_3, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_apply_1(x_2, x_17);
return x_18;
}
}
}
lean_object* l_Lean_Server_Watchdog_handleRequest_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_handleRequest_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_fromJsonDocumentSymbolParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_125_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_LanguageFeatures_0__Lean_Lsp_toJsonDocumentSymbolParams____x40_Lean_Data_Lsp_LanguageFeatures___hyg_155_(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_handleRequest___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__4(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
x_9 = l_IO_FS_Stream_writeLspMessage(x_1, x_8, x_3);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_writeRequest___at_Lean_Server_Watchdog_handleRequest___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = l_Lean_Server_Watchdog_FileWorker_stdin(x_1);
lean_inc(x_2);
x_5 = l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_handleRequest___spec__3(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_st_ref_take(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__4(x_13);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_Std_RBNode_insert___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__1(x_9, x_11, x_15);
x_17 = lean_st_ref_set(x_7, x_16, x_10);
lean_dec(x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
return x_5;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_4 < x_3;
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
x_11 = l_Lean_Server_Watchdog_FileWorker_writeMessage(x_1, x_10, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 1;
x_14 = x_4 + x_13;
x_4 = x_14;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_array_push(x_5, x_10);
x_18 = 1;
x_19 = x_4 + x_18;
x_4 = x_19;
x_5 = x_17;
x_7 = x_16;
goto _start;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__7(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__4(x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = 1;
x_16 = x_2 + x_15;
x_17 = x_14;
x_18 = lean_array_uset(x_8, x_2, x_17);
x_2 = x_16;
x_3 = x_18;
goto _start;
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Server_Watchdog_eraseFileWorker(x_1, x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_5);
x_11 = l_Lean_Server_Watchdog_startFileWorker(x_10, x_5, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_3);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_empty___closed__1;
x_20 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__6(x_14, x_3, x_17, x_18, x_19, x_5, x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Array_isEmpty___rarg(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__1;
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_5);
x_26 = lean_box(0);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; 
lean_free_object(x_20);
x_27 = l_Lean_Server_Watchdog_handleCrash(x_1, x_22, x_5, x_23);
lean_dec(x_5);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__2;
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_5);
x_29 = lean_box(0);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; 
lean_free_object(x_20);
x_30 = l_Lean_Server_Watchdog_handleCrash(x_1, x_22, x_5, x_23);
lean_dec(x_5);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = l_Array_isEmpty___rarg(x_31);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__1;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_5);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Server_Watchdog_handleCrash(x_1, x_31, x_5, x_32);
lean_dec(x_5);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__2;
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_31);
lean_dec(x_5);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Server_Watchdog_handleCrash(x_1, x_31, x_5, x_32);
lean_dec(x_5);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___lambda__1(x_2, x_3, x_4, x_10, x_6, x_7);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___closed__1() {
_start:
{
size_t x_1; size_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__2;
x_3 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__3;
x_4 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__7(x_2, x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___closed__1;
x_2 = x_1;
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___lambda__2(x_5, x_1, x_9, x_12, x_13, x_6, x_11);
lean_dec(x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__4(x_19);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_push(x_16, x_21);
x_23 = lean_box(0);
x_24 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___lambda__2(x_5, x_1, x_9, x_22, x_23, x_6, x_15);
lean_dec(x_22);
return x_24;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_apply_3(x_3, x_9, x_2, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_dec(x_6);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___closed__2;
x_29 = l_Lean_Server_Watchdog_handleCrash(x_1, x_28, x_6, x_27);
lean_dec(x_6);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_dec(x_8);
x_31 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2);
x_32 = lean_array_push(x_31, x_2);
x_33 = lean_apply_3(x_3, x_9, x_2, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_32);
lean_dec(x_6);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_array_get_size(x_32);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
x_38 = x_32;
x_39 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__7(x_36, x_37, x_38);
x_40 = x_39;
x_41 = l_Lean_Server_Watchdog_handleCrash(x_1, x_40, x_6, x_34);
lean_dec(x_6);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
return x_8;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonTextDocumentPositionParams____x40_Lean_Data_Lsp_Basic___hyg_1299_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonTextDocumentPositionParams____x40_Lean_Data_Lsp_Basic___hyg_1265_(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
lean_object* l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_handleRequest___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__11(x_6);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
x_9 = l_IO_FS_Stream_writeLspMessage(x_1, x_8, x_3);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_writeRequest___at_Lean_Server_Watchdog_handleRequest___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = l_Lean_Server_Watchdog_FileWorker_stdin(x_1);
lean_inc(x_2);
x_5 = l_IO_FS_Stream_writeLspRequest___at_Lean_Server_Watchdog_handleRequest___spec__10(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_st_ref_take(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__11(x_13);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_Std_RBNode_insert___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__1(x_9, x_11, x_15);
x_17 = lean_st_ref_set(x_7, x_16, x_10);
lean_dec(x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
return x_5;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_4 < x_3;
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
x_11 = l_Lean_Server_Watchdog_FileWorker_writeMessage(x_1, x_10, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 1;
x_14 = x_4 + x_13;
x_4 = x_14;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_array_push(x_5, x_10);
x_18 = 1;
x_19 = x_4 + x_18;
x_4 = x_19;
x_5 = x_17;
x_7 = x_16;
goto _start;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__14(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__11(x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = 1;
x_16 = x_2 + x_15;
x_17 = x_14;
x_18 = lean_array_uset(x_8, x_2, x_17);
x_2 = x_16;
x_3 = x_18;
goto _start;
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Server_Watchdog_eraseFileWorker(x_1, x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_5);
x_11 = l_Lean_Server_Watchdog_startFileWorker(x_10, x_5, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_3);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_empty___closed__1;
x_20 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__13(x_14, x_3, x_17, x_18, x_19, x_5, x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Array_isEmpty___rarg(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__1;
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_5);
x_26 = lean_box(0);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; 
lean_free_object(x_20);
x_27 = l_Lean_Server_Watchdog_handleCrash(x_1, x_22, x_5, x_23);
lean_dec(x_5);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__2;
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_5);
x_29 = lean_box(0);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; 
lean_free_object(x_20);
x_30 = l_Lean_Server_Watchdog_handleCrash(x_1, x_22, x_5, x_23);
lean_dec(x_5);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = l_Array_isEmpty___rarg(x_31);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__1;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_5);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Server_Watchdog_handleCrash(x_1, x_31, x_5, x_32);
lean_dec(x_5);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__2;
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_31);
lean_dec(x_5);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Server_Watchdog_handleCrash(x_1, x_31, x_5, x_32);
lean_dec(x_5);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___lambda__1(x_2, x_3, x_4, x_10, x_6, x_7);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___closed__1() {
_start:
{
size_t x_1; size_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__2;
x_3 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__3;
x_4 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__14(x_2, x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___closed__1;
x_2 = x_1;
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___lambda__2(x_5, x_1, x_9, x_12, x_13, x_6, x_11);
lean_dec(x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_Lean_Json_toStructured_x3f___at_Lean_Server_Watchdog_handleRequest___spec__11(x_19);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_push(x_16, x_21);
x_23 = lean_box(0);
x_24 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___lambda__2(x_5, x_1, x_9, x_22, x_23, x_6, x_15);
lean_dec(x_22);
return x_24;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_apply_3(x_3, x_9, x_2, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_dec(x_6);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___closed__2;
x_29 = l_Lean_Server_Watchdog_handleCrash(x_1, x_28, x_6, x_27);
lean_dec(x_6);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_dec(x_8);
x_31 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2);
x_32 = lean_array_push(x_31, x_2);
x_33 = lean_apply_3(x_3, x_9, x_2, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_32);
lean_dec(x_6);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_array_get_size(x_32);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
x_38 = x_32;
x_39 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__14(x_36, x_37, x_38);
x_40 = x_39;
x_41 = l_Lean_Server_Watchdog_handleCrash(x_1, x_40, x_6, x_34);
lean_dec(x_6);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
return x_8;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_Extra_0__Lean_Lsp_fromJsonWaitForDiagnosticsParam____x40_Lean_Data_Lsp_Extra___hyg_32_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_FileWorker_writeRequest___at_Lean_Server_Watchdog_handleRequest___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = l_Lean_Server_Watchdog_FileWorker_stdin(x_1);
lean_inc(x_2);
x_5 = l_IO_FS_Stream_writeLspRequest___at_Lean_Lsp_Ipc_collectDiagnostics___spec__2(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_st_ref_take(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_collectDiagnostics___spec__3(x_13);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_Std_RBNode_insert___at_Lean_Server_Watchdog_FileWorker_writeRequest___spec__1(x_9, x_11, x_15);
x_17 = lean_st_ref_set(x_7, x_16, x_10);
lean_dec(x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
return x_5;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__18(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_4 < x_3;
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
x_11 = l_Lean_Server_Watchdog_FileWorker_writeMessage(x_1, x_10, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 1;
x_14 = x_4 + x_13;
x_4 = x_14;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_array_push(x_5, x_10);
x_18 = 1;
x_19 = x_4 + x_18;
x_4 = x_19;
x_5 = x_17;
x_7 = x_16;
goto _start;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__19(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_collectDiagnostics___spec__3(x_12);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = 1;
x_16 = x_2 + x_15;
x_17 = x_14;
x_18 = lean_array_uset(x_8, x_2, x_17);
x_2 = x_16;
x_3 = x_18;
goto _start;
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Server_Watchdog_eraseFileWorker(x_1, x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_5);
x_11 = l_Lean_Server_Watchdog_startFileWorker(x_10, x_5, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_3);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_empty___closed__1;
x_20 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__18(x_14, x_3, x_17, x_18, x_19, x_5, x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Array_isEmpty___rarg(x_22);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__1;
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_5);
x_26 = lean_box(0);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; 
lean_free_object(x_20);
x_27 = l_Lean_Server_Watchdog_handleCrash(x_1, x_22, x_5, x_23);
lean_dec(x_5);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__2;
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_5);
x_29 = lean_box(0);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; 
lean_free_object(x_20);
x_30 = l_Lean_Server_Watchdog_handleCrash(x_1, x_22, x_5, x_23);
lean_dec(x_5);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = l_Array_isEmpty___rarg(x_31);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__1;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_5);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Server_Watchdog_handleCrash(x_1, x_31, x_5, x_32);
lean_dec(x_5);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__2;
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_31);
lean_dec(x_5);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Server_Watchdog_handleCrash(x_1, x_31, x_5, x_32);
lean_dec(x_5);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___lambda__1(x_2, x_3, x_4, x_10, x_6, x_7);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___closed__1() {
_start:
{
size_t x_1; size_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__2;
x_3 = l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__3;
x_4 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__19(x_2, x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___closed__1;
x_2 = x_1;
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_Watchdog_findFileWorker(x_1, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___lambda__2(x_5, x_1, x_9, x_12, x_13, x_6, x_11);
lean_dec(x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_Lean_Json_toStructured_x3f___at_Lean_Lsp_Ipc_collectDiagnostics___spec__3(x_19);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_push(x_16, x_21);
x_23 = lean_box(0);
x_24 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___lambda__2(x_5, x_1, x_9, x_22, x_23, x_6, x_15);
lean_dec(x_22);
return x_24;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_apply_3(x_3, x_9, x_2, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_dec(x_6);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___closed__2;
x_29 = l_Lean_Server_Watchdog_handleCrash(x_1, x_28, x_6, x_27);
lean_dec(x_6);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_8, 1);
lean_inc(x_30);
lean_dec(x_8);
x_31 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2);
x_32 = lean_array_push(x_31, x_2);
x_33 = lean_apply_3(x_3, x_9, x_2, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_32);
lean_dec(x_6);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_array_get_size(x_32);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
x_38 = x_32;
x_39 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__19(x_36, x_37, x_38);
x_40 = x_39;
x_41 = l_Lean_Server_Watchdog_handleCrash(x_1, x_40, x_6, x_34);
lean_dec(x_6);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
return x_8;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Unsupported request method: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_writeRequest___at_Lean_Server_Watchdog_handleRequest___spec__2), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_writeRequest___at_Lean_Server_Watchdog_handleRequest___spec__9), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleRequest___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_FileWorker_writeRequest___at_Lean_Server_Watchdog_handleRequest___spec__16), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_handleRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Lsp_Ipc_collectDiagnostics___closed__1;
x_7 = lean_string_dec_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Server_Watchdog_handleRequest_match__1___rarg___closed__1;
x_9 = lean_string_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Server_Watchdog_handleRequest_match__1___rarg___closed__2;
x_11 = lean_string_dec_eq(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = l_Lean_Server_Watchdog_handleRequest___closed__1;
x_14 = lean_string_append(x_13, x_2);
lean_dec(x_2);
x_15 = l_Lean_instInhabitedParserDescr___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_box(0);
x_18 = 2;
x_19 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_18);
x_20 = l_IO_FS_Stream_writeLspResponseError(x_12, x_19, x_5);
lean_dec(x_19);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1(x_3, x_4, x_5);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_22);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 2, x_22);
x_25 = l_Lean_Server_Watchdog_handleRequest___closed__2;
x_26 = 1;
x_27 = 0;
x_28 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5(x_22, x_24, x_25, x_26, x_27, x_4, x_23);
lean_dec(x_22);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_33; 
x_33 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__8(x_3, x_4, x_5);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_2);
lean_ctor_set(x_37, 2, x_34);
x_38 = l_Lean_Server_Watchdog_handleRequest___closed__3;
x_39 = 1;
x_40 = 0;
x_41 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12(x_36, x_37, x_38, x_39, x_40, x_4, x_35);
lean_dec(x_36);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
return x_33;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
lean_object* x_46; 
x_46 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__15(x_3, x_4, x_5);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_47);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_2);
lean_ctor_set(x_49, 2, x_47);
x_50 = l_Lean_Server_Watchdog_handleRequest___closed__4;
x_51 = 1;
x_52 = 0;
x_53 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17(x_47, x_49, x_50, x_51, x_52, x_4, x_48);
lean_dec(x_47);
return x_53;
}
else
{
uint8_t x_54; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_46);
if (x_54 == 0)
{
return x_46;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_46, 0);
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_46);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__6(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__7(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___lambda__2(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__8(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__13(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__14(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___lambda__2(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleRequest___spec__15(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Server_Watchdog_handleRequest___spec__18(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_Watchdog_handleRequest___spec__19(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___lambda__2(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleNotification_match__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("textDocument/didClose");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_handleNotification_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Server_Watchdog_startFileWorker___closed__5;
x_8 = lean_string_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_2);
x_9 = l_Lean_Server_Watchdog_handleDidChange___lambda__1___closed__1;
x_10 = lean_string_dec_eq(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_3);
x_11 = l_Lean_Server_Watchdog_handleNotification_match__1___rarg___closed__1;
x_12 = lean_string_dec_eq(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_4);
x_13 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8___closed__1;
x_14 = lean_string_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_apply_1(x_6, x_1);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_apply_1(x_5, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_apply_1(x_4, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_apply_1(x_3, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_apply_1(x_2, x_22);
return x_23;
}
}
}
lean_object* l_Lean_Server_Watchdog_handleNotification_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_handleNotification_match__1___rarg), 6, 0);
return x_2;
}
}
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_handleNotification___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
lean_dec(x_1);
x_6 = 10;
x_7 = lean_string_push(x_2, x_6);
x_8 = lean_apply_2(x_5, x_7, x_4);
return x_8;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_fromJsonCancelParams____x40_Lean_Data_Lsp_Basic___hyg_84_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidCloseTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_439_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidChangeTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_309_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Data_Lsp_TextSync_0__Lean_Lsp_fromJsonDidOpenTextDocumentParams____x40_Lean_Data_Lsp_TextSync___hyg_88_(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Json_compress(x_1);
x_6 = l_Lean_Server_Watchdog_parseParams___rarg___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_instInhabitedParserDescr___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_IO_throwServerError___rarg(x_9, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_handleNotification___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Got unsupported notification: ");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_handleNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Server_Watchdog_startFileWorker___closed__5;
x_6 = lean_string_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Server_Watchdog_handleDidChange___lambda__1___closed__1;
x_8 = lean_string_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Server_Watchdog_handleNotification_match__1___rarg___closed__1;
x_10 = lean_string_dec_eq(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8___closed__1;
x_12 = lean_string_dec_eq(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
x_14 = l_Lean_Server_Watchdog_handleNotification___closed__1;
x_15 = lean_string_append(x_14, x_1);
x_16 = l_Lean_instInhabitedParserDescr___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_handleNotification___spec__1(x_13, x_17, x_3, x_4);
lean_dec(x_3);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__2(x_2, x_3, x_4);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Server_Watchdog_handleCancelRequest(x_20, x_3, x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__3(x_2, x_3, x_4);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Server_Watchdog_terminateFileWorker(x_28, x_3, x_29);
lean_dec(x_3);
lean_dec(x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
lean_object* x_35; 
x_35 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4(x_2, x_3, x_4);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Server_Watchdog_handleDidChange(x_36, x_3, x_37);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__5(x_2, x_3, x_4);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Server_Watchdog_handleDidOpen(x_44, x_3, x_45);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_handleNotification___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_handleNotification___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_Watchdog_parseParams___at_Lean_Server_Watchdog_handleNotification___spec__5(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_handleNotification___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_Watchdog_handleNotification(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_shutdown_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Server_Watchdog_shutdown_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_shutdown_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_shutdown_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Server_Watchdog_shutdown_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_shutdown_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_shutdown_match__3___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_shutdown_match__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_shutdown_match__3___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_shutdown_match__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_Watchdog_shutdown_match__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_shutdown_match__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_shutdown_match__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_shutdown_match__4___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_shutdown_match__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_Watchdog_shutdown_match__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1(x_7, x_2, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_8, 2);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_io_wait(x_17, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_1 = x_9;
x_2 = x_20;
x_4 = x_19;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_8);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 3);
x_10 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2(x_7, x_2, x_3, x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Server_Watchdog_terminateFileWorker(x_8, x_3, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_1 = x_9;
x_2 = x_14;
x_4 = x_13;
goto _start;
}
}
}
lean_object* l_Lean_Server_Watchdog_shutdown(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_3 = lean_ctor_get(x_1, 4);
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_19 = lean_box(0);
x_20 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2(x_5, x_19, x_1, x_6);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_7 = x_21;
goto block_18;
block_18:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1(x_5, x_8, x_1, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
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
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_shutdown___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_shutdown___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_Watchdog_shutdown(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_runClientTask_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
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
lean_object* l_Lean_Server_Watchdog_runClientTask_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_runClientTask_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
return x_4;
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_runClientTask___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_runClientTask___lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_runClientTask___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_runClientTask___lambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_runClientTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_IO_FS_Stream_readLspMessage), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_Server_Watchdog_runClientTask___closed__1;
x_6 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_5);
x_7 = l_Task_Priority_default;
x_8 = lean_io_as_task(x_6, x_7, x_2);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Server_Watchdog_runClientTask___closed__2;
x_12 = lean_task_map(x_11, x_10, x_7);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_8);
x_15 = l_Lean_Server_Watchdog_runClientTask___closed__2;
x_16 = lean_task_map(x_15, x_13, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_runClientTask___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_Watchdog_runClientTask___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_mainLoop_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mainLoop_match__2___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("shutdown");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = l_Lean_Server_Watchdog_mainLoop_match__2___rarg___closed__1;
x_10 = lean_string_dec_eq(x_7, x_9);
if (x_10 == 0)
{
lean_dec(x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_11 = lean_apply_1(x_5, x_1);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_apply_3(x_3, x_6, x_7, x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_apply_2(x_2, x_6, x_8);
return x_14;
}
}
case 1:
{
lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_4);
x_16 = lean_apply_1(x_5, x_1);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_apply_2(x_4, x_17, x_18);
return x_19;
}
}
default: 
{
lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_apply_1(x_5, x_1);
return x_20;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_mainLoop_match__2___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Server_Watchdog_mainLoop_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_mainLoop_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_4, x_5, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
}
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_mainLoop_match__4___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_fold___at_Lean_Server_Watchdog_mainLoop___spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Std_RBNode_fold___at_Lean_Server_Watchdog_mainLoop___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Std_RBNode_fold___at_Lean_Server_Watchdog_mainLoop___spec__1(x_1, x_3);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_7);
lean_dec(x_4);
x_1 = x_6;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_4);
x_9 = lean_alloc_closure((void*)(l_Std_RBNode_fold___at_Lean_Server_Watchdog_mainLoop___spec__1___lambda__1), 2, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_Task_Priority_default;
x_12 = lean_task_map(x_9, x_10, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_6);
x_1 = x_13;
x_2 = x_5;
goto _start;
}
}
}
}
lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_IO_FS_Stream_writeLspMessage(x_1, x_6, x_3);
lean_dec(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mainLoop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Internal server error: got termination event for worker that should have been removed");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mainLoop___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Got invalid JSON-RPC message");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_mainLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 4);
lean_inc(x_4);
x_5 = lean_st_ref_get(x_4, x_3);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_Std_RBNode_fold___at_Lean_Server_Watchdog_mainLoop___spec__1(x_8, x_6);
lean_inc(x_1);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_io_wait_any(x_10, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Server_Watchdog_mainLoop___closed__1;
x_16 = l_IO_throwServerError___rarg(x_15, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_13);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Array_empty___closed__1;
x_23 = l_Lean_Server_Watchdog_handleCrash(x_21, x_22, x_2, x_17);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_3 = x_24;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
case 1:
{
lean_object* x_30; 
lean_dec(x_1);
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
lean_dec(x_12);
switch (lean_obj_tag(x_30)) {
case 0:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_dec(x_11);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 2);
lean_inc(x_34);
lean_dec(x_30);
x_35 = l_Lean_Server_Watchdog_mainLoop_match__2___rarg___closed__1;
x_36 = lean_string_dec_eq(x_33, x_35);
if (x_36 == 0)
{
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_2);
x_37 = l_Lean_Server_Watchdog_mainLoop___closed__2;
x_38 = l_IO_throwServerError___rarg(x_37, x_31);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
lean_dec(x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_inc(x_2);
x_42 = l_Lean_Server_Watchdog_handleRequest(x_32, x_33, x_41, x_2, x_31);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_2);
x_44 = l_Lean_Server_Watchdog_runClientTask(x_2, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_1 = x_45;
x_3 = x_46;
goto _start;
}
else
{
uint8_t x_48; 
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
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
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_39, 0);
lean_inc(x_56);
lean_dec(x_39);
x_57 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_inc(x_2);
x_58 = l_Lean_Server_Watchdog_handleRequest(x_32, x_33, x_57, x_2, x_31);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
lean_inc(x_2);
x_60 = l_Lean_Server_Watchdog_runClientTask(x_2, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_1 = x_61;
x_3 = x_62;
goto _start;
}
else
{
uint8_t x_64; 
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
return x_60;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_60, 0);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_60);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_58);
if (x_68 == 0)
{
return x_58;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_58, 0);
x_70 = lean_ctor_get(x_58, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_58);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
else
{
lean_object* x_72; 
lean_dec(x_34);
lean_dec(x_33);
x_72 = l_Lean_Server_Watchdog_shutdown(x_2, x_31);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_ctor_get(x_2, 1);
lean_inc(x_74);
lean_dec(x_2);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_32);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__2(x_74, x_76, x_73);
lean_dec(x_76);
return x_77;
}
else
{
uint8_t x_78; 
lean_dec(x_32);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_72);
if (x_78 == 0)
{
return x_72;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_72, 0);
x_80 = lean_ctor_get(x_72, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_72);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
case 1:
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_30, 1);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_30);
lean_dec(x_2);
x_83 = lean_ctor_get(x_11, 1);
lean_inc(x_83);
lean_dec(x_11);
x_84 = l_Lean_Server_Watchdog_mainLoop___closed__2;
x_85 = l_IO_throwServerError___rarg(x_84, x_83);
return x_85;
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec(x_82);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_11, 1);
lean_inc(x_87);
lean_dec(x_11);
x_88 = lean_ctor_get(x_30, 0);
lean_inc(x_88);
lean_dec(x_30);
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_90, 0, x_89);
lean_inc(x_2);
x_91 = l_Lean_Server_Watchdog_handleNotification(x_88, x_90, x_2, x_87);
lean_dec(x_88);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
lean_inc(x_2);
x_93 = l_Lean_Server_Watchdog_runClientTask(x_2, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_1 = x_94;
x_3 = x_95;
goto _start;
}
else
{
uint8_t x_97; 
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_93);
if (x_97 == 0)
{
return x_93;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_93, 0);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_93);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_2);
x_101 = !lean_is_exclusive(x_91);
if (x_101 == 0)
{
return x_91;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_91, 0);
x_103 = lean_ctor_get(x_91, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_91);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_11, 1);
lean_inc(x_105);
lean_dec(x_11);
x_106 = lean_ctor_get(x_30, 0);
lean_inc(x_106);
lean_dec(x_30);
x_107 = lean_ctor_get(x_86, 0);
lean_inc(x_107);
lean_dec(x_86);
x_108 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_108, 0, x_107);
lean_inc(x_2);
x_109 = l_Lean_Server_Watchdog_handleNotification(x_106, x_108, x_2, x_105);
lean_dec(x_106);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
lean_inc(x_2);
x_111 = l_Lean_Server_Watchdog_runClientTask(x_2, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_1 = x_112;
x_3 = x_113;
goto _start;
}
else
{
uint8_t x_115; 
lean_dec(x_2);
x_115 = !lean_is_exclusive(x_111);
if (x_115 == 0)
{
return x_111;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_111, 0);
x_117 = lean_ctor_get(x_111, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_111);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_2);
x_119 = !lean_is_exclusive(x_109);
if (x_119 == 0)
{
return x_109;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_109, 0);
x_121 = lean_ctor_get(x_109, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_109);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
}
default: 
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_30);
lean_dec(x_2);
x_123 = lean_ctor_get(x_11, 1);
lean_inc(x_123);
lean_dec(x_11);
x_124 = l_Lean_Server_Watchdog_mainLoop___closed__2;
x_125 = l_IO_throwServerError___rarg(x_124, x_123);
return x_125;
}
}
}
default: 
{
uint8_t x_126; 
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_11);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_11, 0);
lean_dec(x_127);
x_128 = lean_ctor_get(x_12, 0);
lean_inc(x_128);
lean_dec(x_12);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_128);
return x_11;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_11, 1);
lean_inc(x_129);
lean_dec(x_11);
x_130 = lean_ctor_get(x_12, 0);
lean_inc(x_130);
lean_dec(x_12);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_11);
if (x_132 == 0)
{
return x_11;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_11, 0);
x_134 = lean_ctor_get(x_11, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_11);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_mainLoop___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = 2;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 2, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__2;
x_2 = 1;
x_3 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__3;
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = l_Lean_Parser_Command_exit___elambda__1___closed__1;
x_7 = lean_string_dec_eq(x_4, x_6);
lean_dec(x_4);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_1);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_2, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_2);
lean_ctor_set(x_1, 0, x_6);
x_14 = lean_apply_1(x_3, x_1);
return x_14;
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_2, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_apply_1(x_3, x_17);
return x_18;
}
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_2);
x_19 = lean_apply_1(x_3, x_1);
return x_19;
}
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_initAndRunWatchdogAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readMessage(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_18 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_17, x_11);
lean_dec(x_11);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_16);
x_24 = l_List_append___rarg(x_23, x_18);
x_25 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Json_mkObj(x_26);
x_28 = l_Lean_Json_compress(x_27);
x_29 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Char_quote___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_33);
return x_5;
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_34 = lean_ctor_get(x_9, 0);
lean_inc(x_34);
lean_dec(x_9);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_16);
x_39 = l_List_append___rarg(x_38, x_18);
x_40 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Json_mkObj(x_41);
x_43 = l_Lean_Json_compress(x_42);
x_44 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_45 = lean_string_append(x_44, x_43);
lean_dec(x_43);
x_46 = l_Char_quote___closed__1;
x_47 = lean_string_append(x_45, x_46);
x_48 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_48);
return x_5;
}
default: 
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_49 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_16);
x_51 = l_List_append___rarg(x_50, x_18);
x_52 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Json_mkObj(x_53);
x_55 = l_Lean_Json_compress(x_54);
x_56 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = l_Char_quote___closed__1;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_60);
return x_5;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
lean_dec(x_5);
x_62 = lean_ctor_get(x_6, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_6, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_6, 2);
lean_inc(x_64);
lean_dec(x_6);
x_65 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_65, 0, x_63);
x_66 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_71 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_70, x_64);
lean_dec(x_64);
switch (lean_obj_tag(x_62)) {
case 0:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_72 = lean_ctor_get(x_62, 0);
lean_inc(x_72);
lean_dec(x_62);
x_73 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
x_77 = l_List_append___rarg(x_76, x_71);
x_78 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_Json_mkObj(x_79);
x_81 = l_Lean_Json_compress(x_80);
x_82 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_83 = lean_string_append(x_82, x_81);
lean_dec(x_81);
x_84 = l_Char_quote___closed__1;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_61);
return x_87;
}
case 1:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_88 = lean_ctor_get(x_62, 0);
lean_inc(x_88);
lean_dec(x_62);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_69);
x_93 = l_List_append___rarg(x_92, x_71);
x_94 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Json_mkObj(x_95);
x_97 = l_Lean_Json_compress(x_96);
x_98 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_99 = lean_string_append(x_98, x_97);
lean_dec(x_97);
x_100 = l_Char_quote___closed__1;
x_101 = lean_string_append(x_99, x_100);
x_102 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_61);
return x_103;
}
default: 
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_104 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_69);
x_106 = l_List_append___rarg(x_105, x_71);
x_107 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Json_mkObj(x_108);
x_110 = l_Lean_Json_compress(x_109);
x_111 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_112 = lean_string_append(x_111, x_110);
lean_dec(x_110);
x_113 = l_Char_quote___closed__1;
x_114 = lean_string_append(x_112, x_113);
x_115 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_61);
return x_116;
}
}
}
}
case 1:
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_5);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_5, 0);
lean_dec(x_118);
x_119 = lean_ctor_get(x_6, 0);
lean_inc(x_119);
lean_dec(x_6);
x_120 = lean_string_dec_eq(x_119, x_3);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_121 = l_IO_FS_Stream_readRequestAs___closed__1;
x_122 = lean_string_append(x_121, x_3);
lean_dec(x_3);
x_123 = l_IO_FS_Stream_readRequestAs___closed__2;
x_124 = lean_string_append(x_122, x_123);
x_125 = lean_string_append(x_124, x_119);
lean_dec(x_119);
x_126 = l_Char_quote___closed__1;
x_127 = lean_string_append(x_125, x_126);
x_128 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_128);
return x_5;
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_119);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_3);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_5, 0, x_130);
return x_5;
}
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = lean_ctor_get(x_5, 1);
lean_inc(x_131);
lean_dec(x_5);
x_132 = lean_ctor_get(x_6, 0);
lean_inc(x_132);
lean_dec(x_6);
x_133 = lean_string_dec_eq(x_132, x_3);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_134 = l_IO_FS_Stream_readRequestAs___closed__1;
x_135 = lean_string_append(x_134, x_3);
lean_dec(x_3);
x_136 = l_IO_FS_Stream_readRequestAs___closed__2;
x_137 = lean_string_append(x_135, x_136);
x_138 = lean_string_append(x_137, x_132);
lean_dec(x_132);
x_139 = l_Char_quote___closed__1;
x_140 = lean_string_append(x_138, x_139);
x_141 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_131);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_132);
x_143 = lean_box(0);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_3);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_131);
return x_145;
}
}
}
case 2:
{
uint8_t x_146; 
lean_dec(x_3);
x_146 = !lean_is_exclusive(x_5);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_147 = lean_ctor_get(x_5, 0);
lean_dec(x_147);
x_148 = lean_ctor_get(x_6, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_6, 1);
lean_inc(x_149);
lean_dec(x_6);
x_150 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
switch (lean_obj_tag(x_148)) {
case 0:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_154 = lean_ctor_get(x_148, 0);
lean_inc(x_154);
lean_dec(x_148);
x_155 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_153);
x_159 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = l_Lean_Json_mkObj(x_160);
x_162 = l_Lean_Json_compress(x_161);
x_163 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_164 = lean_string_append(x_163, x_162);
lean_dec(x_162);
x_165 = l_Char_quote___closed__1;
x_166 = lean_string_append(x_164, x_165);
x_167 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_167);
return x_5;
}
case 1:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_168 = lean_ctor_get(x_148, 0);
lean_inc(x_168);
lean_dec(x_148);
x_169 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_153);
x_173 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
x_175 = l_Lean_Json_mkObj(x_174);
x_176 = l_Lean_Json_compress(x_175);
x_177 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_178 = lean_string_append(x_177, x_176);
lean_dec(x_176);
x_179 = l_Char_quote___closed__1;
x_180 = lean_string_append(x_178, x_179);
x_181 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_181);
return x_5;
}
default: 
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_182 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_153);
x_184 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
x_186 = l_Lean_Json_mkObj(x_185);
x_187 = l_Lean_Json_compress(x_186);
x_188 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_189 = lean_string_append(x_188, x_187);
lean_dec(x_187);
x_190 = l_Char_quote___closed__1;
x_191 = lean_string_append(x_189, x_190);
x_192 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_192);
return x_5;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_193 = lean_ctor_get(x_5, 1);
lean_inc(x_193);
lean_dec(x_5);
x_194 = lean_ctor_get(x_6, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_6, 1);
lean_inc(x_195);
lean_dec(x_6);
x_196 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
x_198 = lean_box(0);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
switch (lean_obj_tag(x_194)) {
case 0:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_200 = lean_ctor_get(x_194, 0);
lean_inc(x_200);
lean_dec(x_194);
x_201 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_201, 0, x_200);
x_202 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_199);
x_205 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_204);
x_207 = l_Lean_Json_mkObj(x_206);
x_208 = l_Lean_Json_compress(x_207);
x_209 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_210 = lean_string_append(x_209, x_208);
lean_dec(x_208);
x_211 = l_Char_quote___closed__1;
x_212 = lean_string_append(x_210, x_211);
x_213 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_193);
return x_214;
}
case 1:
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_215 = lean_ctor_get(x_194, 0);
lean_inc(x_215);
lean_dec(x_194);
x_216 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_217 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_216);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_199);
x_220 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
x_222 = l_Lean_Json_mkObj(x_221);
x_223 = l_Lean_Json_compress(x_222);
x_224 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_225 = lean_string_append(x_224, x_223);
lean_dec(x_223);
x_226 = l_Char_quote___closed__1;
x_227 = lean_string_append(x_225, x_226);
x_228 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_228, 0, x_227);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_193);
return x_229;
}
default: 
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_230 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_199);
x_232 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
x_234 = l_Lean_Json_mkObj(x_233);
x_235 = l_Lean_Json_compress(x_234);
x_236 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_237 = lean_string_append(x_236, x_235);
lean_dec(x_235);
x_238 = l_Char_quote___closed__1;
x_239 = lean_string_append(x_237, x_238);
x_240 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_240, 0, x_239);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_193);
return x_241;
}
}
}
}
default: 
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_3);
x_242 = lean_ctor_get(x_5, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_243 = x_5;
} else {
 lean_dec_ref(x_5);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_6, 0);
lean_inc(x_244);
x_245 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_246 = lean_ctor_get(x_6, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_6, 2);
lean_inc(x_247);
lean_dec(x_6);
x_248 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_248, 0, x_246);
x_249 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_248);
x_251 = lean_box(0);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_254 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_253, x_247);
lean_dec(x_247);
switch (lean_obj_tag(x_244)) {
case 0:
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_244, 0);
lean_inc(x_291);
lean_dec(x_244);
x_292 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_292, 0, x_291);
x_255 = x_292;
goto block_290;
}
case 1:
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_244, 0);
lean_inc(x_293);
lean_dec(x_244);
x_294 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_294, 0, x_293);
x_255 = x_294;
goto block_290;
}
default: 
{
lean_object* x_295; 
x_295 = lean_box(0);
x_255 = x_295;
goto block_290;
}
}
block_290:
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_255);
switch (x_245) {
case 0:
{
lean_object* x_279; 
x_279 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_258 = x_279;
goto block_278;
}
case 1:
{
lean_object* x_280; 
x_280 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_258 = x_280;
goto block_278;
}
case 2:
{
lean_object* x_281; 
x_281 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_258 = x_281;
goto block_278;
}
case 3:
{
lean_object* x_282; 
x_282 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_258 = x_282;
goto block_278;
}
case 4:
{
lean_object* x_283; 
x_283 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_258 = x_283;
goto block_278;
}
case 5:
{
lean_object* x_284; 
x_284 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_258 = x_284;
goto block_278;
}
case 6:
{
lean_object* x_285; 
x_285 = l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
x_258 = x_285;
goto block_278;
}
case 7:
{
lean_object* x_286; 
x_286 = l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
x_258 = x_286;
goto block_278;
}
case 8:
{
lean_object* x_287; 
x_287 = l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
x_258 = x_287;
goto block_278;
}
case 9:
{
lean_object* x_288; 
x_288 = l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
x_258 = x_288;
goto block_278;
}
default: 
{
lean_object* x_289; 
x_289 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
x_258 = x_289;
goto block_278;
}
}
block_278:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_259 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_258);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_252);
x_262 = l_List_append___rarg(x_261, x_254);
x_263 = l_Lean_Json_mkObj(x_262);
x_264 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_263);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_251);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_257);
lean_ctor_set(x_267, 1, x_266);
x_268 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
x_270 = l_Lean_Json_mkObj(x_269);
x_271 = l_Lean_Json_compress(x_270);
x_272 = l_IO_FS_Stream_readNotificationAs___closed__1;
x_273 = lean_string_append(x_272, x_271);
lean_dec(x_271);
x_274 = l_Char_quote___closed__1;
x_275 = lean_string_append(x_273, x_274);
x_276 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_276, 0, x_275);
if (lean_is_scalar(x_243)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_243;
 lean_ctor_set_tag(x_277, 1);
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_242);
return x_277;
}
}
}
}
}
else
{
uint8_t x_296; 
lean_dec(x_3);
x_296 = !lean_is_exclusive(x_5);
if (x_296 == 0)
{
return x_5;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_5, 0);
x_298 = lean_ctor_get(x_5, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_5);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
}
lean_object* l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2(x_1, x_5, x_2, x_6);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_io_error_to_string(x_9);
x_11 = l_IO_FS_Stream_readLspNotificationAs___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_instInhabitedParserDescr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_io_error_to_string(x_16);
x_19 = l_IO_FS_Stream_readLspNotificationAs___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_instInhabitedParserDescr___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_io_error_to_string(x_26);
x_28 = l_IO_FS_Stream_readLspNotificationAs___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_instInhabitedParserDescr___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_4, 0, x_32);
return x_4;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = lean_io_error_to_string(x_33);
x_36 = l_IO_FS_Stream_readLspNotificationAs___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_instInhabitedParserDescr___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("initialized");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Expected an exit notification");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdogAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_16 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1;
lean_inc(x_3);
x_17 = l_IO_FS_Stream_readLspNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__1(x_3, x_16, x_2);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_1);
x_19 = l_Lean_Server_Watchdog_runClientTask(x_1, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_1);
x_22 = l_Lean_Server_Watchdog_mainLoop(x_20, x_1, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_IO_FS_Stream_readLspMessage(x_3, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 1)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = l_Lean_Parser_Command_exit___elambda__1___closed__1;
x_32 = lean_string_dec_eq(x_29, x_31);
lean_dec(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_30);
lean_free_object(x_24);
x_33 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2;
x_34 = l_IO_throwServerError___rarg(x_33, x_27);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_4 = x_35;
x_5 = x_36;
goto block_15;
}
else
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_37; 
lean_dec(x_1);
x_37 = lean_box(0);
lean_ctor_set(x_24, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_30);
lean_free_object(x_24);
x_38 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2;
x_39 = l_IO_throwServerError___rarg(x_38, x_27);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_4 = x_40;
x_5 = x_41;
goto block_15;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_25, 1);
lean_inc(x_44);
lean_dec(x_25);
x_45 = l_Lean_Parser_Command_exit___elambda__1___closed__1;
x_46 = lean_string_dec_eq(x_43, x_45);
lean_dec(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_44);
x_47 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2;
x_48 = l_IO_throwServerError___rarg(x_47, x_42);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_4 = x_49;
x_5 = x_50;
goto block_15;
}
else
{
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_1);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_42);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_44);
x_53 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2;
x_54 = l_IO_throwServerError___rarg(x_53, x_42);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_4 = x_55;
x_5 = x_56;
goto block_15;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_25);
x_57 = lean_ctor_get(x_24, 1);
lean_inc(x_57);
lean_dec(x_24);
x_58 = l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2;
x_59 = l_IO_throwServerError___rarg(x_58, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_4 = x_60;
x_5 = x_61;
goto block_15;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_24, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_24, 1);
lean_inc(x_63);
lean_dec(x_24);
x_4 = x_62;
x_5 = x_63;
goto block_15;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_3);
x_64 = lean_ctor_get(x_22, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_dec(x_22);
x_4 = x_64;
x_5 = x_65;
goto block_15;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_3);
x_66 = lean_ctor_get(x_19, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_19, 1);
lean_inc(x_67);
lean_dec(x_19);
x_4 = x_66;
x_5 = x_67;
goto block_15;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_3);
x_68 = lean_ctor_get(x_17, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_17, 1);
lean_inc(x_69);
lean_dec(x_17);
x_4 = x_68;
x_5 = x_69;
goto block_15;
}
block_15:
{
lean_object* x_6; 
x_6 = l_Lean_Server_Watchdog_shutdown(x_1, x_5);
lean_dec(x_1);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_4);
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
}
lean_object* l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readNotificationAs___at_Lean_Server_Watchdog_initAndRunWatchdogAux___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_initAndRunWatchdog_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_Watchdog_initAndRunWatchdog_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_mkRef___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readMessage(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_string_dec_eq(x_10, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_9);
x_13 = l_IO_FS_Stream_readRequestAs___closed__1;
x_14 = lean_string_append(x_13, x_3);
lean_dec(x_3);
x_15 = l_IO_FS_Stream_readRequestAs___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_10);
lean_dec(x_10);
x_18 = l_Char_quote___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
if (lean_is_scalar(x_8)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_8;
 lean_ctor_set_tag(x_21, 1);
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_47; 
x_47 = lean_box(0);
x_22 = x_47;
goto block_46;
}
else
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_11, 0);
lean_inc(x_48);
lean_dec(x_11);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_22 = x_50;
goto block_46;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_22 = x_52;
goto block_46;
}
}
block_46:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_165____closed__1;
x_24 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__1(x_22, x_23);
x_25 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_165____closed__2;
x_26 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__2(x_22, x_25);
x_27 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_165____closed__3;
x_28 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__2(x_22, x_27);
x_29 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_165____closed__4;
x_30 = l_Lean_Json_getObjVal_x3f(x_22, x_29);
x_31 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_165____closed__9;
x_32 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__4(x_22, x_31);
x_33 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeParams____x40_Lean_Data_Lsp_InitShutdown___hyg_165____closed__8;
x_34 = l_Lean_Json_getObjValAs_x3f___at_Lean_Lsp_instFromJsonInitializeParams___spec__5(x_22, x_33);
lean_dec(x_22);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_box(0);
x_36 = 0;
x_37 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_26);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 3, x_30);
lean_ctor_set(x_37, 4, x_35);
lean_ctor_set(x_37, 5, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*6, x_36);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_9);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_37);
if (lean_is_scalar(x_8)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_8;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_7);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_26);
lean_ctor_set(x_42, 2, x_28);
lean_ctor_set(x_42, 3, x_30);
lean_ctor_set(x_42, 4, x_41);
lean_ctor_set(x_42, 5, x_34);
x_43 = lean_unbox(x_40);
lean_dec(x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*6, x_43);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_9);
lean_ctor_set(x_44, 1, x_3);
lean_ctor_set(x_44, 2, x_42);
if (lean_is_scalar(x_8)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_8;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_7);
return x_45;
}
}
}
}
case 1:
{
uint8_t x_53; 
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_5);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_54 = lean_ctor_get(x_5, 0);
lean_dec(x_54);
x_55 = lean_ctor_get(x_6, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_6, 1);
lean_inc(x_56);
lean_dec(x_6);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_55);
x_58 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_61 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_60, x_56);
lean_dec(x_56);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Lean_Json_mkObj(x_64);
x_66 = l_Lean_Json_compress(x_65);
x_67 = l_IO_FS_Stream_readRequestAs___closed__5;
x_68 = lean_string_append(x_67, x_66);
lean_dec(x_66);
x_69 = l_Char_quote___closed__1;
x_70 = lean_string_append(x_68, x_69);
x_71 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_71);
return x_5;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_72 = lean_ctor_get(x_5, 1);
lean_inc(x_72);
lean_dec(x_5);
x_73 = lean_ctor_get(x_6, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_6, 1);
lean_inc(x_74);
lean_dec(x_6);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_73);
x_76 = l_Lean_JsonRpc_instToJsonMessage___closed__5;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_JsonRpc_instToJsonMessage___closed__6;
x_79 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__1(x_78, x_74);
lean_dec(x_74);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Lean_Json_mkObj(x_82);
x_84 = l_Lean_Json_compress(x_83);
x_85 = l_IO_FS_Stream_readRequestAs___closed__5;
x_86 = lean_string_append(x_85, x_84);
lean_dec(x_84);
x_87 = l_Char_quote___closed__1;
x_88 = lean_string_append(x_86, x_87);
x_89 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_72);
return x_90;
}
}
case 2:
{
uint8_t x_91; 
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_5);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_92 = lean_ctor_get(x_5, 0);
lean_dec(x_92);
x_93 = lean_ctor_get(x_6, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_6, 1);
lean_inc(x_94);
lean_dec(x_6);
x_95 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
switch (lean_obj_tag(x_93)) {
case 0:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_99 = lean_ctor_get(x_93, 0);
lean_inc(x_99);
lean_dec(x_93);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_98);
x_104 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = l_Lean_Json_mkObj(x_105);
x_107 = l_Lean_Json_compress(x_106);
x_108 = l_IO_FS_Stream_readRequestAs___closed__5;
x_109 = lean_string_append(x_108, x_107);
lean_dec(x_107);
x_110 = l_Char_quote___closed__1;
x_111 = lean_string_append(x_109, x_110);
x_112 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_112);
return x_5;
}
case 1:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_113 = lean_ctor_get(x_93, 0);
lean_inc(x_113);
lean_dec(x_93);
x_114 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_98);
x_118 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
x_120 = l_Lean_Json_mkObj(x_119);
x_121 = l_Lean_Json_compress(x_120);
x_122 = l_IO_FS_Stream_readRequestAs___closed__5;
x_123 = lean_string_append(x_122, x_121);
lean_dec(x_121);
x_124 = l_Char_quote___closed__1;
x_125 = lean_string_append(x_123, x_124);
x_126 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_126);
return x_5;
}
default: 
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_127 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_98);
x_129 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = l_Lean_Json_mkObj(x_130);
x_132 = l_Lean_Json_compress(x_131);
x_133 = l_IO_FS_Stream_readRequestAs___closed__5;
x_134 = lean_string_append(x_133, x_132);
lean_dec(x_132);
x_135 = l_Char_quote___closed__1;
x_136 = lean_string_append(x_134, x_135);
x_137 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_137);
return x_5;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_138 = lean_ctor_get(x_5, 1);
lean_inc(x_138);
lean_dec(x_5);
x_139 = lean_ctor_get(x_6, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_6, 1);
lean_inc(x_140);
lean_dec(x_6);
x_141 = l_Lean_JsonRpc_instToJsonMessage___closed__9;
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = lean_box(0);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
switch (lean_obj_tag(x_139)) {
case 0:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_145 = lean_ctor_get(x_139, 0);
lean_inc(x_145);
lean_dec(x_139);
x_146 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_144);
x_150 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
x_152 = l_Lean_Json_mkObj(x_151);
x_153 = l_Lean_Json_compress(x_152);
x_154 = l_IO_FS_Stream_readRequestAs___closed__5;
x_155 = lean_string_append(x_154, x_153);
lean_dec(x_153);
x_156 = l_Char_quote___closed__1;
x_157 = lean_string_append(x_155, x_156);
x_158 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_138);
return x_159;
}
case 1:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_160 = lean_ctor_get(x_139, 0);
lean_inc(x_160);
lean_dec(x_139);
x_161 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_144);
x_165 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = l_Lean_Json_mkObj(x_166);
x_168 = l_Lean_Json_compress(x_167);
x_169 = l_IO_FS_Stream_readRequestAs___closed__5;
x_170 = lean_string_append(x_169, x_168);
lean_dec(x_168);
x_171 = l_Char_quote___closed__1;
x_172 = lean_string_append(x_170, x_171);
x_173 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_138);
return x_174;
}
default: 
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_175 = l_Lean_JsonRpc_instToJsonMessage___closed__8;
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_144);
x_177 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
x_179 = l_Lean_Json_mkObj(x_178);
x_180 = l_Lean_Json_compress(x_179);
x_181 = l_IO_FS_Stream_readRequestAs___closed__5;
x_182 = lean_string_append(x_181, x_180);
lean_dec(x_180);
x_183 = l_Char_quote___closed__1;
x_184 = lean_string_append(x_182, x_183);
x_185 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_185, 0, x_184);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_138);
return x_186;
}
}
}
}
default: 
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_3);
x_187 = lean_ctor_get(x_5, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_188 = x_5;
} else {
 lean_dec_ref(x_5);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_6, 0);
lean_inc(x_189);
x_190 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
x_191 = lean_ctor_get(x_6, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_6, 2);
lean_inc(x_192);
lean_dec(x_6);
x_193 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_193, 0, x_191);
x_194 = l_Lean_JsonRpc_instToJsonMessage___closed__10;
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
x_196 = lean_box(0);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_198 = l_Lean_JsonRpc_instToJsonMessage___closed__11;
x_199 = l_Lean_Json_opt___at_Lean_JsonRpc_instToJsonMessage___spec__2(x_198, x_192);
lean_dec(x_192);
switch (lean_obj_tag(x_189)) {
case 0:
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_189, 0);
lean_inc(x_236);
lean_dec(x_189);
x_237 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_237, 0, x_236);
x_200 = x_237;
goto block_235;
}
case 1:
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_189, 0);
lean_inc(x_238);
lean_dec(x_189);
x_239 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_239, 0, x_238);
x_200 = x_239;
goto block_235;
}
default: 
{
lean_object* x_240; 
x_240 = lean_box(0);
x_200 = x_240;
goto block_235;
}
}
block_235:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = l_Lean_JsonRpc_instToJsonMessage___closed__7;
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_200);
switch (x_190) {
case 0:
{
lean_object* x_224; 
x_224 = l_Lean_JsonRpc_instToJsonErrorCode___closed__4;
x_203 = x_224;
goto block_223;
}
case 1:
{
lean_object* x_225; 
x_225 = l_Lean_JsonRpc_instToJsonErrorCode___closed__8;
x_203 = x_225;
goto block_223;
}
case 2:
{
lean_object* x_226; 
x_226 = l_Lean_JsonRpc_instToJsonErrorCode___closed__12;
x_203 = x_226;
goto block_223;
}
case 3:
{
lean_object* x_227; 
x_227 = l_Lean_JsonRpc_instToJsonErrorCode___closed__16;
x_203 = x_227;
goto block_223;
}
case 4:
{
lean_object* x_228; 
x_228 = l_Lean_JsonRpc_instToJsonErrorCode___closed__20;
x_203 = x_228;
goto block_223;
}
case 5:
{
lean_object* x_229; 
x_229 = l_Lean_JsonRpc_instToJsonErrorCode___closed__24;
x_203 = x_229;
goto block_223;
}
case 6:
{
lean_object* x_230; 
x_230 = l_Lean_JsonRpc_instToJsonErrorCode___closed__28;
x_203 = x_230;
goto block_223;
}
case 7:
{
lean_object* x_231; 
x_231 = l_Lean_JsonRpc_instToJsonErrorCode___closed__32;
x_203 = x_231;
goto block_223;
}
case 8:
{
lean_object* x_232; 
x_232 = l_Lean_JsonRpc_instToJsonErrorCode___closed__36;
x_203 = x_232;
goto block_223;
}
case 9:
{
lean_object* x_233; 
x_233 = l_Lean_JsonRpc_instToJsonErrorCode___closed__40;
x_203 = x_233;
goto block_223;
}
default: 
{
lean_object* x_234; 
x_234 = l_Lean_JsonRpc_instToJsonErrorCode___closed__44;
x_203 = x_234;
goto block_223;
}
}
block_223:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_204 = l_Lean_JsonRpc_instToJsonMessage___closed__12;
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_203);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_197);
x_207 = l_List_append___rarg(x_206, x_199);
x_208 = l_Lean_Json_mkObj(x_207);
x_209 = l_Lean_JsonRpc_instToJsonMessage___closed__13;
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_196);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_202);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_JsonRpc_instToJsonMessage___closed__4;
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_212);
x_215 = l_Lean_Json_mkObj(x_214);
x_216 = l_Lean_Json_compress(x_215);
x_217 = l_IO_FS_Stream_readRequestAs___closed__5;
x_218 = lean_string_append(x_217, x_216);
lean_dec(x_216);
x_219 = l_Char_quote___closed__1;
x_220 = lean_string_append(x_218, x_219);
x_221 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_221, 0, x_220);
if (lean_is_scalar(x_188)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_188;
 lean_ctor_set_tag(x_222, 1);
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_187);
return x_222;
}
}
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_3);
x_241 = !lean_is_exclusive(x_5);
if (x_241 == 0)
{
return x_5;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_5, 0);
x_243 = lean_ctor_get(x_5, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_5);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
}
lean_object* l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__3(x_1, x_5, x_2, x_6);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_io_error_to_string(x_9);
x_11 = l_IO_FS_Stream_readLspRequestAs___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_instInhabitedParserDescr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_io_error_to_string(x_16);
x_19 = l_IO_FS_Stream_readLspRequestAs___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_Lean_instInhabitedParserDescr___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_io_error_to_string(x_26);
x_28 = l_IO_FS_Stream_readLspRequestAs___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_instInhabitedParserDescr___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_4, 0, x_32);
return x_4;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = lean_io_error_to_string(x_33);
x_36 = l_IO_FS_Stream_readLspRequestAs___closed__1;
x_37 = lean_string_append(x_36, x_35);
lean_dec(x_35);
x_38 = l_Lean_instInhabitedParserDescr___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
}
}
}
lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l___private_Lean_Data_Lsp_InitShutdown_0__Lean_Lsp_toJsonInitializeResult____x40_Lean_Data_Lsp_InitShutdown___hyg_395_(x_5);
lean_inc(x_4);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_IO_FS_Stream_writeLspMessage(x_1, x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("wdIn.txt");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("wdOut.txt");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("wdErr.txt");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("0.0.1");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Lsp_msgToDiagnostic___closed__1;
x_2 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Watchdog_mkLeanServerCapabilities;
x_2 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_8 = lean_box(0);
x_9 = l_IO_mkRef___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__1(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__1;
x_13 = 0;
x_14 = l_Lean_Server_maybeTee(x_12, x_13, x_1, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__2;
x_18 = 1;
x_19 = l_Lean_Server_maybeTee(x_17, x_18, x_2, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__3;
x_23 = l_Lean_Server_maybeTee(x_22, x_18, x_3, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Parser_Command_initialize___elambda__1___closed__1;
lean_inc(x_15);
x_27 = l_IO_FS_Stream_readLspRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__2(x_15, x_26, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 2);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__8;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_20);
x_34 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__4(x_20, x_33, x_29);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_36, 0, x_15);
lean_ctor_set(x_36, 1, x_20);
lean_ctor_set(x_36, 2, x_24);
lean_ctor_set(x_36, 3, x_4);
lean_ctor_set(x_36, 4, x_10);
lean_ctor_set(x_36, 5, x_31);
lean_ctor_set(x_36, 6, x_5);
x_37 = l_Lean_Server_Watchdog_initAndRunWatchdogAux(x_36, x_35);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_31);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
return x_27;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_19);
if (x_50 == 0)
{
return x_19;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_19, 0);
x_52 = lean_ctor_get(x_19, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_19);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_14);
if (x_54 == 0)
{
return x_14;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_14, 0);
x_56 = lean_ctor_get(x_14, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_14);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("LEAN_WORKER_PATH");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2___closed__1;
x_9 = lean_io_getenv(x_8, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1(x_1, x_2, x_3, x_4, x_5, x_12, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1(x_1, x_2, x_3, x_4, x_15, x_16, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("LEAN_SYSROOT");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("/bin/lean");
return x_1;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_io_app_dir(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1;
x_10 = lean_io_getenv(x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2(x_2, x_3, x_4, x_1, x_7, x_13, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l_Lean_instInhabitedParserDescr___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_System_FilePath_exeSuffix;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_string_append(x_22, x_17);
x_24 = lean_box(0);
x_25 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2(x_2, x_3, x_4, x_1, x_23, x_24, x_15);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_6);
if (x_30 == 0)
{
return x_6;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_6, 0);
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_6);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readRequestAs___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeLspResponse___at_Lean_Server_Watchdog_initAndRunWatchdog___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_IO_getStdin___at_Lean_Server_Watchdog_watchdogMain___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_stdin(x_1);
return x_2;
}
}
lean_object* l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_watchdogMain___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 10;
x_6 = lean_string_push(x_2, x_5);
x_7 = lean_apply_2(x_4, x_6, x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_watchdogMain___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Watchdog error: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_watchdogMain___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Watchdog_watchdogMain___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* lean_server_watchdog_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_stdin(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_get_stdout(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_get_stderr(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_Server_Watchdog_initAndRunWatchdog(x_1, x_4, x_7, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = l_Lean_Server_Watchdog_watchdogMain___boxed__const__1;
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = l_Lean_Server_Watchdog_watchdogMain___boxed__const__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_io_error_to_string(x_19);
x_22 = l_Lean_Server_Watchdog_watchdogMain___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lean_instInhabitedParserDescr___closed__1;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_IO_FS_Stream_putStrLn___at_Lean_Server_Watchdog_watchdogMain___spec__2(x_10, x_25, x_20);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = l_Lean_Server_Watchdog_watchdogMain___boxed__const__2;
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = l_Lean_Server_Watchdog_watchdogMain___boxed__const__2;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_9);
if (x_37 == 0)
{
return x_9;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_9, 0);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_9);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_4);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_6);
if (x_41 == 0)
{
return x_6;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_6, 0);
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_6);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_3);
if (x_45 == 0)
{
return x_3;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_3, 0);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_3);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Init_Data_ByteArray(lean_object*);
lean_object* initialize_Std_Data_RBMap(lean_object*);
lean_object* initialize_Lean_Elab_Import(lean_object*);
lean_object* initialize_Lean_Data_Lsp(lean_object*);
lean_object* initialize_Lean_Server_FileSource(lean_object*);
lean_object* initialize_Lean_Server_Utils(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Server_Watchdog(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_RBMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Import(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_FileSource(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Utils(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_Watchdog_workerCfg = _init_l_Lean_Server_Watchdog_workerCfg();
lean_mark_persistent(l_Lean_Server_Watchdog_workerCfg);
l_Lean_Server_Watchdog_findFileWorker___closed__1 = _init_l_Lean_Server_Watchdog_findFileWorker___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_findFileWorker___closed__1);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__1 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__1();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__1);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__2 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__2();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__2);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__3 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__3();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__3);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__4);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__5 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__5();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages_loop___closed__5);
l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages___closed__1 = _init_l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages___closed__1();
lean_mark_persistent(l___private_Lean_Server_Watchdog_0__Lean_Server_Watchdog_forwardMessages___closed__1);
l_Lean_Server_Watchdog_startFileWorker___closed__1 = _init_l_Lean_Server_Watchdog_startFileWorker___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_startFileWorker___closed__1);
l_Lean_Server_Watchdog_startFileWorker___closed__2 = _init_l_Lean_Server_Watchdog_startFileWorker___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_startFileWorker___closed__2);
l_Lean_Server_Watchdog_startFileWorker___closed__3 = _init_l_Lean_Server_Watchdog_startFileWorker___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_startFileWorker___closed__3);
l_Lean_Server_Watchdog_startFileWorker___closed__4 = _init_l_Lean_Server_Watchdog_startFileWorker___closed__4();
lean_mark_persistent(l_Lean_Server_Watchdog_startFileWorker___closed__4);
l_Lean_Server_Watchdog_startFileWorker___closed__5 = _init_l_Lean_Server_Watchdog_startFileWorker___closed__5();
lean_mark_persistent(l_Lean_Server_Watchdog_startFileWorker___closed__5);
l_Lean_Server_Watchdog_terminateFileWorker___closed__1 = _init_l_Lean_Server_Watchdog_terminateFileWorker___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_terminateFileWorker___closed__1);
l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__1 = _init_l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__1();
l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__2 = _init_l_Lean_Server_Watchdog_tryWriteMessage___rarg___lambda__1___closed__2();
l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__1 = _init_l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__1);
l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__2 = _init_l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__2();
l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__3 = _init_l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___rarg___closed__3);
l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___closed__1 = _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___closed__1);
l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___closed__2 = _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleDidChange___spec__4___closed__2);
l_Lean_Server_Watchdog_handleDidChange___lambda__1___closed__1 = _init_l_Lean_Server_Watchdog_handleDidChange___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleDidChange___lambda__1___closed__1);
l_Lean_Server_Watchdog_handleDidChange___lambda__1___closed__2 = _init_l_Lean_Server_Watchdog_handleDidChange___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_handleDidChange___lambda__1___closed__2);
l_Lean_Server_Watchdog_handleDidChange___closed__1 = _init_l_Lean_Server_Watchdog_handleDidChange___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleDidChange___closed__1);
l_Lean_Server_Watchdog_handleDidChange___closed__2 = _init_l_Lean_Server_Watchdog_handleDidChange___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_handleDidChange___closed__2);
l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___closed__1 = _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___closed__1);
l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___closed__2 = _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleCancelRequest___spec__5___closed__2);
l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8___closed__1 = _init_l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8___closed__1();
lean_mark_persistent(l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8___closed__1);
l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8___closed__2 = _init_l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8___closed__2();
lean_mark_persistent(l_Std_RBNode_forIn_visit___at_Lean_Server_Watchdog_handleCancelRequest___spec__8___closed__2);
l_Lean_Server_Watchdog_parseParams___rarg___closed__1 = _init_l_Lean_Server_Watchdog_parseParams___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_parseParams___rarg___closed__1);
l_Lean_Server_Watchdog_handleRequest_match__1___rarg___closed__1 = _init_l_Lean_Server_Watchdog_handleRequest_match__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest_match__1___rarg___closed__1);
l_Lean_Server_Watchdog_handleRequest_match__1___rarg___closed__2 = _init_l_Lean_Server_Watchdog_handleRequest_match__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest_match__1___rarg___closed__2);
l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___closed__1 = _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___closed__1);
l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___closed__2 = _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__5___closed__2);
l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___closed__1 = _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___closed__1);
l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___closed__2 = _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__12___closed__2);
l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___closed__1 = _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___closed__1);
l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___closed__2 = _init_l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_tryWriteMessage___at_Lean_Server_Watchdog_handleRequest___spec__17___closed__2);
l_Lean_Server_Watchdog_handleRequest___closed__1 = _init_l_Lean_Server_Watchdog_handleRequest___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest___closed__1);
l_Lean_Server_Watchdog_handleRequest___closed__2 = _init_l_Lean_Server_Watchdog_handleRequest___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest___closed__2);
l_Lean_Server_Watchdog_handleRequest___closed__3 = _init_l_Lean_Server_Watchdog_handleRequest___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest___closed__3);
l_Lean_Server_Watchdog_handleRequest___closed__4 = _init_l_Lean_Server_Watchdog_handleRequest___closed__4();
lean_mark_persistent(l_Lean_Server_Watchdog_handleRequest___closed__4);
l_Lean_Server_Watchdog_handleNotification_match__1___rarg___closed__1 = _init_l_Lean_Server_Watchdog_handleNotification_match__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleNotification_match__1___rarg___closed__1);
l_Lean_Server_Watchdog_handleNotification___closed__1 = _init_l_Lean_Server_Watchdog_handleNotification___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_handleNotification___closed__1);
l_Lean_Server_Watchdog_runClientTask___closed__1 = _init_l_Lean_Server_Watchdog_runClientTask___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_runClientTask___closed__1);
l_Lean_Server_Watchdog_runClientTask___closed__2 = _init_l_Lean_Server_Watchdog_runClientTask___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_runClientTask___closed__2);
l_Lean_Server_Watchdog_mainLoop_match__2___rarg___closed__1 = _init_l_Lean_Server_Watchdog_mainLoop_match__2___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_mainLoop_match__2___rarg___closed__1);
l_Lean_Server_Watchdog_mainLoop___closed__1 = _init_l_Lean_Server_Watchdog_mainLoop___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_mainLoop___closed__1);
l_Lean_Server_Watchdog_mainLoop___closed__2 = _init_l_Lean_Server_Watchdog_mainLoop___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_mainLoop___closed__2);
l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__1 = _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__1);
l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__2 = _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__2);
l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__3 = _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_mkLeanServerCapabilities___closed__3);
l_Lean_Server_Watchdog_mkLeanServerCapabilities = _init_l_Lean_Server_Watchdog_mkLeanServerCapabilities();
lean_mark_persistent(l_Lean_Server_Watchdog_mkLeanServerCapabilities);
l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1 = _init_l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__1);
l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2 = _init_l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdogAux___closed__2);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__1 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__1);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__2 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__2);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__3 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__3);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__4 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__4);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__5 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__5);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__6 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__6);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__7 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__7);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__8 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__1___closed__8);
l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2___closed__1 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___lambda__2___closed__1);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__1);
l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2 = _init_l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2();
lean_mark_persistent(l_Lean_Server_Watchdog_initAndRunWatchdog___closed__2);
l_Lean_Server_Watchdog_watchdogMain___closed__1 = _init_l_Lean_Server_Watchdog_watchdogMain___closed__1();
lean_mark_persistent(l_Lean_Server_Watchdog_watchdogMain___closed__1);
l_Lean_Server_Watchdog_watchdogMain___boxed__const__1 = _init_l_Lean_Server_Watchdog_watchdogMain___boxed__const__1();
lean_mark_persistent(l_Lean_Server_Watchdog_watchdogMain___boxed__const__1);
l_Lean_Server_Watchdog_watchdogMain___boxed__const__2 = _init_l_Lean_Server_Watchdog_watchdogMain___boxed__const__2();
lean_mark_persistent(l_Lean_Server_Watchdog_watchdogMain___boxed__const__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
