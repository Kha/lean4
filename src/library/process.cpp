/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Jared Roesch
*/
#include <string>
#include <fstream>
#include <iostream>
#include <iomanip>
#include <utility>

#if defined(LEAN_WINDOWS)
#include <windows.h>
#include <Fcntl.h>
#include <io.h>
#include <tchar.h>
#include <stdio.h>
#include <strsafe.h>
#else
#include <unistd.h>
#include <sys/wait.h>
#endif

#include <lean/object.h>
#include <lean/io.h>
#include "util/array_ref.h"
#include "util/string_ref.h"
#include "util/option_ref.h"
#include "util/pair_ref.h"
#include "util/buffer.h"

namespace lean {

enum stdio {
    PIPED,
    INHERIT,
    NUL,
};

#if defined(LEAN_WINDOWS)

static lean_external_class * g_win_handle_external_class = nullptr;

static void win_handle_finalizer(void * h) {
    CloseHandle(static_cast<HANDLE>(h));
}

static void win_handle_foreach(void * /* mod */, b_obj_arg /* fn */) {
}

lean_object * wrap_win_handle(HANDLE h) {
    return lean_alloc_external(g_win_handle_external_class, static_cast<void *>(h));
}

extern "C" obj_res lean_io_process_child_wait(obj_arg child, obj_arg) {
    HANDLE h = static_cast<HANDLE>(cnstr_get(child, 3 * sizeof(object *)));
    DWORD exit_code;
    WaitForSingleObject(h, INFINITE);
    GetExitCodeProcess(h, &exit_code);
    return lean_mk_io_result(box(exit_code));
}

static FILE * from_win_handle(HANDLE handle, char const * mode) {
    int fd = _open_osfhandle(reinterpret_cast<intptr_t>(handle), _O_APPEND);
    return fdopen(fd, mode);
}

static void setup_stdio(SECURITY_ATTRIBUTES * saAttr, HANDLE * theirs, FILE ** ours, bool in, stdio cfg) {
    /* Setup stdio based on process configuration. */
    switch (cfg) {
    case stdio::INHERIT:
        lean_always_assert(DuplicateHandle(GetCurrentProcess(), *theirs,
                                           GetCurrentProcess(), theirs,
                                           0, TRUE, DUPLICATE_SAME_ACCESS));
        return;
    case stdio::PIPED: {
        HANDLE readh;
        HANDLE writeh;
        if (!CreatePipe(&readh, &writeh, saAttr, 0))
            throw new exception("unable to create pipe");
        *ours = in ? from_win_handle(writeh, "w") : from_win_handle(readh, "r");
        *theirs = in ? readh : writeh;
        lean_always_assert(SetHandleInformation(ours, HANDLE_FLAG_INHERIT, 0));
        return;
    }
    case stdio::NUL:
        /* We should map /dev/null. */
        return;
    }
    lean_unreachable();
}

// This code is adapted from: https://msdn.microsoft.com/en-us/library/windows/desktop/ms682499(v=vs.85).aspx
static obj_res spawn(string_ref const & proc_name, array_ref<string_ref> const & args, stdio stdin_mode, stdio stdout_mode,
                     stdio stderr_mode, option_ref<string_ref> const & cwd, array_ref<pair_ref<string_ref, option_ref<string_ref>>> const & env) {
    HANDLE child_stdin = GetStdHandle(STD_INPUT_HANDLE);
    HANDLE child_stdout = GetStdHandle(STD_OUTPUT_HANDLE);
    HANDLE child_stderr = GetStdHandle(STD_ERROR_HANDLE);

    SECURITY_ATTRIBUTES saAttr;

    // Set the bInheritHandle flag so pipe handles are inherited.
    saAttr.nLength = sizeof(SECURITY_ATTRIBUTES);
    saAttr.bInheritHandle = TRUE;
    saAttr.lpSecurityDescriptor = NULL;

    FILE * parent_stdin  = nullptr; setup_stdio(&saAttr, &child_stdin,  &parent_stdin,  true, stdin_mode);
    FILE * parent_stdout = nullptr; setup_stdio(&saAttr, &child_stdout, &parent_stdout, false, stdout_mode);
    FILE * parent_stderr = nullptr; setup_stdio(&saAttr, &child_stderr, &parent_stderr, false, stderr_mode);

    std::string command;

    // This needs some thought, on Windows we must pass a command string
    // which is a valid command, that is a fully assembled command to be executed.
    //
    // We must escape the arguments to preseving spacing and other characters,
    // we might need to revisit escaping here.
    bool once_through = false;
    for (auto arg : m_args) {
        if (once_through) {
            command += " \"";
        }
        command += arg.data();
        if (once_through) {
            command += "\"";
        }
        once_through = true;
    }

    // Create the child process.
    PROCESS_INFORMATION piProcInfo;
    STARTUPINFO siStartInfo;
    BOOL bSuccess = FALSE;

    // Set up members of the PROCESS_INFORMATION structure.
    ZeroMemory(&piProcInfo, sizeof(PROCESS_INFORMATION));

    // Set up members of the STARTUPINFO structure.
    // This structure specifies the STDIN and STDOUT handles for redirection.

    ZeroMemory(&siStartInfo, sizeof(STARTUPINFO));
    siStartInfo.cb = sizeof(STARTUPINFO);
    siStartInfo.hStdInput = child_stdin;
    siStartInfo.hStdOutput = child_stdout;
    siStartInfo.hStdError = child_stderr;
    siStartInfo.dwFlags |= STARTF_USESTDHANDLES;

    // TODO(gabriel): this is thread-unsafe
    std::unordered_map<std::string, optional<std::string>> old_env_vars;
    for (auto & entry : env) {
        optional<std::string> old;
        if (auto old_val = getenv(entry.first.c_str()))
            old = std::string(old_val);
        old_env_vars[entry.first] = old;

        if (entry.snd()) {
            SetEnvironmentVariable(entry.fst.data(), entry.snd().get()->data());
        } else {
            SetEnvironmentVariable(entry.fst.data(), nullptr);
        }
    }

    // Create the child process.
    bSuccess = CreateProcess(
        NULL,
        command.data(),                      // command line
        NULL,                                // process security attributes
        NULL,                                // primary thread security attributes
        TRUE,                                // handles are inherited
        0,                                   // creation flags
        NULL,                                // use parent's environment
        cwd ? cwd->c_str() : NULL,           // current directory
        &siStartInfo,                        // STARTUPINFO pointer
        &piProcInfo);                        // receives PROCESS_INFORMATION

    for (auto & entry : old_env_vars) {
        SetEnvironmentVariable(entry.first.c_str(), entry.second.c_str());
    }

    // If an error occurs, exit the application.
    if (!bSuccess) {
        throw errno;
    }

    // Close handle to primary thread, we don't need it.
    CloseHandle(piProcInfo.hThread);

    if (stdin_mode  == stdio::PIPED) CloseHandle(child_stdin);
    if (stdout_mode == stdio::PIPED) CloseHandle(child_stdout);
    if (stderr_mode == stdio::PIPED) CloseHandle(child_stderr);

    object_ref r = mk_cnstr(0, io_wrap_handle(parent_stdin), io_wrap_handle(parent_stdout), io_wrap_handle(parent_stderr),
                            wrap_win_handle(piProcInfo.hProcess));
    return lean_mk_io_result(r.steal());
}

void initialize_process() {
    g_win_handle_external_class = lean_register_external_class(win_handle_finalizer, win_handle_foreach);
}
void finalize_process() {}

#else

extern "C" obj_res lean_io_process_child_wait(obj_arg child, obj_arg) {
    static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
    pid_t pid = cnstr_get_uint32(child, 3 * sizeof(object *));
    int status;
    waitpid(pid, &status, 0);
    if (WIFEXITED(status)) {
        return lean_mk_io_result(box(static_cast<unsigned>(WEXITSTATUS(status))));
    } else {
        lean_assert(WIFSIGNALED(status));
        // use bash's convention
        return lean_mk_io_result(box(128 + static_cast<unsigned>(WTERMSIG(status))));
    }
}

struct pipe { int m_read_fd; int m_write_fd; };

static optional<pipe> setup_stdio(stdio cfg) {
    /* Setup stdio based on process configuration. */
    switch (cfg) {
    case stdio::INHERIT:
        /* We should need to do nothing in this case */
        return optional<pipe>();
    case stdio::PIPED:
        int fds[2];
        if (::pipe(fds) == -1) {
            throw errno;
        } else {
            return optional<pipe>(pipe { fds[0], fds[1] });
        }
    case stdio::NUL:
        /* We should map /dev/null. */
        return optional<pipe>();
    }
    lean_unreachable();
}

static obj_res spawn(string_ref const & proc_name, array_ref<string_ref> const & args, stdio stdin_mode, stdio stdout_mode,
  stdio stderr_mode, option_ref<string_ref> const & cwd, array_ref<pair_ref<string_ref, option_ref<string_ref>>> const & env) {
    /* Setup stdio based on process configuration. */
    auto stdin_pipe  = setup_stdio(stdin_mode);
    auto stdout_pipe = setup_stdio(stdout_mode);
    auto stderr_pipe = setup_stdio(stderr_mode);

    int pid = fork();

    if (pid == 0) {
        for (auto & entry : env) {
            if (entry.snd()) {
                setenv(entry.fst().data(), entry.snd().get()->data(), true);
            } else {
                unsetenv(entry.fst().data());
            }
        }

        if (stdin_pipe) {
            dup2(stdin_pipe->m_read_fd, STDIN_FILENO);
            close(stdin_pipe->m_write_fd);
        }

        if (stdout_pipe) {
            dup2(stdout_pipe->m_write_fd, STDOUT_FILENO);
            close(stdout_pipe->m_read_fd);
        }

        if (stderr_pipe) {
            dup2(stderr_pipe->m_write_fd, STDERR_FILENO);
            close(stderr_pipe->m_read_fd);
        }

        if (cwd) {
            if (chdir(cwd.get()->data()) < 0) {
                std::cerr << "could not change directory to " << cwd.get()->data() << std::endl;
                exit(-1);
            }
        }

        buffer<char *> pargs;
        pargs.push_back(strdup(proc_name.data()));
        for (auto & arg : args)
            pargs.push_back(strdup(arg.data()));
        pargs.push_back(NULL);

        if (execvp(pargs[0], pargs.data()) < 0) {
            std::cerr << "could not execute external process" << std::endl;
            exit(-1);
        }
    } else if (pid == -1) {
        throw errno;
    }

    /* We want to setup the parent's view of the file descriptors. */
    FILE * parent_stdin = nullptr, * parent_stdout = nullptr, * parent_stderr = nullptr;

    if (stdin_pipe) {
        close(stdin_pipe->m_read_fd);
        parent_stdin = fdopen(stdin_pipe->m_write_fd, "w");
    }

    if (stdout_pipe) {
        close(stdout_pipe->m_write_fd);
        parent_stdout = fdopen(stdout_pipe->m_read_fd, "r");
    }

    if (stderr_pipe) {
        close(stderr_pipe->m_write_fd);
        parent_stderr = fdopen(stderr_pipe->m_read_fd, "r");
    }

    object_ref r = mk_cnstr(0, io_wrap_handle(parent_stdin), io_wrap_handle(parent_stdout), io_wrap_handle(parent_stderr), sizeof(pid_t));
    static_assert(sizeof(pid_t) == sizeof(uint32), "pid_t is expected to be a 32-bit type"); // NOLINT
    cnstr_set_uint32(r.raw(), 3 * sizeof(object *), pid);
    return lean_mk_io_result(r.steal());
}

void initialize_process() {}
void finalize_process() {}

#endif

extern "C" obj_res lean_io_process_spawn(obj_arg args, obj_arg) {
    stdio stdin_mode  = static_cast<stdio>(cnstr_get_uint8(args, 4 * sizeof(object *) + 0));
    stdio stdout_mode = static_cast<stdio>(cnstr_get_uint8(args, 4 * sizeof(object *) + 1));
    stdio stderr_mode = static_cast<stdio>(cnstr_get_uint8(args, 4 * sizeof(object *) + 2));
    if (stdin_mode == stdio::INHERIT) {
        std::cout.flush();
    }
    try {
        object * r = spawn(
                string_ref(cnstr_get(args, 0)),
                array_ref<string_ref>(cnstr_get(args, 1)),
                stdin_mode,
                stdout_mode,
                stderr_mode,
                option_ref<string_ref>(cnstr_get(args, 2)),
                array_ref<pair_ref<string_ref, option_ref<string_ref>>>(cnstr_get(args, 3)));
        dec(args);
        return r;
    } catch (int err) {
        dec(args);
        return lean_mk_io_error(decode_io_error(err, nullptr));
    }
}

}
