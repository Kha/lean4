/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Sebastian Ullrich
*/
#include <cstdio>
#ifdef _MSC_VER
#include <direct.h>
#define getcwd _getcwd
#define PATH_MAX _MAX_PATH
#else
#include <unistd.h>
#endif
#ifdef __linux__
#include <linux/limits.h>
#endif
#include "runtime/sstream.h"
#include "library/handle.h"
#include "library/process.h"
#include "runtime/io.h"

namespace lean {
static obj_res const REAL_WORLD = box(0);

obj_res mk_io_result(obj_arg r) {
    object * res = alloc_cnstr(0, 2, 0);
    cnstr_set(res, 0, r);
    cnstr_set(res, 1, REAL_WORLD);
    return res;
}
b_obj_res get_io_result(b_obj_arg st) {
    return cnstr_get(st, 0);
}
/* `(act : io α) → α` */
obj_res run_io(obj_arg act) {
    // not implemented yet
    lean_unreachable();
}
/* `(r : α) → (except ε α × real_world)` */
obj_res mk_ioe_result(obj_arg r) {
    object * res = alloc_cnstr(1, 1, 0);
    cnstr_set(res, 0, r);
    return mk_io_result(res);
}
/* `(e : ε) → (except ε α × real_world)` */
obj_res mk_ioe_failure(obj_arg e) {
    object * res = alloc_cnstr(0, 1, 0);
    cnstr_set(res, 0, e);
    return mk_io_result(e);
}
/* `(s : string) → (except io.error α × real_world)` */
obj_res mk_ioe_failure(std::string const & s) {
    return mk_ioe_failure(mk_string(s));
}
obj_res mk_ioe_failure(sstream const & s) {
    return mk_ioe_failure(s.str());
}
/* `ioe` produces a result object, or an error.
   If `o` is a result, then we return the result value. */
optional<obj_res> is_ioe_result(obj_arg o) {
    // not implemented yet
    lean_unreachable();
}
/* `ioe` produces a result object, or an error.
   If `o` is an error, then we return the io.error value. */
optional<obj_res> is_ioe_error(obj_arg o) {
    // not implemented yet
    lean_unreachable();
}
/* Convert an io.error object into a string */
std::string io_error_to_string(obj_arg o) {
    // not implemented yet
    lean_unreachable();
}

obj_res io_prim_put_str(b_obj_arg s, obj_arg /* w */) {
    if ((std::cout << string_to_std(s)).bad())
        return mk_ioe_failure("io.put_str failed");
    else
        return mk_ioe_result(mk_unit_star());
}

obj_res io_prim_get_line(obj_arg /* w */) {
    // not implemented yet
    lean_unreachable();
}

struct vm_handle : public external_object {
    handle_ref m_handle;
    explicit vm_handle(handle_ref const & h):m_handle(h) {}
    explicit vm_handle(handle_ref && h):m_handle(std::move(h)) {}
    virtual ~vm_handle() {}
};

static handle_ref const & to_handle(b_obj_arg o) {
    // lean_vm_check(dynamic_cast<vm_handle*>(to_external(o)));
    return static_cast<vm_handle*>(to_external(o))->m_handle;
}

static obj_res to_obj(handle_ref && h) {
    return new (alloc_heap_object(sizeof(vm_handle))) vm_handle(std::move(h));
}

/*
inductive io.mode
| read | write | read_write | append
*/
char const * to_c_io_mode(uint8 mode, uint8 bin) {
    switch (mode) {
        case 0: return bin ? "rb" : "r";
        case 1: return bin ? "wb" : "w";
        case 2: return bin ? "r+b" : "r+";
        case 3: return bin ? "ab" : "a";
    }
    lean_unreachable();
}

/* handle.mk (s : string) (m : mode) (bin : bool := ff) : eio handle */
obj_res io_prim_handle_mk(b_obj_arg fname, uint8 mode, uint8 bin, obj_arg) {
    FILE * h = fopen(string_to_std(fname).c_str(), to_c_io_mode(mode, bin));
    if (h != nullptr)
        return mk_ioe_result(to_obj(std::make_shared<handle>(h)));
    else
        return mk_ioe_failure(sstream() << "failed to open file '" << to_string(fname) << "'");
}

static obj_res mk_handle_has_been_closed_error() {
    return mk_ioe_failure("invalid io action, handle has been closed");
}

/* handle.is_eof : handle → eio bool */
obj_res io_prim_handle_is_eof(b_obj_arg h, obj_arg /* w */) {
    handle_ref const & href = to_handle(h);
    if (href->is_closed()) return mk_handle_has_been_closed_error();
    bool r = feof(href->m_file) != 0;
    return mk_ioe_result(box(r));
}

/* handle.flush : handle → eio bool */
obj_res io_prim_handle_flush(b_obj_arg h, obj_arg /* w */) {
    handle_ref const & href = to_handle(h);

    if (href->is_closed()) {
        return mk_handle_has_been_closed_error();
    }

    try {
        href->flush();
        return mk_ioe_result(mk_unit_star());
    } catch (handle_exception e) {
        return mk_ioe_failure("flush failed");
    }
}

/* handle.close : handle → eio unit */
obj_res io_prim_handle_close(b_obj_arg h, obj_arg /* w */) {
    handle_ref const & href = to_handle(h);

    if (href->is_closed()) {
        return mk_handle_has_been_closed_error();
    }

    if (href->is_stdin())
        return mk_ioe_failure("close failed, stdin cannot be closed");
    if (href->is_stdout())
        return mk_ioe_failure("close failed, stdout cannot be closed");
    if (href->is_stderr())
        return mk_ioe_failure("close failed, stderr cannot be closed");

    try {
        href->close();
        return mk_ioe_result(mk_unit_star());
    } catch (handle_exception e) {
        return mk_ioe_failure("close failed");
    }
}

/* handle.get_line : handle → eio unit */
obj_res io_prim_handle_get_line(b_obj_arg h, obj_arg /* w */) {
    handle_ref const & href = to_handle(h);

    if (href->is_closed()) {
        return mk_handle_has_been_closed_error();
    }

    std::string r;
    while (true) {
        int c = fgetc(href->m_file);
        if (ferror(href->m_file)) {
            clearerr(href->m_file);
            return mk_ioe_failure("get_line failed");
        }
        if (c == EOF)
            break;
        r.push_back(static_cast<char>(c));
        if (c == '\n')
            break;
    }
    return mk_ioe_result(mk_string(r));
}
}
