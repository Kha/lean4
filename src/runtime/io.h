/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Sebastian Ullrich
*/
#pragma once
#include <string>
#include "runtime/object.h"

namespace lean {
b_obj_res get_io_result(b_obj_arg st);
/* `(act : io α) → α` */
obj_res run_io(obj_arg act);
/* `(r : α) → (except ε α × real_world)` */
obj_res mk_ioe_result(obj_arg r);
/* `(e : ε) → (except ε α × real_world)` */
obj_res mk_ioe_failure(obj_arg e);
/* `(s : string) → (except io.error α × real_world)` */
obj_res mk_ioe_failure(std::string const & s);
/* `ioe` produces a result object, or an error.
   If `o` is a result, then we return the result value. */
optional<obj_res> is_ioe_result(obj_arg o);
/* `ioe` produces a result object, or an error.
   If `o` is an error, then we return the io.error value. */
optional<obj_res> is_ioe_error(obj_arg o);
/* Convert an io.error object into a string */
std::string io_error_to_string(obj_arg o);

obj_res io_prim_put_str(b_obj_arg s, obj_arg w);
obj_res io_prim_get_line(obj_arg w);
obj_res io_prim_handle_mk(b_obj_arg s, uint8 mode, uint8 bin, obj_arg w);
obj_res io_prim_handle_is_eof(b_obj_arg h, obj_arg w);
obj_res io_prim_handle_flush(b_obj_arg h, obj_arg w);
obj_res io_prim_handle_close(b_obj_arg h, obj_arg w);
obj_res io_prim_handle_get_line(b_obj_arg h, obj_arg w);
}
