/*
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Sebastian Ullrich
*/
#include "runtime/interrupt.h"
#include "kernel/type_checker.h"
#include "kernel/kernel_exception.h"
#include "library/elab_environment.h"
#include "library/compiler/ir_interpreter.h"

namespace lean {

native_reduce_fn mk_default_native_reduce_fn(elab_environment const & env) {
    return [&env](name const & d) {
        return ir::run_boxed(env, options(), d, 0, nullptr);
    };
}

extern "C" obj_res lean_elab_environment_update_base_after_kernel_add(obj_arg env, obj_arg d, obj_arg kenv);

elab_environment elab_environment::add(declaration const & d, bool check) const {
    native_reduce_fn reduce_fn = mk_default_native_reduce_fn(*this);
    scope_native_reduce_fn _(&reduce_fn);
    environment kenv = to_kernel_env().add(d, check);
    return elab_environment(lean_elab_environment_update_base_after_kernel_add(this->to_obj_arg(), d.to_obj_arg(), kenv.to_obj_arg()));
}

extern "C" LEAN_EXPORT object * lean_elab_add_decl(object * env, size_t max_heartbeat, object * decl,
    object * opt_cancel_tk) {
    scope_max_heartbeat s(max_heartbeat);
    scope_cancel_tk s2(is_scalar(opt_cancel_tk) ? nullptr : cnstr_get(opt_cancel_tk, 0));
    return catch_kernel_exceptions<elab_environment>([&]() {
            return elab_environment(env).add(declaration(decl, true));
        });
}

extern "C" LEAN_EXPORT object * lean_elab_add_decl_without_checking(object * env, object * decl) {
    return catch_kernel_exceptions<elab_environment>([&]() {
            return elab_environment(env).add(declaration(decl, true), false);
        });
}

extern "C" obj_res lean_elab_environment_to_kernel_env(obj_arg);
environment elab_environment::to_kernel_env() const {
    return environment(lean_elab_environment_to_kernel_env(to_obj_arg()));
}

extern "C" obj_res lean_display_stats(obj_arg env, obj_arg w);
void elab_environment::display_stats() const {
    dec_ref(lean_display_stats(to_obj_arg(), io_mk_world()));
}

}
