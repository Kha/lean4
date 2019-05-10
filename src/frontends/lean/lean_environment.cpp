/*
Copyright (c) 2018 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich

Lean interface to the kernel environment type and extensions
*/

#include <string>
#include <iostream>
#include "runtime/apply.h"
#include "library/replace_visitor.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/annotation.h"
#include "util/timeit.h"
#include "library/locals.h"
#include "library/trace.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/definition_cmds.h"
#include "frontends/lean/brackets.h"
#include "frontends/lean/choice.h"
#include "frontends/lean/inductive_cmds.h"
#include "frontends/lean/structure_cmd.h"
#include "frontends/lean/util.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/simple_pos_info_provider.h"

namespace lean {
void env_finalizer(void * env) {
    delete static_cast<environment*>(env);
}

void env_foreach(void * /* env */, b_obj_arg /* fn */) {
    // TODO(leo, kha)
    throw exception("unimplemented: sharing `environment` across threads");
}

static external_object_class * g_env_class = nullptr;

environment const & to_environment(b_obj_arg o) {
    lean_assert(external_class(o) == g_env_class);
    return *static_cast<environment *>(external_data(o));
}

obj_res to_lean_environment(environment const & env) {
    return alloc_external(g_env_class, new environment(env));
}

static std::vector<object_ref> * g_exts;
static std::vector<object_ref> & get_exts() { return *g_exts; }
static std::unordered_map<std::string, object_ref> * g_persistent_exts;
static std::unordered_map<std::string, object_ref> & get_persistent_exts() { return *g_persistent_exts; };

/** Like `scope_ext`, but using dynamic dispatch instead of a template parameter. */
class lean_env_ext : public object_ref {
    typedef object_ref state;
    typedef object_ref entry;

    unsigned get_ext_id() const { return cnstr_get_scalar<unsigned>(this->raw(), 0); };
    // (key : Option String)
    object_ref const & get_key() const { return cnstr_get_ref(*this, 0); }
    // (empty_state : stateTy)
    object_ref const & get_empty_state() const { return cnstr_get_ref(*this, 1); }
    // (addEntry : Π (init : Bool), environment → stateTy → entryTy → stateTy)
    object_ref const & get_add_entry() const { return cnstr_get_ref(*this, 2); };

    struct data : public environment_extension {
        /* Stack of states, it is updated using push/pop operations */
        list<state> m_scopes;
        state m_state; // explicit top-most (current) scope

        /** \brief Open a namespace/section. It returns the new updated state. */
        data push() const {
            data r(*this);
            r.m_scopes           = cons(m_state, r.m_scopes);
            return r;
        }

        /** \brief Close namespace/section. It returns the new updated state.
            \pre There are open namespaces */
        data pop() const {
            lean_assert(!is_nil(m_scopes));
            data r(*this);
            r.m_state  = head(m_scopes);
            r.m_scopes = tail(m_scopes);
            return r;
        }

        explicit data(object_ref const & state) : m_state(state) {}
    };

    void add_entry(object_ref const & env, io_state const &, state & s, entry const & e) const {
        // TODO: conditionally set `init = true`, and check that it's indeed linear
        object * init = box(0);
        s = object_ref(apply_4(get_add_entry().copy(), env.copy(), init, s.copy(), e.copy()));
    }

    /* Add \c e to all states in \c l. */
    list<state> add_all(object_ref const & env, io_state const & ios, list<state> const & l, entry const & e) const {
        if (is_nil(l)) {
            return l;
        } else {
            state new_s = head(l);
            add_entry(env, ios, new_s, e);
            return cons(new_s, add_all(env, ios, tail(l), e));
        }
    }

    /* Add persistent entry, updating all states with this entry. This method is invoked when importing files. */
    data _register_entry(data const & d, object_ref const & env, io_state const & ios, entry const & e) const {
        data r(d);
        add_entry(env, ios, r.m_state, e);
        r.m_scopes = add_all(env, ios, r.m_scopes, e);
        return r;
    }

    /* Add entry to current state */
    data _add_tmp_entry(data const & d, object_ref const & env, io_state const & ios, entry const & e) const {
        data r(d);
        add_entry(env, ios, r.m_state, e);
        return r;
    }

    struct modification : public lean::modification {
        std::string m_key;
        entry m_entry;

        modification() {}
        modification(std::string const & key, entry const & e) : m_key(key), m_entry(e) {}

        const char * get_key() const override { return m_key.c_str(); }

        void perform(environment & env) const override {
            env = lean_env_ext(get_persistent_exts()[m_key]).register_entry(env, get_global_ios(), m_entry);
        }

        void serialize(serializer & s) const override {
            s << m_key << m_entry.raw();
        }

        static std::shared_ptr<lean::modification const> deserialize(deserializer & d) {
            return std::make_shared<modification>(d.read_string(), object_ref(d.read_object()));
        }
    };
public:
    lean_env_ext(object_ref const & o) : object_ref(o) {}
    lean_env_ext(object_ref const & opt_key, object_ref const & empty_state, object_ref const & add_entry_fn) :
        lean_env_ext(mk_cnstr(0, opt_key.copy(), empty_state.copy(), add_entry_fn.copy())) {
        if (cnstr_tag(opt_key.raw()) == 1) {
            // opt_key = some k
            std::string k = string_to_std(cnstr_get_ref(opt_key, 0).raw());
            register_module_object_reader(k, module_modification_reader(modification::deserialize));
            (*g_persistent_exts)[k] = *this;
        }
        cnstr_set_scalar(this->raw(), 0, environment::register_extension(std::make_shared<data>(empty_state)));
        get_exts().push_back(*this);
    }

    data const & get(environment const & env) {
        return static_cast<data const &>(env.get_extension(get_ext_id()));
    }
    environment update(environment const & env, data const & ext) {
        return env.update(get_ext_id(), std::make_shared<data>(ext));
    }
    environment push_fn(environment const & env, io_state const &, scope_kind) {
        return update(env, get(env).push());
    }
    environment pop_fn(environment const & env, io_state const &, scope_kind) {
        return update(env, get(env).pop());
    }

    environment register_entry(environment const & env, io_state const & ios, entry const & e) {
        object_ref lenv(to_lean_environment(env));
        return update(env, _register_entry(get(env), lenv, ios, e));
    }

    environment add_entry(environment env, io_state const & ios, entry const & e, persistence persist) {
        object_ref lenv(to_lean_environment(env));
        if (persist == persistence::scope) {
            return update(env, _add_tmp_entry(get(env), lenv, ios, e));
        } else {
            if (persist == persistence::global) {
                if (cnstr_tag(get_key().raw()) == 0) // key = None
                    throw exception("EnvironmentExtension.addEntry: cannot add persisted entry to this extension.");
                env = module::add(env, std::make_shared<modification>(string_to_std(cnstr_get(get_key().raw(), 0)), e));
            }
            return update(env, _register_entry(get(env), lenv, ios, e));
        }
    }

    environment add_entry(environment const & env, io_state const & ios, entry const & e, bool persistent) {
        return add_entry(env, ios, e, persistent ? persistence::global : persistence::scope);
    }

    state const & get_state(environment const & env) {
        return get(env).m_state;
    }

    static void initialize() {
        g_exts = new std::vector<object_ref>();
        g_persistent_exts = new std::unordered_map<std::string, object_ref>();
    }

    static void finalize() {
        delete g_persistent_exts;
        delete g_exts;
    }
};

extern "C" obj_res lean_environment_mk_empty(b_obj_arg) {
    return to_lean_environment(environment());
}

extern "C" uint8 lean_environment_contains(b_obj_arg lean_environment, b_obj_arg vm_n) {
    return static_cast<uint8>(static_cast<bool>(to_environment(lean_environment).find(name(vm_n, true))));
}

extern "C" obj_res lean_environment_ext_register(obj_arg key, obj_arg empty_state, obj_arg add_entry_fn) {
    return lean_env_ext(object_ref(key), object_ref(empty_state), object_ref(add_entry_fn)).steal();
}

void initialize_lean_environment() {
    g_env_class = register_external_object_class(env_finalizer, env_foreach);
    lean_env_ext::initialize();
}
void finalize_lean_environment() {
    lean_env_ext::initialize();
}
}
