/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include "runtime/sstream.h"
#include "kernel/local_ctx.h"
#include "kernel/abstract.h"

namespace lean {
static expr *       g_dummy_type;
static local_decl * g_dummy_decl;

static expr mk_local_ref(name const & n, name const & un, binder_info bi) {
    return mk_local(n, un, *g_dummy_type, bi); // TODO(Leo): fix after we remove legacy code
}

bool is_local_decl_ref(expr const & e) { // TODO(Leo): delete
    return is_local(e) && local_type(e) == *g_dummy_type;
}

local_decl::local_decl():object_ref(*g_dummy_decl) {}

local_decl::local_decl(unsigned idx, name const & n, name const & un, expr const & t, expr const & v):
    object_ref(mk_cnstr(0, n, un, t, v, sizeof(unsigned) + sizeof(unsigned char))) {
    cnstr_set_scalar<unsigned>(raw(), sizeof(object*)*4, idx);
    cnstr_set_scalar<unsigned char>(raw(), sizeof(object*)*4+sizeof(unsigned), 0);
}

local_decl::local_decl(unsigned idx, name const & n, name const & un, expr const & t, binder_info bi):
    object_ref(mk_cnstr(0, n, un, t, object_ref(box(0)), sizeof(unsigned) + sizeof(unsigned char))) {
    cnstr_set_scalar<unsigned>(raw(), sizeof(object*)*4, idx);
    cnstr_set_scalar<unsigned char>(raw(), sizeof(object*)*4+sizeof(unsigned), static_cast<unsigned char>(bi));
}

local_decl::local_decl(local_decl const & d, expr const & t, expr const & v):
    local_decl(d.get_idx(), d.get_name(), d.get_user_name(), t, v) {}

local_decl::local_decl(local_decl const & d, expr const & t):
    local_decl(d.get_idx(), d.get_name(), d.get_user_name(), t, d.get_info()) {}

expr local_decl::mk_ref() const {
    // TODO(Leo):
    return mk_local_ref(get_name(), get_user_name(), get_info());
}

local_decl local_ctx::mk_local_decl(name const & n, name const & un, expr const & type, expr const & value) {
    lean_assert(!m_name2local_decl.contains(n));
    unsigned idx = m_next_idx;
    m_next_idx++;
    local_decl d(idx, n, un, type, value);
    m_name2local_decl.insert(n, d);
    return d;
}

local_decl local_ctx::mk_local_decl(name const & n, name const & un, expr const & type, binder_info bi) {
    lean_assert(!m_name2local_decl.contains(n));
    unsigned idx = m_next_idx;
    m_next_idx++;
    local_decl d(idx, n, un, type, bi);
    m_name2local_decl.insert(n, d);
    return d;
}

optional<local_decl> local_ctx::find_local_decl(name const & n) const {
    if (auto r = m_name2local_decl.find(n))
        return optional<local_decl>(*r);
    else
        return optional<local_decl>();
}

optional<local_decl> local_ctx::find_local_decl(expr const & e) const {
    return find_local_decl(local_name(e));
}

local_decl const & local_ctx::get_local_decl(name const & n) const {
    if (local_decl const * r = m_name2local_decl.find(n))
        return *r;
    else
        throw exception(sstream() << "unknown free variable: " << n);
}

expr local_ctx::get_local(name const & n) const {
    lean_assert(find_local_decl(n));
    return get_local_decl(n).mk_ref();
}

void local_ctx::clear(local_decl const & d) {
    lean_assert(find_local_decl(d.get_name()));
    m_name2local_decl.erase(d.get_name());
}

template<bool is_lambda>
expr local_ctx::mk_binding(unsigned num, expr const * fvars, expr const & b) const {
    expr r     = abstract(b, num, fvars);
    unsigned i = num;
    while (i > 0) {
        --i;
        local_decl const & decl = get_local_decl(fvar_name(fvars[i]));
        expr type = abstract(decl.get_type(), i, fvars);
        if (optional<expr> const & val = decl.get_value()) {
            r = ::lean::mk_let(decl.get_user_name(), type, abstract(*val, i, fvars), r);
        } else if (is_lambda) {
            r = ::lean::mk_lambda(decl.get_user_name(), type, r, decl.get_info());
        } else {
            r = ::lean::mk_pi(decl.get_user_name(), type, r, decl.get_info());
        }
    }
    return r;
}

expr local_ctx::mk_lambda(unsigned num, expr const * fvars, expr const & e) const {
    return mk_binding<true>(num, fvars, e);
}

expr local_ctx::mk_pi(unsigned num, expr const * fvars, expr const & e) const {
    return mk_binding<false>(num, fvars, e);
}

void initialize_local_ctx() {
    g_dummy_type   = new expr(mk_constant(name::mk_internal_unique_name()));
    g_dummy_decl   = new local_decl(std::numeric_limits<unsigned>::max(),
                                    name("__local_decl_for_default_constructor"), name("__local_decl_for_default_constructor"),
                                    mk_Prop(), mk_binder_info());
}

void finalize_local_ctx() {
    delete g_dummy_decl;
    delete g_dummy_type;
}
}
