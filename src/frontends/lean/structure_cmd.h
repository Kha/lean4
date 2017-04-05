/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/cmd_table.h"
namespace lean {
environment structure_cmd_ex(parser & p, decl_attributes const & attrs, decl_modifiers const & modifiers);
environment class_cmd_ex(parser & p, decl_modifiers const & modifiers);
void get_structure_fields(environment const & env, name const & S, buffer<name> & fields);
void register_structure_cmd(cmd_table & r);
environment private_structure_cmd(parser & p);
/** \brief Return true iff \c S is a structure created with the structure command */
bool is_structure(environment const & env, name const & S);
optional<name> is_parent_field(environment const & env, name const & structure_name, name const & field_name);
buffer<name> get_parent_structures(environment const & env, name const & structure_name);
name_set get_ancestor_structures(environment const & env, name const & structure_name);

/* Default value support */
optional<name> has_default_value(environment const & env, name const & field_name, name const & structure_name);
expr mk_field_default_value(environment const & env, name const & full_field_name, std::function<optional<expr>(name const &)> const & get_field_value);

expr unfold_to_projections(const environment & env, name_set const & S_names,
                           std::function<expr(expr const & proj_app)> const & replace, const expr & e);
}
