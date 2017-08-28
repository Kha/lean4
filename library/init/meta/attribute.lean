/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import init.meta.tactic init.meta.rb_map init.meta.has_reflect init.meta.lean.parser

meta constant attribute.get_instances : name → tactic (list name)
meta constant attribute.fingerprint : name → tactic nat

meta structure user_attribute :=
(name         : name)
(descr        : string)

/- Registers a new user-defined attribute. The argument must be the name of a definition of type
   `user_attribute` or a sub-structure. -/
meta def attribute.register (decl : name) : command :=
tactic.set_basic_attribute ``user_attribute decl tt

/-- Handler that will be called after the attribute has been applied to a declaration.
   Failing the tactic will fail the entire `attribute/def/...` command, i.e. the attribute will
   not be applied after all.
   Declaring an `after_set` handler without a `before_unset` handler will make the attribute
   non-removable. -/
meta def user_attribute.after_set (attr : user_attribute) :=
Π (decl : name) (prio : nat) (persistent : bool), command

/-- Handler that will be called before the attribute is removed from a declaration. -/
meta def user_attribute.before_unset (attr : user_attribute) :=
Π (decl : name) (persistent : bool), command

meta class user_attribute.caching (attr: user_attribute) :=
(cache_ty     : Type)
(mk_cache     : list name → tactic cache_ty)
(dependencies : list name)

meta constant user_attribute.get_cache (attr : user_attribute) [c : attr.caching] : tactic c.cache_ty

meta class user_attribute.parameterized (attr : user_attribute) :=
{param_ty : Type}
[reflect : has_reflect param_ty]
(parser : lean.parser param_ty)

meta def user_attribute.parse_reflect (attr : user_attribute) [attr.parameterized] : lean.parser expr :=
(λ a, user_attribute.parameterized.reflect attr a) <$> user_attribute.parameterized.parser attr

meta constant user_attribute.get_param (attr : user_attribute) [p : attr.parameterized]
  : name → tactic p.param_ty

open tactic

meta def register_attribute := attribute.register

meta def mk_attribute_dyn (attr_name : name) (descr : string) (caching : option expr := none)
                          (after_set : option expr := none) (before_unset : option expr := none) : tactic unit :=
do add_meta_definition attr_name []
                       `(user_attribute)
                       `({user_attribute . name := attr_name, descr := descr}),

   let mk_inst : name → option expr → tactic unit := λ n e, match e with
   | some e :=
   do add_meta_definition (attr_name ++ n) [] ((expr.const (`user_attribute ++ n) [] : expr) (expr.const attr_name [])) e,
      set_basic_attribute `instance (attr_name ++ n) tt
   | none := skip
   end,

   mk_inst `caching caching,
   mk_inst `after_set after_set,
   mk_inst `before_unset before_unset,

   attribute.register attr_name

meta def get_attribute_cache_dyn {α : Type} [reflected α] (name : name) : tactic α :=
let attr : pexpr := expr.const name [] in
to_expr ``(user_attribute.get_cache %%attr) >>= eval_expr α

meta def mk_name_set_attr (name : name) : command :=
mk_attribute_dyn name "name_set attribute" (some
  `({cache_ty := name_set,
     mk_cache := λ ns, return (name_set.of_list ns),
     dependencies := []} : user_attribute.caching %%(expr.const name [])))

meta def get_name_set_for_attr (name : name) : tactic name_set :=
get_attribute_cache_dyn name
