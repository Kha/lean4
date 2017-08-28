/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

Attribute that can automatically derive typeclass instances.
-/
prelude
import init.meta.attribute
import init.meta.interactive_base
import init.meta.has_reflect

open lean
open interactive.types

@[user_attribute] meta def derive_attribute : user_attribute :=
{ name := `derive, descr := "Attribute that can automatically derive typeclass instances." }

#print instances has_reflect

meta instance : user_attribute.parameterized derive_attribute :=
⟨_, pexpr_list_or_texpr⟩
