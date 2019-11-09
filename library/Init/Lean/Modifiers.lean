/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import private Init.Lean.Environment

namespace Lean

def mkProtectedExtension : IO TagDeclarationExtension :=
mkTagDeclarationExtension `protected

@[init mkProtectedExtension]
constant protectedExt : TagDeclarationExtension := arbitrary _

@[export lean_add_protected]
def addProtected (env : Environment) (n : Name) : Environment :=
protectedExt.tag env n

@[export lean_is_protected]
def isProtected (env : Environment) (n : Name) : Bool :=
protectedExt.isTagged env n

def mkPrivateExtension : IO (EnvExtension Nat) :=
registerEnvExtension (pure 1)

@[init mkPrivateExtension]
constant privateExt : EnvExtension Nat := arbitrary _

/- Private name support.

   Suppose the user marks as declaration `n` as private. Then, we create
   the name: `_private.<module_name>.<index> ++ n`.
   We say `_private.<module_name>.<index>` is the "private prefix"
   where `<index>` comes from the environment extension `privateExt`.

   We assume that `n` is a valid user name and does not contain
   `Name.mkNumeral` constructors. Thus, we can easily convert from
   private internal name to user given name.
-/

def privateHeader : Name := `_private

@[export lean_mk_private_prefix]
def mkPrivatePrefix (env : Environment) : Environment × Name :=
let idx := privateExt.getState env;
let p   := Name.mkNumeral (privateHeader ++ env.mainModule) idx;
let env := privateExt.setState env (idx+1);
(env, p)

@[export lean_mk_private_name]
def mkPrivateName (env : Environment) (n : Name) : Environment × Name :=
let (env, p) := mkPrivatePrefix env;
(env, p ++ n)

def isPrivateName : Name → Bool
| n@(Name.mkString p _) => n == privateHeader || isPrivateName p
| Name.mkNumeral p _    => isPrivateName p
| _                     => false

@[export lean_is_private_name]
def isPrivateNameExport (n : Name) : Bool :=
isPrivateName n

private def privateToUserNameAux : Name → Name
| Name.mkString p s => Name.mkString (privateToUserNameAux p) s
| _                 => Name.anonymous

@[export lean_private_to_user_name]
def privateToUserName (n : Name) : Option Name :=
if isPrivateName n then privateToUserNameAux n
else none

private def privatePrefixAux : Name → Name
| Name.mkString p _ => privatePrefixAux p
| n                 => n

@[export lean_private_prefix]
def privatePrefix (n : Name) : Option Name :=
if isPrivateName n then privatePrefixAux n
else none

end Lean
