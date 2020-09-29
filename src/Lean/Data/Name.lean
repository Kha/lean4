/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Std.Data.HashSet
import Std.Data.RBMap
import Std.Data.RBTree
namespace Lean

instance stringToName : HasCoe String Name :=
⟨mkNameSimple⟩

namespace Name

@[export lean_name_hash] def hashEx : Name → USize :=
Name.hash

def getPrefix : Name → Name
| anonymous => anonymous
| str p s _ => p
| num p s _ => p

def getRoot : Name → Name
| anonymous             => anonymous
| n@(str anonymous _ _) => n
| n@(num anonymous _ _) => n
| str n _ _             => getRoot n
| num n _ _             => getRoot n

def getString! : Name → String
| str _ s _ => s
| _         => unreachable!

def getNumParts : Name → Nat
| anonymous => 0
| str p _ _ => getNumParts p + 1
| num p _ _ => getNumParts p + 1

def updatePrefix : Name → Name → Name
| anonymous, newP => anonymous
| str p s _, newP => mkNameStr newP s
| num p s _, newP => mkNameNum newP s

def components' : Name → List Name
| anonymous => []
| str n s _ => mkNameStr anonymous s :: components' n
| num n v _ => mkNameNum anonymous v :: components' n

def components (n : Name) : List Name :=
n.components'.reverse

def eqStr : Name → String → Bool
| str anonymous s _, s' => s == s'
| _,                 _  => false

def replacePrefix : Name → Name → Name → Name
| anonymous,     anonymous, newP => newP
| anonymous,     _,         _    => anonymous
| n@(str p s _), queryP,    newP => if n == queryP then newP else mkNameStr (p.replacePrefix queryP newP) s
| n@(num p s _), queryP,    newP => if n == queryP then newP else mkNameNum (p.replacePrefix queryP newP) s

def isPrefixOf : Name → Name → Bool
| p, anonymous      => p == anonymous
| p, n@(num p' _ _) => p == n || isPrefixOf p p'
| p, n@(str p' _ _) => p == n || isPrefixOf p p'


def isSuffixOf : Name → Name → Bool
| anonymous,   _           => true
| str p₁ s₁ _, str p₂ s₂ _ => s₁ == s₂ && isSuffixOf p₁ p₂
| num p₁ n₁ _, num p₂ n₂ _ => n₁ == n₂ && isSuffixOf p₁ p₂
| _,           _           => false

def lt : Name → Name → Bool
| anonymous,   anonymous   => false
| anonymous,   _           => true
| num p₁ i₁ _, num p₂ i₂ _ => lt p₁ p₂ || (p₁ == p₂ && i₁ < i₂)
| num _ _ _,   str _ _ _   => true
| str p₁ n₁ _, str p₂ n₂ _ => lt p₁ p₂ || (p₁ == p₂ && n₁ < n₂)
| _,           _           => false

def quickLtAux : Name → Name → Bool
| anonymous, anonymous   => false
| anonymous, _           => true
| num n v _, num n' v' _ => v < v' || (v = v' && n.quickLtAux n')
| num _ _ _, str _ _ _   => true
| str n s _, str n' s' _ => s < s' || (s = s' && n.quickLtAux n')
| _,         _           => false

def quickLt (n₁ n₂ : Name) : Bool :=
if n₁.hash < n₂.hash then true
else if n₁.hash > n₂.hash then false
else quickLtAux n₁ n₂

/- Alternative HasLt instance. -/
@[inline] protected def hasLtQuick : HasLess Name :=
⟨fun a b => Name.quickLt a b = true⟩

@[inline] instance : DecidableRel (@HasLess.Less Name Name.hasLtQuick) :=
inferInstanceAs (DecidableRel (fun a b => Name.quickLt a b = true))

def appendAfter : Name → String → Name
| str p s _, suffix => mkNameStr p (s ++ suffix)
| n,         suffix => mkNameStr n suffix

def appendIndexAfter : Name → Nat → Name
| str p s _, idx => mkNameStr p (s ++ "_" ++ toString idx)
| n,         idx => mkNameStr n ("_" ++ toString idx)

def appendBefore : Name → String → Name
| anonymous, pre => mkNameStr anonymous pre
| str p s _, pre => mkNameStr p (pre ++ s)
| num p n _, pre => mkNameNum (mkNameStr p pre) n

/- The frontend does not allow user declarations to start with `_` in any of its parts.
   We use name parts starting with `_` internally to create auxiliary names (e.g., `_private`). -/
def isInternal : Name → Bool
| str p s _ => s.get 0 == '_' || isInternal p
| num p _ _ => isInternal p
| _         => false

def isAtomic : Name → Bool
| anonymous         => true
| str anonymous _ _ => true
| num anonymous _ _ => true
| _                 => false

def isAnonymous : Name → Bool
| anonymous         => true
| _                 => false

def isStr : Name → Bool
| str _ _ _ => true
| _         => false

def isNum : Name → Bool
| num _ _ _ => true
| _         => false

end Name

open Std (RBMap RBTree mkRBMap mkRBTree)

def NameMap (α : Type) := Std.RBMap Name α Name.quickLt

@[inline] def mkNameMap (α : Type) : NameMap α := Std.mkRBMap Name α Name.quickLt

namespace NameMap
variable {α : Type}

instance (α : Type) : HasEmptyc (NameMap α) := ⟨mkNameMap α⟩

instance (α : Type) : Inhabited (NameMap α) := ⟨{}⟩

def insert (m : NameMap α) (n : Name) (a : α) := Std.RBMap.insert m n a

def contains (m : NameMap α) (n : Name) : Bool := Std.RBMap.contains m n

@[inline] def find? (m : NameMap α) (n : Name) : Option α := Std.RBMap.find? m n

end NameMap

def NameSet := RBTree Name Name.quickLt

namespace NameSet
def empty : NameSet := mkRBTree Name Name.quickLt
instance : HasEmptyc NameSet := ⟨empty⟩
instance : Inhabited NameSet := ⟨{}⟩
def insert (s : NameSet) (n : Name) : NameSet := Std.RBTree.insert s n
def contains (s : NameSet) (n : Name) : Bool := Std.RBMap.contains s n

end NameSet

def NameHashSet := Std.HashSet Name

namespace NameHashSet
@[inline] def empty : NameHashSet := Std.HashSet.empty
instance : HasEmptyc NameHashSet := ⟨empty⟩
instance : Inhabited NameHashSet := ⟨{}⟩
def insert (s : NameHashSet) (n : Name) := s.insert n
def contains (s : NameHashSet) (n : Name) : Bool := s.contains n
end NameHashSet

end Lean

open Lean

def String.toName (s : String) : Name :=
let ps := s.splitOn ".";
ps.foldl (fun n p => mkNameStr n p.trim) Name.anonymous
