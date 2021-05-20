/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Std.Data.AssocList
namespace Std
universes u v w

def HashMapBucket (α : Type u) (β : Type v) :=
  { b : Array (AssocList α β) // b.size > 0 }

def HashMapBucket.update {α : Type u} {β : Type v} (data : HashMapBucket α β) (i : USize) (d : AssocList α β) (h : i.toNat < data.val.size) : HashMapBucket α β :=
  ⟨ data.val.uset i d h,
    by erw [Array.size_set]; exact data.property ⟩

structure HashMapImp (α : Type u) (β : Type v) where
  size       : Nat
  buckets    : HashMapBucket α β

def mkHashMapImp {α : Type u} {β : Type v} (nbuckets := 8) : HashMapImp α β :=
  let n := if nbuckets = 0 then 8 else nbuckets;
  { size       := 0,
    buckets    :=
    ⟨ mkArray n AssocList.nil,
      by simp; cases nbuckets; decide; apply Nat.zeroLtSucc; done ⟩ }

namespace HashMapImp
variable {α : Type u} {β : Type v}

def mkIdx {n : Nat} (h : n > 0) (u : USize) : { u : USize // u.toNat < n } :=
  ⟨u % n, USize.modn_lt _ h⟩

@[inline] def reinsertAux (hashFn : α → USize) (data : HashMapBucket α β) (a : α) (b : β) : HashMapBucket α β :=
  let ⟨i, h⟩ := mkIdx data.property (hashFn a)
  data.update i (AssocList.cons a b (data.val.uget i h)) h

@[inline] def foldBucketsM {δ : Type w} {m : Type w → Type w} [Monad m] (data : HashMapBucket α β) (d : δ) (f : δ → α → β → m δ) : m δ :=
  data.val.foldlM (init := d) fun d b => b.foldlM f d

@[inline] def foldBuckets {δ : Type w} (data : HashMapBucket α β) (d : δ) (f : δ → α → β → δ) : δ :=
  Id.run $ foldBucketsM data d f

@[inline] def foldM {δ : Type w} {m : Type w → Type w} [Monad m] (f : δ → α → β → m δ) (d : δ) (h : HashMapImp α β) : m δ :=
  foldBucketsM h.buckets d f

@[inline] def fold {δ : Type w} (f : δ → α → β → δ) (d : δ) (m : HashMapImp α β) : δ :=
  foldBuckets m.buckets d f

@[inline] def forBucketsM {m : Type w → Type w} [Monad m] (data : HashMapBucket α β) (f : α → β → m PUnit) : m PUnit :=
  data.val.forM fun b => b.forM f

@[inline] def forM {m : Type w → Type w} [Monad m] (f : α → β → m PUnit) (h : HashMapImp α β) : m PUnit :=
  forBucketsM h.buckets f

def findEntry? [BEq α] [Hashable α] (m : HashMapImp α β) (a : α) : Option (α × β) :=
  match m with
  | ⟨_, buckets⟩ =>
    let ⟨i, h⟩ := mkIdx buckets.property (hash a)
    (buckets.val.uget i h).findEntry? a

def find? [BEq α] [Hashable α] (m : HashMapImp α β) (a : α) : Option β :=
  match m with
  | ⟨_, buckets⟩ =>
    let ⟨i, h⟩ := mkIdx buckets.property (hash a)
    (buckets.val.uget i h).find? a

def contains [BEq α] [Hashable α] (m : HashMapImp α β) (a : α) : Bool :=
  match m with
  | ⟨_, buckets⟩ =>
    let ⟨i, h⟩ := mkIdx buckets.property (hash a)
    (buckets.val.uget i h).contains a

-- TODO: remove `partial` by using well-founded recursion
partial def moveEntries [Hashable α] (i : Nat) (source : Array (AssocList α β)) (target : HashMapBucket α β) : HashMapBucket α β :=
  if h : i < source.size then
     let idx : Fin source.size := ⟨i, h⟩
     let es  : AssocList α β   := source.get idx
     -- We remove `es` from `source` to make sure we can reuse its memory cells when performing es.foldl
     let source                := source.set idx AssocList.nil
     let target                := es.foldl (reinsertAux hash) target
     moveEntries (i+1) source target
  else target

def expand [Hashable α] (size : Nat) (buckets : HashMapBucket α β) : HashMapImp α β :=
  let nbuckets := buckets.val.size * 2
  have : nbuckets > 0 := Nat.mulPos buckets.property (by decide)
  let new_buckets : HashMapBucket α β := ⟨mkArray nbuckets AssocList.nil, by simp; assumption⟩
  { size    := size,
    buckets := moveEntries 0 buckets.val new_buckets }

def insert [BEq α] [Hashable α] (m : HashMapImp α β) (a : α) (b : β) : HashMapImp α β :=
  match m with
  | ⟨size, buckets⟩ =>
    let ⟨i, h⟩ := mkIdx buckets.property (hash a)
    let bkt    := buckets.val.uget i h
    if bkt.contains a then
      ⟨size, buckets.update i (bkt.replace a b) h⟩
    else
      let size'    := size + 1
      let buckets' := buckets.update i (AssocList.cons a b bkt) h
      if size' ≤ buckets.val.size then
        { size := size', buckets := buckets' }
      else
        expand size' buckets'

def erase [BEq α] [Hashable α] (m : HashMapImp α β) (a : α) : HashMapImp α β :=
  match m with
  | ⟨ size, buckets ⟩ =>
    let ⟨i, h⟩ := mkIdx buckets.property (hash a)
    let bkt    := buckets.val.uget i h
    if bkt.contains a then ⟨size - 1, buckets.update i (bkt.erase a) h⟩
    else m

inductive WellFormed [BEq α] [Hashable α] : HashMapImp α β → Prop where
  | mkWff     : ∀ n,                    WellFormed (mkHashMapImp n)
  | insertWff : ∀ m a b, WellFormed m → WellFormed (insert m a b)
  | eraseWff  : ∀ m a,   WellFormed m → WellFormed (erase m a)

end HashMapImp

def HashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] :=
  { m : HashMapImp α β // m.WellFormed }

open Std.HashMapImp

def mkHashMap {α : Type u} {β : Type v} [BEq α] [Hashable α] (nbuckets := 8) : HashMap α β :=
  ⟨ mkHashMapImp nbuckets, WellFormed.mkWff nbuckets ⟩

namespace HashMap
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

instance : Inhabited (HashMap α β) where
  default := mkHashMap

instance : EmptyCollection (HashMap α β) := ⟨mkHashMap⟩

@[inline] def insert (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
  match m with
  | ⟨ m, hw ⟩ => ⟨ m.insert a b, WellFormed.insertWff m a b hw ⟩

@[inline] def erase (m : HashMap α β) (a : α) : HashMap α β :=
  match m with
  | ⟨ m, hw ⟩ => ⟨ m.erase a, WellFormed.eraseWff m a hw ⟩

@[inline] def findEntry? (m : HashMap α β) (a : α) : Option (α × β) :=
  match m with
  | ⟨ m, _ ⟩ => m.findEntry? a

@[inline] def find? (m : HashMap α β) (a : α) : Option β :=
  match m with
  | ⟨ m, _ ⟩ => m.find? a

@[inline] def findD (m : HashMap α β) (a : α) (b₀ : β) : β :=
  (m.find? a).getD b₀

@[inline] def find! [Inhabited β] (m : HashMap α β) (a : α) : β :=
  match m.find? a with
  | some b => b
  | none   => panic! "key is not in the map"

@[inline] def getOp (self : HashMap α β) (idx : α) : Option β :=
  self.find? idx

@[inline] def contains (m : HashMap α β) (a : α) : Bool :=
  match m with
  | ⟨ m, _ ⟩ => m.contains a

@[inline] def foldM {δ : Type w} {m : Type w → Type w} [Monad m] (f : δ → α → β → m δ) (init : δ) (h : HashMap α β) : m δ :=
  match h with
  | ⟨ h, _ ⟩ => h.foldM f init

@[inline] def fold {δ : Type w} (f : δ → α → β → δ) (init : δ) (m : HashMap α β) : δ :=
  match m with
  | ⟨ m, _ ⟩ => m.fold f init

@[inline] def forM {m : Type w → Type w} [Monad m] (f : α → β → m PUnit) (h : HashMap α β) : m PUnit :=
  match h with
  | ⟨ h, _ ⟩ => h.forM f

@[inline] def size (m : HashMap α β) : Nat :=
  match m with
  | ⟨ {size := sz, ..}, _ ⟩ => sz

@[inline] def isEmpty (m : HashMap α β) : Bool :=
  m.size = 0

@[inline] def empty : HashMap α β :=
  mkHashMap

def toList (m : HashMap α β) : List (α × β) :=
  m.fold (init := []) fun r k v => (k, v)::r

def toArray (m : HashMap α β) : Array (α × β) :=
  m.fold (init := #[]) fun r k v => r.push (k, v)

def numBuckets (m : HashMap α β) : Nat :=
  m.val.buckets.val.size

end HashMap
end Std
