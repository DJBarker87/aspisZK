import Aeneas
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace Aeneas.Std
/-- P6 model of `core::array::iter::IntoIter<T, N>` and its forward cursor. See pinned Rust source `library/core/src/array/iter.rs` lines 41–75. -/
@[rust_type "core::array::iter::IntoIter"]
structure core.array.iter.IntoIter (T : Type) (N : Usize) where
  data : List T
  cursor : Nat
/-- P6 model of `core::slice::iter::ChunksExactMut<'a, T>`. The source retains the full mutable slice, exact chunk size, and remaining cursor. See pinned Rust source `library/core/src/slice/iter.rs` lines 2011–2032. -/
@[rust_type "core::slice::iter::ChunksExactMut" (mutRegions := #[0])]
structure core.slice.iter.ChunksExactMut (T : Type) where
  source : Slice T
  chunkSize : Usize
  cursor : Nat
  lastStart : Usize
  hasLast : Bool
/-- P6 model of `slice::chunks_exact_mut`: create a forward iterator over full chunks and a final-state projection. The S5 call uses nonzero chunk size 4 on exactly 32 bytes. See pinned `library/core/src/slice/mod.rs` lines 1291–1294. -/
@[rust_fun "core::slice::{[@T]}::chunks_exact_mut"]
def core.slice.Slice.chunks_exact_mut {T : Type} (s : Slice T) (n : Usize) :
    Result (core.slice.iter.ChunksExactMut T × (core.slice.iter.ChunksExactMut T → Slice T)) := do
  if n.val = 0 then fail .panic else
  ok (⟨s,n,0,0#usize,false⟩, fun it => it.source)
/-- P6 model of owned-array `IntoIterator::into_iter`, preserving element order. See pinned Rust source `library/core/src/array/iter.rs` lines 41–75. -/
@[rust_fun "core::array::iter::{core::iter::traits::collect::IntoIterator<[@T; @N], @T, core::array::iter::IntoIter<@T, @N>>}::into_iter"]
def Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter
    {T : Type} {N : Usize} (a : Array T N) : Result (core.array.iter.IntoIter T N) :=
  ok ⟨a.val,0⟩
/-- P6 model of the owned-array iterator's `next`, returning and consuming one element in order. See pinned Rust source `library/core/src/array/iter.rs` lines 238–245. -/
@[rust_fun "core::array::iter::{core::iter::traits::iterator::Iterator<core::array::iter::IntoIter<@T, @N>, @T>}::next"]
def core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
    {T : Type} {N : Usize} (it : core.array.iter.IntoIter T N) :
    Result ((Option T) × core.array.iter.IntoIter T N) :=
  if h : it.cursor < it.data.length then
    ok (some (it.data[it.cursor]), {it with cursor := it.cursor+1})
  else ok (none,it)
/-- P6 model of mutable `ChunksExactMut::next`. The continuation writes a returned replacement chunk into the updated iterator state, preserving disjoint chunk writeback. See pinned Rust source `library/core/src/slice/iter.rs` lines 2045–2055. -/
@[rust_fun "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::ChunksExactMut<'a, @T>, &'a mut [@T]>}::next"]
def core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next
    {T : Type} (it : core.slice.iter.ChunksExactMut T) :
    Result ((Option (Slice T)) × (core.slice.iter.ChunksExactMut T) ×
      (core.slice.iter.ChunksExactMut T → Option (Slice T) → core.slice.iter.ChunksExactMut T)) :=
  if h : it.cursor < it.source.len ∧ 0 < it.chunkSize.val ∧ it.cursor + it.chunkSize.val ≤ it.source.len then
    let chunk : Slice T := ⟨(it.source.val.drop it.cursor).take it.chunkSize.val, by scalar_tac⟩
    let start := it.cursor
    let pos : Usize := Usize.ofNatCore it.cursor (by scalar_tac)
    let it' := {it with cursor := it.cursor + it.chunkSize.val, lastStart := pos, hasLast := true}
    let back := fun (z : core.slice.iter.ChunksExactMut T) (o : Option (Slice T)) =>
      match o with
      | none => z
      | some x =>
        let xs := z.source.val.setSlice! start x.val
        {z with source := ⟨xs, by scalar_tac⟩}
    ok (some chunk,it',back)
  else
    ok (none,it,fun z _ => z)
end Aeneas.Std
#print axioms Aeneas.Std.core.slice.Slice.chunks_exact_mut
#print axioms Aeneas.Std.core.slice.iter.ChunksExactMut.Insts.CoreIterTraitsIteratorIteratorMutASlice.next
#print axioms Aeneas.Std.core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next
#print axioms Aeneas.Std.Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter

namespace P6ToBytes.StdModel
open Aeneas.Std
/-- P6 adaptation for Rust's mutable `Iterator::next` continuation ABI. The
standard Aeneas Iterator carries only `(Option Item, Self)`, while translation
of `&mut [T]` yields an additional writeback continuation. See the pinned
`ChunksExactMut::next` source at `library/core/src/slice/iter.rs:2045-2055`.
This is an extraction-harness library interface, not a claim that ordinary
Rust Iterator has this Lean signature. -/
structure MutableIterator (Self Item : Type) where
  next : Self → Result (Option Item × Self × (Self → Option Item → Self))

/-- Specialized mutable-left `Zip::next`, preserving the left callback while
using ordinary `Iterator::next` on the owned-array right side. It mirrors the
pinned Rust `Zip::next` short-circuit order (`zip.rs:162-166`) and threads the
left chunk replacement back through the zip state. -/
def zipNext {A B ItemA ItemB : Type}
    (IA : MutableIterator A ItemA)
    (IB : core.iter.traits.iterator.Iterator B ItemB)
    (z : core.iter.adapters.zip.Zip A B) :
    Result ((Option (ItemA × ItemB)) × core.iter.adapters.zip.Zip A B ×
      (core.iter.adapters.zip.Zip A B → Option (ItemA × ItemB) → core.iter.adapters.zip.Zip A B)) := do
  let (oa, a', backA) ← IA.next z.fst
  match oa with
  | none => ok (none, ⟨a', z.snd⟩, fun z' _ => ⟨backA z'.fst none, z'.snd⟩)
  | some a => do
    let (ob, b') ← IB.next z.snd
    match ob with
    | none => ok (none, ⟨a', b'⟩, fun z' _ => ⟨backA z'.fst none, z'.snd⟩)
    | some b => ok (some (a,b), ⟨a',b'⟩,
        fun z' o => ⟨backA z'.fst (o.map Prod.fst), z'.snd⟩)

/-- Mutable-left counterpart of `Iterator::zip` for the extraction ABI. -/
def MutableIterator.zip.trait_default
    {A B U ItemA ItemB : Type}
    (_IA : MutableIterator A ItemA)
    (IB : core.iter.traits.collect.IntoIterator U ItemB B)
    (self : A) (other : U) :
    Result (core.iter.adapters.zip.Zip A B ×
      ((core.iter.adapters.zip.Zip A B → core.iter.adapters.zip.Zip A B) → A)) := do
  let b ← IB.into_iter other
  let z : core.iter.adapters.zip.Zip A B := ⟨self,b⟩
  ok (z, fun back => (back z).fst)
end P6ToBytes.StdModel
#print axioms P6ToBytes.StdModel.zipNext
#print axioms P6ToBytes.StdModel.MutableIterator.zip.trait_default
