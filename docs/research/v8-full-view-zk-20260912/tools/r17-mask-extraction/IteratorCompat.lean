import Aeneas.Std
import AspisV8R17.MaskClosureWriteback

/-! Explicit candidate compatibility models for the R17 generated caller.
These definitions retain closure/iterator state. Compilation does not certify
Rust specialization, allocation behavior, or source-to-model correspondence.
Do not import the generated external-axiom template. -/
namespace AspisR17MaskSource.IteratorCompat
open Aeneas Aeneas.Std Result

structure BorrowFnOnce (F A B : Type) where
  call_once : F → A → Result (B × F)

structure BorrowFnMut (F A B : Type) where
  FnOnceInst : BorrowFnOnce F A B
  call_mut : F → A → Result (B × F × (F → F))

def mapDefault {I A F B : Type}
    (_ : core.iter.traits.iterator.Iterator I A) (_ : BorrowFnMut F A B)
    (iter : I) (f : F) :
    Result (core.iter.adapters.map.Map I F × (core.iter.adapters.map.Map I F → F)) :=
  ok (⟨iter, f⟩, fun current => current.f)

def mapNext {I A F B : Type}
    (it : core.iter.traits.iterator.Iterator I A) (fn : BorrowFnMut F A B)
    (self : core.iter.adapters.map.Map I F) :
    Result (Option B × core.iter.adapters.map.Map I F) := do
  let (value, iter) ← it.next self.iter
  match value with
  | none => ok (none, ⟨iter, self.f⟩)
  | some value =>
    let (out, f) ← AspisV8R17.MaskClosureWriteback.finishCall (fn.call_mut self.f value)
    ok (some out, ⟨iter, f⟩)

/-- Keep final iterator state, including captured mutable closure state.
This is a refinement candidate of cached iterToList, not an erased borrow. -/
def collectListState {I B : Type} (it : core.iter.traits.iterator.Iterator I B)
    (iter : I) (acc : List B) : Result (List B × I) := do
  let (value, iter) ← it.next iter
  match value with
  | none => ok (acc.reverse, iter)
  | some value => collectListState it iter (value :: acc)
partial_fixpoint

def collectState {I B : Type} (it : core.iter.traits.iterator.Iterator I B)
    (iter : I) : Result (alloc.vec.Vec B × I) := do
  let (values, finalIter) ← collectListState it iter []
  if h : values.length ≤ Usize.max then ok (⟨values, h⟩, finalIter)
  else fail .panic

/-- Only for the ordinary Iterator dictionary; the mutable zip path below
calls the full next and preserves its write-back. -/
def iterMutNextForward {T : Type} (self : core.slice.iter.IterMut T) :
    Result (Option T × core.slice.iter.IterMut T) := do
  let (value, iter, _) ← core.slice.iter.IteratorIterMut.next self
  ok (value, iter)

def zipMutVec {T U : Type} (a : core.slice.iter.IterMut T) (b : alloc.vec.Vec U) :
    Result (core.iter.adapters.zip.Zip (core.slice.iter.IterMut T)
      (alloc.vec.into_iter.IntoIter U) ×
      (core.iter.adapters.zip.Zip (core.slice.iter.IterMut T)
        (alloc.vec.into_iter.IntoIter U) → core.slice.iter.IterMut T)) :=
  ok (⟨a, b⟩, fun current => current.fst)

/-- Default zip advancement, retaining the mutable first component's borrow.
The second iterator advances only when the first yields Some. -/
def zipMutNext {T U : Type}
    (self : core.iter.adapters.zip.Zip (core.slice.iter.IterMut T)
      (alloc.vec.into_iter.IntoIter U)) :
    Result (Option (T × U) ×
      core.iter.adapters.zip.Zip (core.slice.iter.IterMut T) (alloc.vec.into_iter.IntoIter U) ×
      (core.iter.adapters.zip.Zip (core.slice.iter.IterMut T) (alloc.vec.into_iter.IntoIter U) →
        Option (T × U) →
        core.iter.adapters.zip.Zip (core.slice.iter.IterMut T) (alloc.vec.into_iter.IntoIter U))) := do
  let (oa, a, back) ← core.slice.iter.IteratorIterMut.next self.fst
  match oa with
  | none => ok (none, ⟨a, self.snd⟩, fun current _ => current)
  | some x =>
    let (ob, b) ← alloc.vec.into_iter.IteratorIntoIter.next self.snd
    match ob with
    | none => ok (none, ⟨a, b⟩, fun current _ => current)
    | some y => ok (some (x, y), ⟨a, b⟩,
        fun current replacement =>
          { current with fst := back current.fst (replacement.map Prod.fst) })

theorem mapNext_some {I A F B : Type}
    (it : core.iter.traits.iterator.Iterator I A) (fn : BorrowFnMut F A B)
    (self : core.iter.adapters.map.Map I F) (value : A) (iter : I)
    (out : B) (updated : F) (back : F → F)
    (hi : it.next self.iter = ok (some value, iter))
    (hf : fn.call_mut self.f value = ok (out, updated, back)) :
    mapNext it fn self = ok (some out, ⟨iter, back updated⟩) := by
  simp [mapNext, hi, hf, AspisV8R17.MaskClosureWriteback.finishCall]

theorem mapNext_none {I A F B : Type}
    (it : core.iter.traits.iterator.Iterator I A) (fn : BorrowFnMut F A B)
    (self : core.iter.adapters.map.Map I F) (iter : I)
    (hi : it.next self.iter = ok (none, iter)) :
    mapNext it fn self = ok (none, ⟨iter, self.f⟩) := by
  simp [mapNext, hi]

#print axioms mapNext_some
#print axioms mapNext_none
#print axioms collectState
#print axioms zipMutNext
end AspisR17MaskSource.IteratorCompat
