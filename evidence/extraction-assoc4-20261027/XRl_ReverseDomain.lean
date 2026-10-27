import XRl_AdapterCounterexample
open Aeneas Aeneas.Std Result
namespace XRl_Adapter
/-- Cursor-respecting mutable next_back, including explicit borrow restoration.
The shared iterator checks the unconsumed span before removing its last item. -/
def originalNextBack {T : Type} (s : core.slice.iter.IterMut T) := do
  let (v,r) ← core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back
    (⟨s.slice,s.i⟩ : core.slice.iter.Iter T)
  ok (v,{s with slice:=r.slice},fun (updated : core.slice.iter.IterMut T) (item : Option T) =>
    match item with
    | none => updated
    | some x => if h : (updated.slice.val++[x]).length≤Usize.max then
        {updated with slice:=⟨updated.slice.val++[x],h⟩} else s)

def originalReverseNext {T : Type} (s : core.iter.adapters.rev.Rev (core.slice.iter.IterMut T)) := do
  let (v,i,back) ← originalNextBack s.iter
  ok (v,(⟨i⟩ : core.iter.adapters.rev.Rev (core.slice.iter.IterMut T)),
    fun (r : core.iter.adapters.rev.Rev (core.slice.iter.IterMut T)) => (⟨back r.iter v⟩ : core.iter.adapters.rev.Rev (core.slice.iter.IterMut T)),
    fun (r : core.iter.adapters.rev.Rev (core.slice.iter.IterMut T)) (item : Option T) => (⟨back r.iter item⟩ : core.iter.adapters.rev.Rev (core.slice.iter.IterMut T)))

/-- Restricted replacement only. The universal version is refuted by L049.
This proves full modeled Result/iterator/backward state equality at cursor 0. -/
theorem reverseNext_at_zero {T : Type}
    (d : core.iter.traits.double_ended.DoubleEndedIterator (core.slice.iter.IterMut T) T)
    (s : core.iter.adapters.rev.Rev (core.slice.iter.IterMut T)) (fresh : s.iter.i=0) :
    XRk_reverseNext d s=originalReverseNext s := by
  unfold XRk_reverseNext originalReverseNext originalNextBack
    core.slice.iter.IterMut.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorMutT.next_back
  rw [fresh]
  rfl

/-- Actual fresh iter_mut construction supplies the restriction; transporting
it through the generated caller's whole reverse loop is a separate obligation. -/
theorem fresh_cursor {T : Type} (slice : Slice T)
    (it : core.slice.iter.IterMut T) (back : core.slice.iter.IterMut T → Slice T)
    (run : core.slice.Slice.iter_mut slice=ok (it,back)) : it.i=0 := by
  have same := congrArg Prod.fst (Result.ok.inj run)
  have index := congrArg core.slice.iter.IterMut.i same
  exact index.symm
#print axioms reverseNext_at_zero
#print axioms fresh_cursor
end XRl_Adapter
