import R1Z.PV_RW_SliceIterator
set_option autoImplicit false
namespace R1Z.PV_RW_IteratorSource
open Aeneas Aeneas.Std Result ControlFlow Error
-- Literal emitted representation from iterator-step-Types.lean.txt.
abbrev aspis_core.field.M31 := U32
/-- [pv_rw_step::iterator_step::iterator_step]:
    Source: 'iterator_step.rs', lines 4:0-7:1
    Visibility: public -/
def iterator_step.iterator_step
  (iterator : core.slice.iter.Iter aspis_core.field.M31) :
  Result ((Option aspis_core.field.M31) × (core.slice.iter.Iter
    aspis_core.field.M31))
  := do
  let (o, iterator1) ← core.slice.iter.IteratorSliceIter.next iterator
  match o with
  | none => ok (none, iterator1)
  | some _ => ok (o, iterator1)


theorem exact (iterator : core.slice.iter.Iter U32) :
    iterator_step.iterator_step iterator = core.slice.iter.IteratorSliceIter.next iterator := by
  unfold iterator_step.iterator_step
  cases h : core.slice.iter.IteratorSliceIter.next iterator with
  | fail error => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨head,next⟩
    cases head <;> rfl

theorem next_some (values : Slice U32) (i : Nat) (h : i < values.val.length) :
    iterator_step.iterator_step (⟨values,i⟩ : core.slice.iter.Iter U32) =
      ok (some values.val[i],(⟨values,i+1⟩ : core.slice.iter.Iter U32)) := by
  rw [exact]
  exact PV_RW_SliceIterator.next_some values i h

theorem next_none (values : Slice U32) (i : Nat) (h : values.val.length ≤ i) :
    iterator_step.iterator_step (⟨values,i⟩ : core.slice.iter.Iter U32) =
      ok (Option.none,(⟨values,i⟩ : core.slice.iter.Iter U32)) := by
  rw [exact]
  exact PV_RW_SliceIterator.next_none values i h

theorem start (values : Slice U32) :
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter values =
      ok (⟨values,0⟩ : core.slice.iter.Iter U32) := rfl

theorem full_poststate (values : Slice U32) (i : Nat) (h : i < values.val.length) :
    ∃ next : core.slice.iter.Iter U32,
      iterator_step.iterator_step (⟨values,i⟩ : core.slice.iter.Iter U32)=ok (some values.val[i],next) ∧
      next.slice=values ∧ next.i=i+1 ∧
      values.val.drop i=values.val[i]::PV_RW_SliceIterator.remaining next := by
  exact ⟨⟨values,i+1⟩,next_some values i h,rfl,rfl,PV_RW_SliceIterator.tail values i h⟩
#print axioms exact
#print axioms next_some
#print axioms next_none
#print axioms start
#print axioms full_poststate
end R1Z.PV_RW_IteratorSource
