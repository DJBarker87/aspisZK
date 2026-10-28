import R1Z.PV_RW_IteratorSource
import R1Z.PV_RW_ResultOutcome
import R1Z.PV_RW_Cursor
set_option autoImplicit false
namespace R1Z.PV_RW_NativeCursor
open Aeneas Aeneas.Std Result

-- Retains every data field of the standard iterator model.
def cursor (iterator : core.slice.iter.Iter U32) : PV_RW_Cursor.Cursor U32 :=
  ⟨iterator.slice.val,iterator.i⟩

theorem remaining (iterator : core.slice.iter.Iter U32) :
    PV_RW_Cursor.remaining (cursor iterator)=PV_RW_SliceIterator.remaining iterator := rfl

theorem next (iterator : core.slice.iter.Iter U32) :
    PV_RW_Outcome.map id (fun pair : Option U32 × core.slice.iter.Iter U32 => (pair.1,cursor pair.2))
      (PV_RW_ResultOutcome.toOutcome (PV_RW_IteratorSource.iterator_step.iterator_step iterator)) =
        .ok (PV_RW_Cursor.next (cursor iterator)) := by
  rcases iterator with ⟨values,i⟩
  by_cases active : i<values.val.length
  · rw [PV_RW_IteratorSource.next_some values i active]
    rw [PV_RW_Cursor.some_step _ active]
    rfl
  · have stopped : values.val.length ≤ i := by omega
    rw [PV_RW_IteratorSource.next_none values i stopped]
    rw [PV_RW_Cursor.none_step _ stopped]
    rfl

theorem injective (left right : core.slice.iter.Iter U32)
    (same : cursor left=cursor right) : left=right := by
  rcases left with ⟨leftValues,leftIndex⟩
  rcases right with ⟨rightValues,rightIndex⟩
  have values : leftValues.val=rightValues.val :=
    congrArg (fun state : PV_RW_Cursor.Cursor U32 => state.values) same
  have indices : leftIndex=rightIndex :=
    congrArg (fun state : PV_RW_Cursor.Cursor U32 => state.index) same
  have slices : leftValues=rightValues := Subtype.ext values
  cases slices
  cases indices
  rfl
#print axioms remaining
#print axioms next
#print axioms injective
end R1Z.PV_RW_NativeCursor
