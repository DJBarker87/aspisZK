import PCF_CountSliceRef.Funs
import PCF_CountWord
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_CountSlice
/-- Generic payload T is never inspected. Exact slice-length projection, no count bound. -/
theorem projection {T : Type} (accounts : Slice T) (expected : Usize) :
    PCF_CountSliceRef.count_reference accounts expected =
      PCF_AccountRef.count_reference (Slice.len accounts) expected := by rfl

theorem complete {T : Type} (accounts : Slice T) (expected : Usize) :
    PCF_CountSliceRef.count_reference accounts expected =
      ok (PCF_CountWord.tag (PCF_Count.source accounts.length expected.val)) := by
  rw [projection,PCF_CountWord.result]
  rfl

#print axioms projection
#print axioms complete
end PCF_CountSlice
