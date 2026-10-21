import S2SdkOwnedModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.SdkReference.PrimitivesTotal

/-- TOTAL at every signed counter, including both extrema. -/
theorem shared_allowed_exact (counter : Isize) :
    shared_allowed counter=ok (decide (counter≥0#isize ∧ counter<core.num.Isize.MAX)) := by
  by_cases h : counter≥0#isize
  · simp [shared_allowed,h]
  · simp [shared_allowed,h]

theorem shared_allowed_true (counter : Isize) :
    shared_allowed counter=ok true ↔ counter≥0#isize ∧ counter<core.num.Isize.MAX := by
  rw [shared_allowed_exact]
  simp

#print alloc.vec.CloneVec.clone
#print Isize.checked_add
#print axioms shared_allowed_exact
#print axioms shared_allowed_true
end AspisS2OwnedStage1.SdkReference.PrimitivesTotal
