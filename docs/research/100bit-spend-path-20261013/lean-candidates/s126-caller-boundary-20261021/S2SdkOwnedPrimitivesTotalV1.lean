import S2SdkOwnedModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
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

/-- TOTAL identity of the exact Vec byte-clone used at all three owned SDK
snapshot sites. This uses the library clone induction, not a concrete buffer
normalization or a supplied snapshot equality. -/
theorem bytes_clone_total (bytes : alloc.vec.Vec U8) :
    alloc.vec.CloneVec.clone core.clone.CloneU8 bytes=ok bytes := by
  change Slice.clone core.clone.CloneU8.clone bytes=ok bytes
  obtain ⟨copy,hcopy,hidentity⟩ := spec_imp_exists
    (Slice.clone_spec (clone:=core.clone.CloneU8.clone) (s:=bytes) (by intros; rfl))
  subst copy
  exact hcopy

#print axioms bytes_clone_total

#print alloc.vec.CloneVec.clone
#print core.num.checked_add_IScalar
#print Isize.checked_add
#print axioms shared_allowed_exact
#print axioms shared_allowed_true
end AspisS2OwnedStage1.SdkReference.PrimitivesTotal
