import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! IMPORTED FIRST ATTEMPT; COMPILED IN THIS WORKSTREAM.
For FIXED nonzero gamma, D has coefficient gamma^28 in the 29-column sum.
This proves a useful translation BEFORE conditioning on D's own disclosures.
It does NOT say the full V8 view is masked by D: D is also opened publicly.
-/
set_option autoImplicit false
open scoped BigOperators
namespace AspisV8Privacy
variable {F I : Type*} [Field F]

def compensateD (coefficient left right old : F) : F := old + (left-right)/coefficient

theorem compensation_identity (c left right old : F) (hc : c ≠ 0) :
    right + c * compensateD c left right old = left + c * old := by
  unfold compensateD
  field_simp [hc]
  <;> ring

theorem gamma_coefficient_nonzero (gamma : F) (h : gamma ≠ 0) : gamma^28 ≠ 0 :=
  pow_ne_zero 28 h

/-- A correction respecting the same inactive zero-sum condition. -/
theorem compensation_sum_preserved (s : Finset I) (c : F) (left right old : I → F)
    (sameSum : (∑ i ∈ s, left i) = ∑ i ∈ s, right i) :
    (∑ i ∈ s, compensateD c (left i) (right i) (old i)) = ∑ i ∈ s, old i := by
  simp only [compensateD, Finset.sum_add_distrib]
  have hz : (∑ i ∈ s, (left i - right i) / c) = 0 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, sameSum, sub_self, zero_div]
  rw [hz, add_zero]

#print axioms compensation_identity
#print axioms gamma_coefficient_nonzero
#print axioms compensation_sum_preserved
end AspisV8Privacy
