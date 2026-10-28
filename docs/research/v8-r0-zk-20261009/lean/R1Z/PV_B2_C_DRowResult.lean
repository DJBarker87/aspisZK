import R1Z.PV_B2_C_DRowRange
import R1Z.PV_B2_C_ErrorRepair
set_option autoImplicit false
namespace PV_B2_C_DRowResult
open Aeneas Aeneas.Std Result PV_B2_253c1
/-- Exhaustive Result behavior of the repaired D row lookup on every Usize. -/
theorem complete (j : Usize) :
    (∃ r, host_weights.host_row .D j = ok r ∧ r.val < 1024) ∨
      host_weights.host_row .D j = fail .arrayOutOfBounds := by
  by_cases hj : j.val < (1024#usize).val
  · exact Or.inl (PV_B2_C_DRowRange.source j hj)
  · exact Or.inr (PV_B2_C_ErrorRepair.copied_row_failure j (Nat.le_of_not_gt hj))

theorem failure_iff (j : Usize) :
    host_weights.host_row .D j = fail .arrayOutOfBounds ↔
      (1024#usize).val ≤ j.val := by
  constructor
  · intro he
    by_contra hn
    obtain ⟨r,hr,_⟩ := PV_B2_C_DRowRange.source j (Nat.lt_of_not_ge hn)
    rw [hr] at he
    cases he
  · exact PV_B2_C_ErrorRepair.copied_row_failure j

/-- Equality with any frozen table read in every invalid-index continuation,
including the error variant, generalizing the retained j=1024 counterexample. -/
theorem invalid_continuation {α : Type} (j : Usize)
    (hj : (1024#usize).val ≤ j.val) (table : Array U16 1024#usize)
    (copied : Usize → Result α) (frozen : U16 → Result α) :
    (host_weights.host_row .D j >>= copied) =
      (Array.index_usize table j >>= frozen) := by
  rw [PV_B2_C_ErrorRepair.copied_row_failure j hj,
    PV_B2_C_ErrorRepair.index_failure table j hj,bind_tc_fail,bind_tc_fail]
#print axioms complete
#print axioms failure_iff
#print axioms invalid_continuation
end PV_B2_C_DRowResult
