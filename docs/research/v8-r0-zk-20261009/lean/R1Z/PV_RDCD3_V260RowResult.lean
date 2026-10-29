import R1Z.PV_RDCD3_V260RowRange
import R1Z.PV_RDCD3_Index194

namespace R1Z.PV_RDCD3_V260RowResult
set_option autoImplicit false
open Aeneas Aeneas.Std Result PV_B2_253c1

theorem invalid_D (j : Usize) (invalid : 1024 ≤ j.val) :
    host_weights.host_row .D j = fail .arrayOutOfBounds := by
  unfold host_weights.host_row
  rw [← PV_RDCD3_Index194.array_complete]
  rw [PV_RDCD3_Index194.failure host_weights.HOST_COEFFICIENT_TO_ROW.val j.val (by
    rw [host_weights.HOST_COEFFICIENT_TO_ROW.property]
    exact invalid),bind_tc_fail]

/-- Every input index is covered, rather than assuming the public row bound.
The D table's invalid-index error is propagated before inactive/point access. -/
theorem complete (variant : transport.Variant) (j : Usize) :
    (∃ r, host_weights.host_row variant j = ok r ∧ r.val < 1024) ∨
      host_weights.host_row variant j = fail .arrayOutOfBounds := by
  by_cases h : j.val < 1024
  · exact Or.inl (PV_RDCD3_V260RowRange.source variant j h)
  · cases variant with
    | S1 => exact Or.inl ⟨_,PV_RDCD3_V260RowSource.S1 j,PV_RDCD3_V260RowRange.perm_bound j⟩
    | S2 => exact Or.inl ⟨_,PV_RDCD3_V260RowSource.S2 j,PV_RDCD3_V260RowRange.perm_bound j⟩
    | D => exact Or.inr (invalid_D j (by omega))

/-- Guarded native inactive uses one of 64 masks and one of 16 bit positions. -/
theorem inactive_indices (r : Usize) (bound : r.val < 1024) :
    r.val/16 < 64 ∧ r.val%16 < 16 := by omega

#print axioms invalid_D
#print axioms complete
#print axioms inactive_indices
end R1Z.PV_RDCD3_V260RowResult
