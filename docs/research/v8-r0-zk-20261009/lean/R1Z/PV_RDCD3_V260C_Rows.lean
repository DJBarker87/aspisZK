import R1Z.PV_B2_C_RawWeights251Funs
import R1Z.PV_RDCD3_V260RowResult

namespace R1Z.PV_RDCD3_V260C_Rows
set_option autoImplicit false
open Aeneas Aeneas.Std Result
abbrev V := PV_B2_251c1.transport.Variant

def variant : V → PV_B2_253c1.transport.Variant
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D

/-- The two retained emissions share the complete usize row program. -/
theorem row (v : V) (j : Usize) :
    PV_B2_251c1.host_weights.host_row v j =
      PV_B2_253c1.host_weights.host_row (variant v) j := by
  cases v <;> simp only [variant,
    PV_B2_251c1.host_weights.host_row,
    PV_B2_251c1.host_weights.host_row_loop0,
    PV_B2_251c1.host_weights.host_row_loop1,
    PV_B2_251c1.host_weights.host_row_loop0.body,
    PV_B2_251c1.host_weights.host_row_loop1.body,
    PV_B2_251c1.host_weights.HOST_COEFFICIENT_TO_ROW,
    PV_B2_251c1.transport.TAU,
    PV_B2_253c1.host_weights.host_row,
    PV_B2_253c1.host_weights.host_row_loop0,
    PV_B2_253c1.host_weights.host_row_loop1,
    PV_B2_253c1.host_weights.host_row_loop0.body,
    PV_B2_253c1.host_weights.host_row_loop1.body,
    PV_B2_253c1.host_weights.HOST_COEFFICIENT_TO_ROW,
    PV_B2_253c1.transport.TAU]

theorem invalid_D (j : Usize) (invalid : 1024 ≤ j.val) :
    PV_B2_251c1.host_weights.host_row .D j = fail .arrayOutOfBounds := by
  rw [row]
  exact PV_RDCD3_V260RowResult.invalid_D j invalid

theorem complete (v : V) (j : Usize) :
    (∃ r, PV_B2_251c1.host_weights.host_row v j = ok r ∧ r.val < 1024) ∨
      PV_B2_251c1.host_weights.host_row v j = fail .arrayOutOfBounds := by
  rw [row]
  exact PV_RDCD3_V260RowResult.complete (variant v) j

theorem inactive_indices (r : Usize) (bound : r.val < 1024) :
    r.val/16 < 64 ∧ r.val%16 < 16 := PV_RDCD3_V260RowResult.inactive_indices r bound

#print axioms row
#print axioms invalid_D
#print axioms complete
#print axioms inactive_indices
end R1Z.PV_RDCD3_V260C_Rows
