import FJf_PointIndices
set_option autoImplicit false
namespace AspisR1.FJf_Coordinates
open Aeneas Aeneas.Std Result
/-- Small bounded index arithmetic, never a finite field evaluation. -/
theorem indices (t : Usize) (ht : t.val≤4) :
    (Usize.wrapping_sub 9#usize (Usize.wrapping_mul 2#usize t)).val=9-2*t.val ∧
    (Usize.wrapping_sub 8#usize (Usize.wrapping_mul 2#usize t)).val=8-2*t.val := by
  interval_cases h : t.val <;> scalar_tac
#print axioms indices
end AspisR1.FJf_Coordinates
