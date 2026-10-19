import BatchedWeightsNewSuccessContentsV3
import BatchedWeightsCastBoundV1
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsInitialRowBoundsV3
open BatchedWeightsNewLoopContentsV3
theorem rowOf_any_coordinate_bound (w : aspis_core.field.QM31) (k : Usize) (hk : k.val < 4) :
    (rowOf w).val[k.val].val < 2^32 := by
  have hv : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 := by omega
  rcases hv with h0 | h1 | h2 | h3
  · simpa [rowOf, Array.make, h0] using BatchedWeightsCastBoundV1.u32_to_u64_bound w.c0.a
  · simpa [rowOf, Array.make, h1] using BatchedWeightsCastBoundV1.u32_to_u64_bound w.c0.b
  · simpa [rowOf, Array.make, h2] using BatchedWeightsCastBoundV1.u32_to_u64_bound w.c1.a
  · simpa [rowOf, Array.make, h3] using BatchedWeightsCastBoundV1.u32_to_u64_bound w.c1.b
#print axioms rowOf_any_coordinate_bound
end BatchedWeightsInitialRowBoundsV3
