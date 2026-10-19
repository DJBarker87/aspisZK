import BatchedWeightsNewSuccessContentsV3
import BatchedWeightsCastBoundV1
set_option autoImplicit false
open Aeneas Aeneas.Std
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsInitialRowBoundsV1
open BatchedWeightsNewLoopContentsV3
theorem rowOf_coordinate_bounds (w : aspis_core.field.QM31) :
    (rowOf w).val[0].val < 2^32 ∧ (rowOf w).val[1].val < 2^32 ∧
    (rowOf w).val[2].val < 2^32 ∧ (rowOf w).val[3].val < 2^32 := by
  simp only [rowOf, Array.make]
  exact ⟨BatchedWeightsCastBoundV1.u32_to_u64_bound w.c0.a,
    BatchedWeightsCastBoundV1.u32_to_u64_bound w.c0.b,
    BatchedWeightsCastBoundV1.u32_to_u64_bound w.c1.a,
    BatchedWeightsCastBoundV1.u32_to_u64_bound w.c1.b⟩
#print axioms rowOf_coordinate_bounds
end BatchedWeightsInitialRowBoundsV1
