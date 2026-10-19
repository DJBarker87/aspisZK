import BatchedWeightsNewSuccessContentsV3
import BatchedWeightsInitialRowBoundsV2
import SliceReadInBoundsV2
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsNewSuccessContentsBoundsV2
abbrev Row := Array Std.U64 4#usize
theorem new_success_contents_bounds (weights : Slice aspis_core.field.QM31)
    (state : batched_weights.BatchedWeights)
    (h : batched_weights.BatchedWeights.new weights = .ok (.Ok state)) :
    state.terms = 0#usize ∧ state.raw.length = (Slice.len weights).val ∧
    ∀ i : Usize, i.val < (Slice.len weights).val →
      ∃ w, Slice.index_usize weights i = .ok w ∧
      Slice.index_usize (state.raw : Slice Row) i = .ok (BatchedWeightsNewLoopContentsV3.rowOf w) ∧
      (BatchedWeightsNewLoopContentsV3.rowOf w).val[0].val < 2^32 ∧
      (BatchedWeightsNewLoopContentsV3.rowOf w).val[1].val < 2^32 ∧
      (BatchedWeightsNewLoopContentsV3.rowOf w).val[2].val < 2^32 ∧
      (BatchedWeightsNewLoopContentsV3.rowOf w).val[3].val < 2^32 := by
  obtain ⟨hterms, hlen, hcontents⟩ :=
    BatchedWeightsNewSuccessContentsV1.new_success_contents weights state h
  refine ⟨hterms, hlen, ?_⟩
  intro i hi
  obtain ⟨w, hw⟩ := SliceReadInBoundsV1.read_success weights i hi
  have hread := hcontents i hi
  rw [hw] at hread
  have hb := BatchedWeightsInitialRowBoundsV1.rowOf_coordinate_bounds w
  exact ⟨w, hw, hread, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩
#print axioms new_success_contents_bounds
end BatchedWeightsNewSuccessContentsBoundsV2
