import BatchedWeightsNewSuccessContentsBoundsV3
import BWVecSliceReadProbeV5
import BatchedWeightsInitialRowBoundsV4
import BatchedWeightsCallerGlobalRangeBridgeV7
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsNewInitialGlobalBoundV2
open BatchedWeightsCallerGlobalRangeBridgeV1
abbrev BW := BatchedWeightsCallerGlobalRangeBridgeV1.BW
abbrev Row := Array Std.U64 4#usize
theorem new_success_global_raw_phase_bound (weights : Slice aspis_core.field.QM31)
    (state : BW)
    (h : batched_weights.BatchedWeights.new weights = .ok (.Ok state)) :
    GlobalRawPhaseBound state := by
  obtain ⟨hterms, hlen, hcontents⟩ :=
    BatchedWeightsNewSuccessContentsBoundsV2.new_success_contents_bounds weights state h
  intro index hindex k hk
  have hi : index.val < (Slice.len weights).val := by simpa [hlen] using hindex
  obtain ⟨w, hw, hread, hb0, hb1, hb2, hb3⟩ := hcontents index hi
  have hrow := BWVecSliceReadProbeV3.probe state.raw index hindex (BatchedWeightsNewLoopContentsV3.rowOf w) hread
  dsimp [AspisR1BatchedWeightsPushLoopGlobalFrameV1.cellAt,
    AspisR1BatchedWeightsPushLoopGlobalFrameV1.rowAt]
  simp only [hrow]
  have hkbound := BatchedWeightsInitialRowBoundsV3.rowOf_any_coordinate_bound w k hk
  rw [hterms]
  change (BatchedWeightsNewLoopContentsV3.rowOf w).val[k.val].val < 2^34 + 0 * AspisR1BatchedAllPrefix.cap
  exact Nat.lt_of_lt_of_le hkbound (by omega)
#print axioms new_success_global_raw_phase_bound
end BatchedWeightsNewInitialGlobalBoundV2
