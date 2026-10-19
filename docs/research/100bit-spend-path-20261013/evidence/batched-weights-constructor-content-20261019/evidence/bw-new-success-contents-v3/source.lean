import BatchedWeightsNewSuccessDecomposeV3
import BatchedWeightsFilledLengthGenericV5
import BatchedWeightsNewLoopContentsV9
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow WP
open AspisR1BatchedWeightsExtraction
namespace BatchedWeightsNewSuccessContentsV1
abbrev Row := Array Std.U64 4#usize
theorem new_success_contents (weights : Slice aspis_core.field.QM31)
    (state : batched_weights.BatchedWeights)
    (h : batched_weights.BatchedWeights.new weights = .ok (.Ok state)) :
    state.terms = 0#usize ∧ state.raw.length = (Slice.len weights).val ∧
    ∀ i : Usize, i.val < (Slice.len weights).val →
      Slice.index_usize (state.raw : Slice Row) i =
        (do let w ← Slice.index_usize weights i; ok (BatchedWeightsNewLoopContentsV3.rowOf w)) := by
  obtain ⟨rawInit, rawOut, hfilled, hloop, hstate⟩ :=
    BatchedWeightsNewSuccessDecomposeV3.new_success_decompose weights state h
  have hinit := BatchedWeightsFilledLengthGenericV5.filled_success_length
    (Array.Insts.CoreMarkerCopy 4#usize core.marker.CopyU64)
    (Slice.len weights) (Array.repeat 4#usize 0#u64) rawInit hfilled
  have hloopContents := BatchedWeightsNewLoopContentsV3.loop_success_contents_fuel
    weights { start := 0#usize, «end» := Slice.len weights } rawInit 0#usize
    (Slice.len weights).val (by simp) (by simp) (by simpa using hinit)
    (by intro i hi hlt; simp at hlt)
    rawOut hloop
  rw [hstate]
  refine ⟨rfl, ?_, ?_⟩
  · exact hloopContents.1.trans hinit
  · intro i hi
    exact hloopContents.2 i (by simp) hi
#print axioms new_success_contents
end BatchedWeightsNewSuccessContentsV1
