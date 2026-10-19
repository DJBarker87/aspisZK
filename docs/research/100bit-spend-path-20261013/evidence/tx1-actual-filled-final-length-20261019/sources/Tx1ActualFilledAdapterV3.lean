import ExtractedTx1Reachability
import HeapFilledActualLengthV3
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace Tx1ActualFilledAdapterV3

/-- Aeneas extraction of the actual asp is_core::r0::heap::filled source body,
instantiated at the accepted Tx1 QM31 carrier and shared Error type. -/
noncomputable def withActualHeapFilled
    (B : AspisR1PublicPreparation.Tx1Model.Boundaries) :
    AspisR1PublicPreparation.Tx1Model.Boundaries :=
  { B with filled := AspisR1HeapFilled.aspis_core.r0.heap.filled }

theorem newAccumulator_success_length
    (B : AspisR1PublicPreparation.Tx1Model.Boundaries)
    (v : AspisR1PublicPreparation.transport.Variant)
    (out : AspisR1PublicPreparation.verifier.Accumulator)
    (h : AspisR1PublicPreparation.Tx1Model.newAccumulator
      (withActualHeapFilled B) v = .ok (.Ok out)) :
    ∃ n, AspisR1PublicPreparation.Tx1Model.final_len v = .ok n ∧
      out.weights.length = n.val := by
  obtain ⟨n, weights, hn, hf, hout⟩ :=
    AspisR1PublicPreparation.Tx1Reachability.accumulator_success
      (withActualHeapFilled B) v out h
  refine ⟨n, hn, ?_⟩
  rw [hout]
  exact HeapFilledActualLengthV3.filled_success_length _ _ _ _ hf

#print axioms newAccumulator_success_length
end Tx1ActualFilledAdapterV3
