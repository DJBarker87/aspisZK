import Tx1ActualFilledAdapterV3
import Tx1FinalLenBoundV8
set_option autoImplicit false
namespace Tx1ActualAccumulatorLengthBoundV1
open Aeneas Aeneas.Std Result

theorem newAccumulator_weights_length_le_256
    (B : AspisR1PublicPreparation.Tx1Model.Boundaries)
    (v : AspisR1PublicPreparation.transport.Variant)
    (out : AspisR1PublicPreparation.verifier.Accumulator)
    (h : AspisR1PublicPreparation.Tx1Model.newAccumulator
      (Tx1ActualFilledAdapterV3.withActualHeapFilled B) v = .ok (.Ok out)) :
    out.weights.length ≤ 256 := by
  obtain ⟨n, hn, hlen⟩ :=
    Tx1ActualFilledAdapterV3.newAccumulator_success_length B v out h
  have hnval : n.val ≤ 256 := by
    cases v <;> simp only [Tx1FinalLenBoundV6.final_len_cases, Result.ok.injEq] at hn <;>
      rw [← hn] <;> norm_num [UScalar.ofNatCore_val_eq]
  rw [hlen]
  exact hnval
#print axioms newAccumulator_weights_length_le_256
end Tx1ActualAccumulatorLengthBoundV1
