import GSConcreteRootRecovery
import GSConcreteInterpolation
import GSFixedInputDecoderFamily
import GSWideExactAgreementInputs
import GSRuntimeFinalDistanceEncoderBridge
import GSFinalActualMessageRecovery
import AspisFormal.Pool.AlgorithmicCircleDecoderV7

set_option autoImplicit false

namespace AspisWide.GSActualFinalRuntimeCloseCompleteness

open CompPoly CompPoly.CBivariate CompPoly.GuruswamiSudan
open AspisWideTower AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSWideExactAgreementInputs
open AspisWide.GSRuntimeFinalDistanceEncoderBridge
open AspisWide.GSFinalActualMessageRecovery
open AspisR1.GSConcreteRootRecovery AspisR1.GSConcreteInterpolation
open AspisR1.GSFixedInputDecoderFamily
open AspisR1.RRFinalMessageRecovery
open AspisWide.FinalEncoder

theorem final_call_success_runtime_close_iff
    (received : FinalWord WideExact)
    (points : Array (WideExact × WideExact))
    (hpoints : points = finalNormalizedPoints received)
    (hsize : points.size = 262144)
    (q t : Nat) (hq : q = Fintype.card WideExact)
    (H : FinalTape WideExact t) (candidates : List (List WideExact))
    (hout : final q t points hsize H = some candidates) :
    ∀ m, m ∈ finalRuntimeCloseList received candidates ↔
      closeAtLeast 9558 (exactFinalEncoder (K := WideExact)) received m := by
  obtain ⟨Q, hrun, hc⟩ := final_correct q t points hsize hq H candidates hout
  have hspec := final_spec points hsize Q hrun
  rw [hpoints] at hspec
  have hQ : ValidInterpolationWitness (finalNormalizedPoints received)
      ⟨256, 3, 28673⟩ Q := by
    convert hspec using 1 <;> rfl
  have hc' : AspisWide.GSRootCandidateContract.Candidates
      (CBivariate.toPoly Q) 256 candidates := by
    simpa [AspisR1.GSConcreteRootRecovery.Candidates] using hc
  intro m
  exact final_runtime_close_list_mem_iff received m Q candidates hQ hc'

#print axioms final_call_success_runtime_close_iff

end AspisWide.GSActualFinalRuntimeCloseCompleteness
