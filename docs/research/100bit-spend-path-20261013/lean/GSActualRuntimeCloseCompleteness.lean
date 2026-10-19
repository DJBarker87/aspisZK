import GSConcreteRootRecovery
import GSConcreteInterpolation
import GSFixedInputDecoderFamily
import GSWideExactAgreementInputs
import GSRuntimeInitialDistanceEncoderBridge
import GSInitialActualMessageRecovery
import AspisFormal.Pool.AlgorithmicCircleDecoderV7
import R1InitialResponses

set_option autoImplicit false

namespace AspisWide.GSActualRuntimeCloseCompleteness

open CompPoly CompPoly.CBivariate CompPoly.GuruswamiSudan
open AspisWideTower
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSWideExactAgreementInputs
open AspisWide.GSRootCandidateContract
open AspisWide.GSRuntimeInitialDistanceEncoderBridge
open AspisWide.GSInitialActualMessageRecovery
open AspisR1.GSConcreteRootRecovery
open AspisR1.GSConcreteInterpolation
open AspisR1.GSFixedInputDecoderFamily
open AspisR1.InitialResponses

/-- A valid interpolation witness and a complete root list make the
runtime close-list exactly the protocol's mathematical Close set. -/
theorem initial_runtime_list_to_Close_of_witness
    (received : InitialWord WideExact) (Q : CBivariate WideExact)
    (candidates : List (List WideExact))
    (hQ : ValidInterpolationWitness (initialNormalizedPoints received)
      ⟨1025, 3, 114689⟩ Q)
    (hc : Candidates (CBivariate.toPoly Q) 1025 candidates) :
    (initialRuntimeCloseList received candidates).toFinset =
      AspisR1.InitialResponses.Close received := by
  classical
  ext m
  rw [List.mem_toFinset]
  have hruntime := initial_runtime_close_list_mem_iff
    received m Q candidates hQ hc
  exact hruntime.trans (AspisR1.InitialResponses.mem_Close received m).symm

/-- Actual initial root recovery is complete when its input points are the
normalized received-word points. The array remains an explicit argument so
runtime encoders can instantiate this theorem without computing a conversion
record. -/
theorem initial_call_success_runtime_list_to_Close
    (received : InitialWord WideExact)
    (points : Array (WideExact × WideExact))
    (hpoints : points = initialNormalizedPoints received)
    (hsize : points.size = 1048576)
    (q t : Nat) (hq : q = Fintype.card WideExact)
    (H : InitialTape WideExact t) (candidates : List (List WideExact))
    (hout : initial q t points hsize H = some candidates) :
    (initialRuntimeCloseList received candidates).toFinset =
      AspisR1.InitialResponses.Close received := by
  obtain ⟨Q, hrun, hc⟩ := initial_correct q t points hsize
    hq H candidates hout
  have hspec := initial_spec points hsize Q hrun
  rw [hpoints] at hspec
  have hQ : ValidInterpolationWitness (initialNormalizedPoints received)
      ⟨1025, 3, 114689⟩ Q := by
    convert hspec using 1 <;> rfl
  have hc' : Candidates (CBivariate.toPoly Q) 1025 candidates := by
    simpa [AspisR1.GSConcreteRootRecovery.Candidates] using hc
  exact initial_runtime_list_to_Close_of_witness received Q candidates hQ hc'

/-- For any fixed-input decoder family, if each initial lane supplies the
actual normalized received-word points, then success of every initial root
call makes each runtime close list complete. -/
theorem all_initial_lanes_runtime_close_complete
    {finalCount : Nat} (inputs : Inputs WideExact finalCount)
    (W : Fin 29 → InitialWord WideExact) (q t : Nat)
    (hq : q = Fintype.card WideExact)
    (H : InitialTape WideExact t × FinalTape WideExact t)
    (hpoints : ∀ lane : Fin 29,
      inputs.initialPoints lane = initialNormalizedPoints (W lane))
    (hsuccess : ∀ lane : Fin 29,
      ∃ candidates,
        (run q t inputs H).1 lane = some candidates) :
    ∀ lane : Fin 29, ∃ candidates,
      (run q t inputs H).1 lane = some candidates ∧
      (initialRuntimeCloseList (W lane) candidates).toFinset =
        AspisR1.InitialResponses.Close (W lane) := by
  intro lane
  obtain ⟨candidates, hresult⟩ := hsuccess lane
  refine ⟨candidates, hresult, ?_⟩
  have hout : initial q t (inputs.initialPoints lane)
      (inputs.initialSize lane) H.1 = some candidates := by
    simpa [run] using hresult
  exact initial_call_success_runtime_list_to_Close (W lane)
    (inputs.initialPoints lane) (hpoints lane) (inputs.initialSize lane) q t hq H.1 candidates hout

#print axioms initial_runtime_list_to_Close_of_witness
#print axioms initial_call_success_runtime_list_to_Close
#print axioms all_initial_lanes_runtime_close_complete

end AspisWide.GSActualRuntimeCloseCompleteness
