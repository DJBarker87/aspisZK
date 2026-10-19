import GSRuntimeFinalDistanceEncoderBridge
import GSWideExactAgreementInputs
import GSInterpolationAgreementCore
import GSActualEncoderGRSBridge
import GSRootCandidateContract
import AspisFormal.Pool.AlgorithmicCircleDecoderV7

set_option autoImplicit false

namespace AspisWide.GSFinalActualMessageRecovery

open CompPoly CompPoly.CBivariate CompPoly.GuruswamiSudan
open AspisWideTower
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSRootCandidateContract
open AspisWide.GSWideExactAgreementInputs
open AspisWide.GSInterpolationAgreementCore
open AspisWide.GSActualEncoderGRSBridge
open AspisWide.GSRuntimeFinalDistanceEncoderBridge
open AspisWide.WideExactGRSInstantiation
open AspisR1.RRFinalMessageRecovery
open AspisV5FriConcreteEncoderApplicability

attribute [local irreducible] finalRuntimeCloseList

theorem final_runtime_close_list_mem_iff
    (received : FinalWord WideExact) (m : FinalMessage WideExact)
    (Q : CBivariate WideExact) (candidates : List (List WideExact))
    (hQ : ValidInterpolationWitness (finalNormalizedPoints received)
      ⟨256, 3, 28673⟩ Q)
    (hc : Candidates (CBivariate.toPoly Q) 256 candidates) :
    m ∈ finalRuntimeCloseList received candidates ↔
      closeAtLeast 9558
        (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact))
        received m := by
  constructor
  · intro hm
    have hruntime := AspisWide.GSRuntimeFinalDistanceEncoderBridge.finalRuntimeCloseList_mem_iff received candidates m
    exact hruntime.mp hm |>.2
  · intro hclose
    have hencode := final_encode_to_grs_messagePolynomial m
    have hmatches := final_close_gives_strict_match_bound
      received m (encodeFinal m) hencode hclose
    have hdegree := final_encode_degreeLt m
    have hzero := valid_witness_agreement_forces_eval_zero hQ hdegree
      (final_points_distinct received) hmatches
    have hfilter := (AspisWide.GSFinalMessageCandidateFilter.filterCandidates_mem_iff
      (CBivariate.toPoly Q) candidates hc m).2 hzero
    have hruntime := AspisWide.GSRuntimeFinalDistanceEncoderBridge.finalRuntimeCloseList_mem_iff received candidates m
    exact hruntime.mpr ⟨hfilter, hclose⟩

#print axioms final_runtime_close_list_mem_iff

end AspisWide.GSFinalActualMessageRecovery
