import GSRuntimeInitialDistanceEncoderBridge
import GSWideExactAgreementInputs
import GSInterpolationAgreementCore
import GSActualEncoderGRSBridge
import GSRootCandidateContract
import AspisFormal.Pool.AlgorithmicCircleDecoderV7

set_option autoImplicit false

namespace AspisWide.GSInitialActualMessageRecovery

open CompPoly CompPoly.CBivariate CompPoly.GuruswamiSudan
open AspisWideTower
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSRootCandidateContract
open AspisWide.GSWideExactAgreementInputs
open AspisWide.GSInterpolationAgreementCore
open AspisWide.GSActualEncoderGRSBridge
open AspisWide.GSRuntimeInitialDistanceEncoderBridge
open AspisWide.WideExactGRSInstantiation
open AspisR1.RRFinalMessageRecovery
open AspisWide.InitialForwardEncoderBaseV9
open AspisV5FriConcreteEncoderApplicability

attribute [local irreducible] initialRuntimeCloseList

theorem initial_runtime_close_list_mem_iff
    (received : InitialWord WideExact) (m : InitialMessage WideExact)
    (Q : CBivariate WideExact) (candidates : List (List WideExact))
    (hQ : ValidInterpolationWitness (initialNormalizedPoints received)
      ⟨1025, 3, 114689⟩ Q)
    (hc : Candidates (CBivariate.toPoly Q) 1025 candidates) :
    m ∈ initialRuntimeCloseList received candidates ↔
      closeAtLeast 38230
        (AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact))
        received m := by
  constructor
  · intro hm
    have hruntime := AspisWide.GSRuntimeInitialDistanceEncoderBridge.initialRuntimeCloseList_mem_iff received candidates m
    exact hruntime.mp hm |>.2
  · intro hclose
    have hencode := initial_encode_to_grs_messagePolynomial m
    have hmatches := initial_close_gives_strict_match_bound
      received m (encodeInitialC m) hencode hclose
    have hdegree := initial_encode_degreeLt m
    have hzero := valid_witness_agreement_forces_eval_zero hQ hdegree
      (initial_points_distinct received) hmatches
    have hfilter := (AspisWide.GSInitialMessageCandidateFilter.filterCandidates_mem_iff
      (CBivariate.toPoly Q) candidates hc m).2 hzero
    have hruntime := AspisWide.GSRuntimeInitialDistanceEncoderBridge.initialRuntimeCloseList_mem_iff received candidates m
    exact hruntime.mpr ⟨hfilter, hclose⟩

#print axioms initial_runtime_close_list_mem_iff

end AspisWide.GSInitialActualMessageRecovery
