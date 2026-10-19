import GSInitialMessageCandidateFilter
import GSFinalMessageCandidateFilter
import GSWideExactAgreementInputs
import GSInterpolationAgreementCore
import GSActualEncoderGRSBridge

set_option autoImplicit false

namespace AspisWide.GSActualMessageRecoveryFromWitness

open CompPoly CompPoly.CBivariate CompPoly.GuruswamiSudan
open AspisWide.GSRootCandidateContract
open AspisWide.GSInitialMessageCandidateFilter
open AspisWide.GSFinalMessageCandidateFilter
open AspisWide.GSWideExactAgreementInputs
open AspisWide.GSInterpolationAgreementCore
open AspisWide.GSActualEncoderGRSBridge
open AspisWide.WideExactGRSInstantiation
open AspisWide.InitialForwardEncoderBaseV9
open AspisV5FriConcreteEncoderApplicability
open AspisPool.AlgorithmicCircleDecoderV7

variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
  [NeZero (2 : K)] [Algebra (ZMod AspisCircleGroupOrder.P) K]
  [Fintype K] [LawfulBEq (CPolynomial K)]

theorem initial_close_message_mem
    (received : InitialWord WideExact) (m : InitialMessage WideExact)
    (Q : CBivariate WideExact) (candidates : List (List WideExact))
    (hQ : ValidInterpolationWitness (initialNormalizedPoints received)
      ⟨1025, 3, 114689⟩ Q)
    (hc : Candidates (CBivariate.toPoly Q) 1025 candidates)
    (hclose : closeAtLeast 38230
      (AspisWide.InitialEncoder.exactInitialEncoder (K := WideExact)) received m) :
    m ∈ GSInitialMessageCandidateFilter.filterCandidates candidates := by
  have hencode := initial_encode_to_grs_messagePolynomial m
  have hmatches := initial_close_gives_strict_match_bound
    received m (encodeInitialC m) hencode hclose
  have hdegree := initial_encode_degreeLt m
  have hzero := valid_witness_agreement_forces_eval_zero hQ hdegree
    (initial_points_distinct received) hmatches
  exact (GSInitialMessageCandidateFilter.filterCandidates_mem_iff
    (CBivariate.toPoly Q) candidates hc m).2 hzero

theorem final_close_message_mem
    (received : FinalWord WideExact) (m : FinalMessage WideExact)
    (Q : CBivariate WideExact) (candidates : List (List WideExact))
    (hQ : ValidInterpolationWitness (finalNormalizedPoints received)
      ⟨256, 3, 28673⟩ Q)
    (hc : Candidates (CBivariate.toPoly Q) 256 candidates)
    (hclose : closeAtLeast 9558
      (AspisWide.FinalEncoder.exactFinalEncoder (K := WideExact)) received m) :
    m ∈ GSFinalMessageCandidateFilter.filterCandidates candidates := by
  have hencode := final_encode_to_grs_messagePolynomial m
  have hmatches := final_close_gives_strict_match_bound
    received m (encodeFinal m) hencode hclose
  have hdegree := final_encode_degreeLt m
  have hzero := valid_witness_agreement_forces_eval_zero hQ hdegree
    (final_points_distinct received) hmatches
  exact (GSFinalMessageCandidateFilter.filterCandidates_mem_iff
    (CBivariate.toPoly Q) candidates hc m).2 hzero

#print axioms initial_close_message_mem
#print axioms final_close_message_mem

end AspisWide.GSActualMessageRecoveryFromWitness
