import AspisFormal.K1.V7Tag73CounterfactualOneFoldProviderCore

/-!
# Algebraic one-fold failure bridge

This leaf contains the heavier algebraic conversion from one literal
production reduction failure to the causal degree-three bad-response event.
It is separate from the source-facing provider definitions to keep focused
replay builds below the memory cap.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73CounterfactualOneFoldProvider

open AspisK1.V7Tag73CausalOneFoldProbability
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73ExactOneFoldRestorationStrategy
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCQM31TowerExact
open AspisV5FriDegreeThreeCorrelatedAgreement
open AspisV6OneFoldCandidateExtraction
open AspisV6PublishedTheoremInterfaces

noncomputable section

/-- A literal actual one-fold failure is a bad response of the complete
counterfactual alpha strategy built from the same future-free oracle. -/
theorem actual_oneFold_failure_is_counterfactual_bad_response
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {baseSchedule : ExactSchedule}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : OneFoldAlgebraBinding baseSchedule
      (decoderCodeEncoders decoder))
    (oracle : CounterfactualParsedOneFoldOracle words gamma baseSchedule)
    (sample : SuccessfulTag73DuplexOrdinaryAttempt)
    (proof : Tag73K12ParsedProof) (proofExact : oracle.proof? sample = some proof)
    (failure : OneFoldReductionFailure proof.schedule
      (decoderCodeEncoders decoder) (parsedK13Transcript words proof)) :
    CausalOneFoldBadResponse baseSchedule (decoderCodeEncoders decoder) binding
      (counterfactualOneFoldBase oracle)
      (counterfactualOneFoldStrategy decoder oracle
        (successfulDuplexOrdinaryFactorization sample).1)
      (successfulDuplexOrdinaryValue sample) := by
  let alpha := successfulDuplexOrdinaryValue sample
  let strategy := counterfactualOneFoldStrategy decoder oracle
    (successfulDuplexOrdinaryFactorization sample).1
  have scheduleExact : proof.schedule = scheduleAtAlpha baseSchedule alpha :=
    oracle.proofScheduleExact sample proof proofExact
  have candidateExact : strategy.candidate alpha = proof.disclosedFinal :=
    actual_counterfactual_candidate_exact decoder oracle sample proof proofExact
  have supportExact : strategy.support alpha =
      consistencySet proof.schedule (decoderCodeEncoders decoder)
        (parsedK13Transcript words proof) :=
    actual_counterfactual_support_exact decoder oracle sample proof proofExact
  have initialExact : (counterfactualOneFoldBase oracle).initial =
      (parsedK13Transcript words proof).initial :=
    actual_counterfactual_base_initial_exact oracle sample proof proofExact
  have transcriptExact : causalOneFoldTranscriptAt
      (counterfactualOneFoldBase oracle) strategy alpha =
        parsedK13Transcript words proof := by
    cases leftEq : counterfactualOneFoldBase oracle with
    | mk leftInitial leftFinal =>
      cases rightEq : parsedK13Transcript words proof with
      | mk rightInitial rightFinal =>
        simp only [leftEq, rightEq] at initialExact
        have rightFinalExact : rightFinal = proof.disclosedFinal := by
          have exact : (parsedK13Transcript words proof).disclosedFinal =
              proof.disclosedFinal := rfl
          simpa only [rightEq] using exact
        have candidateRight : strategy.candidate alpha = rightFinal :=
          candidateExact.trans rightFinalExact.symm
        simp only [causalOneFoldTranscriptAt]
        rw [initialExact, candidateRight]
  constructor
  · constructor
    · rw [supportExact]
      exact failure.1
    · intro index member
      have member' : index ∈ consistencySet proof.schedule
          (decoderCodeEncoders decoder) (parsedK13Transcript words proof) := by
        rw [← supportExact]
        exact member
      have consistent : QueryConsistent proof.schedule
          (decoderCodeEncoders decoder) (parsedK13Transcript words proof) index := by
        simpa [consistencySet] using member'
      rw [curve_oneFoldDecodedLanes_eq_circleFold baseSchedule
        (decoderCodeEncoders decoder) binding
        (counterfactualOneFoldBase oracle) alpha index]
      change circleFoldLayer 262144 alpha baseSchedule.circleInv2x
          baseSchedule.circleInv2y (counterfactualOneFoldBase oracle).initial index =
        binding.finalLinear (strategy.candidate alpha) index
      rw [initialExact, candidateExact]
      calc
        (circleFoldLayer 262144 alpha baseSchedule.circleInv2x
            baseSchedule.circleInv2y)
              (parsedK13Transcript words proof).initial index =
            (decoderCodeEncoders decoder).final proof.disclosedFinal index := by
          simpa [QueryConsistent, scheduleExact, scheduleAtAlpha,
            parsedK13Transcript, extractedIdealTranscript] using consistent
        _ = binding.finalLinear proof.disclosedFinal index := by
          rw [binding.finalEncoderEq]
  · intro predecessor
    apply failure.2
    rcases predecessor with ⟨candidate, supported, folded⟩
    change SupportedNearInitial (scheduleAtAlpha baseSchedule alpha)
      (decoderCodeEncoders decoder)
      (causalOneFoldTranscriptAt (counterfactualOneFoldBase oracle)
        strategy alpha) candidate at supported
    change foldInitial (scheduleAtAlpha baseSchedule alpha) candidate =
      strategy.candidate alpha at folded
    rw [← scheduleExact, transcriptExact] at supported
    rw [← scheduleExact, candidateExact] at folded
    exact ⟨candidate, supported, folded⟩

#print axioms actual_oneFold_failure_is_counterfactual_bad_response

end
end AspisK1.V7Tag73CounterfactualOneFoldProvider
