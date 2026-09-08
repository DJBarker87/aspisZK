import AspisFormal.K1.V7Tag73CausalOneFoldProbability
import AspisFormal.K1.V7Tag73ParsedK13K14Classifier

/-!
# Core counterfactual Tag-73 alpha response provider

This lightweight leaf defines the future-free parsed-proof family and its
alpha-dependent one-fold strategy. The heavier algebraic bad-response proof
lives in `V7Tag73CounterfactualOneFoldFailureBridge`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

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

def ordinaryForSkeletonValue
    (skeleton : Tag73CompleteOrdinarySamplerSkeleton)
    (value : QM31Exact) : SuccessfulTag73DuplexOrdinaryAttempt :=
  successfulDuplexOrdinaryFactorization.symm (skeleton, value)

@[simp] theorem ordinaryForSkeletonValue_factorization
    (sample : SuccessfulTag73DuplexOrdinaryAttempt) :
    ordinaryForSkeletonValue
        (successfulDuplexOrdinaryFactorization sample).1
        (successfulDuplexOrdinaryFactorization sample).2 = sample := by
  exact successfulDuplexOrdinaryFactorization.symm_apply_apply sample

@[simp] theorem ordinaryForSkeletonValue_returns_value
    (skeleton : Tag73CompleteOrdinarySamplerSkeleton)
    (value : QM31Exact) :
    successfulDuplexOrdinaryValue (ordinaryForSkeletonValue skeleton value) =
      value := by
  have exact := successfulDuplexOrdinaryFactorization.apply_symm_apply
    (skeleton, value)
  rw [← successfulDuplexOrdinaryFactorization_value]
  exact congrArg Prod.snd exact

/-- Minimal deterministic future-free seam at alpha. It contains no
probability, acceptance, extraction or witness conclusion. -/
structure CounterfactualParsedOneFoldOracle
    (words : AspisPool.V7MerkleQueryExtractor.ExtractedWords)
    (gamma : QM31Exact) (baseSchedule : ExactSchedule) where
  defaultFinal : FinalMessage QM31Exact
  proof? : SuccessfulTag73DuplexOrdinaryAttempt → Option Tag73K12ParsedProof
  proofGammaExact : ∀ sample proof, proof? sample = some proof →
    proof.gamma = gamma
  proofScheduleExact : ∀ sample proof, proof? sample = some proof →
    proof.schedule = scheduleAtAlpha baseSchedule
      (successfulDuplexOrdinaryValue sample)

def counterfactualOneFoldProof?
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {baseSchedule : ExactSchedule}
    (oracle : CounterfactualParsedOneFoldOracle words gamma baseSchedule)
    (skeleton : Tag73CompleteOrdinarySamplerSkeleton)
    (alpha : QM31Exact) : Option Tag73K12ParsedProof :=
  oracle.proof? (ordinaryForSkeletonValue skeleton alpha)

noncomputable def counterfactualOneFoldStrategy
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {baseSchedule : ExactSchedule}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (oracle : CounterfactualParsedOneFoldOracle words gamma baseSchedule)
    (skeleton : Tag73CompleteOrdinarySamplerSkeleton) :
    ProximateStrategy QM31Exact (Fin 262144) (FinalCoefficients QM31Exact) := by
  classical
  exact {
    candidate := fun alpha =>
      match counterfactualOneFoldProof? oracle skeleton alpha with
      | some proof => proof.disclosedFinal
      | none => oracle.defaultFinal
    support := fun alpha =>
      match counterfactualOneFoldProof? oracle skeleton alpha with
      | some proof =>
          consistencySet (scheduleAtAlpha baseSchedule alpha)
            (decoderCodeEncoders decoder) (parsedK13Transcript words proof)
      | none => ∅
  }

def counterfactualOneFoldBase
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {baseSchedule : ExactSchedule}
    (oracle : CounterfactualParsedOneFoldOracle words gamma baseSchedule) :
    IdealTranscript QM31Exact :=
  extractedIdealTranscript words gamma oracle.defaultFinal

theorem actual_ordinary_counterfactual_proof_exact
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {baseSchedule : ExactSchedule}
    (oracle : CounterfactualParsedOneFoldOracle words gamma baseSchedule)
    (sample : SuccessfulTag73DuplexOrdinaryAttempt)
    (proof : Tag73K12ParsedProof) (proofExact : oracle.proof? sample = some proof) :
    counterfactualOneFoldProof? oracle
        (successfulDuplexOrdinaryFactorization sample).1
        (successfulDuplexOrdinaryValue sample) = some proof := by
  unfold counterfactualOneFoldProof?
  rw [show ordinaryForSkeletonValue
      (successfulDuplexOrdinaryFactorization sample).1
      (successfulDuplexOrdinaryValue sample) = sample by
    rw [← successfulDuplexOrdinaryFactorization_value]
    exact ordinaryForSkeletonValue_factorization sample]
  exact proofExact

theorem actual_counterfactual_candidate_exact
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {baseSchedule : ExactSchedule}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (oracle : CounterfactualParsedOneFoldOracle words gamma baseSchedule)
    (sample : SuccessfulTag73DuplexOrdinaryAttempt)
    (proof : Tag73K12ParsedProof) (proofExact : oracle.proof? sample = some proof) :
    (counterfactualOneFoldStrategy decoder oracle
      (successfulDuplexOrdinaryFactorization sample).1).candidate
        (successfulDuplexOrdinaryValue sample) = proof.disclosedFinal := by
  rw [counterfactualOneFoldStrategy]
  simp only
  rw [actual_ordinary_counterfactual_proof_exact oracle sample proof proofExact]

theorem actual_counterfactual_support_exact
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {baseSchedule : ExactSchedule}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (oracle : CounterfactualParsedOneFoldOracle words gamma baseSchedule)
    (sample : SuccessfulTag73DuplexOrdinaryAttempt)
    (proof : Tag73K12ParsedProof) (proofExact : oracle.proof? sample = some proof) :
    (counterfactualOneFoldStrategy decoder oracle
      (successfulDuplexOrdinaryFactorization sample).1).support
        (successfulDuplexOrdinaryValue sample) =
      consistencySet proof.schedule (decoderCodeEncoders decoder)
        (parsedK13Transcript words proof) := by
  rw [counterfactualOneFoldStrategy]
  simp only
  rw [actual_ordinary_counterfactual_proof_exact oracle sample proof proofExact]
  rw [oracle.proofScheduleExact sample proof proofExact]

theorem actual_counterfactual_base_initial_exact
    {words : AspisPool.V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {baseSchedule : ExactSchedule}
    (oracle : CounterfactualParsedOneFoldOracle words gamma baseSchedule)
    (sample : SuccessfulTag73DuplexOrdinaryAttempt)
    (proof : Tag73K12ParsedProof) (proofExact : oracle.proof? sample = some proof) :
    (counterfactualOneFoldBase oracle).initial =
      (parsedK13Transcript words proof).initial := by
  unfold counterfactualOneFoldBase parsedK13Transcript extractedIdealTranscript
  rw [oracle.proofGammaExact sample proof proofExact]

#print axioms ordinaryForSkeletonValue_factorization
#print axioms actual_ordinary_counterfactual_proof_exact
#print axioms actual_counterfactual_support_exact

end
end AspisK1.V7Tag73CounterfactualOneFoldProvider
