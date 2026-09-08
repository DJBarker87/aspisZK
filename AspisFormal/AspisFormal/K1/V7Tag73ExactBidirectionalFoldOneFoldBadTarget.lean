import AspisFormal.K1.V7Tag73ExactBidirectionalFoldOneFoldActualBadResponse
import AspisFormal.K1.V7Tag73ExactBidirectionalFoldOneFoldBadTargetCore

/-!
# Exact accepted one-fold failure in the causal bad target

This leaf packages the executable replay oracle as the exact algebraic context
used by the degree-three probability theorem.  It proves the pointwise source
endpoint: an accepted production one-fold failure at the actual routed alpha
is a member of that fixed replay family's bad target.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73ExactBidirectionalFoldOneFoldBadTarget

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CausalOneFoldProbability
open AspisK1.V7Tag73CausalRawOneFoldProbability
open AspisK1.V7Tag73CausalRawOneFoldProductProbability
open AspisK1.V7Tag73CausalRawOneFoldTarget
open AspisK1.V7Tag73CounterfactualOneFoldProvider
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldActualBadResponse
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplay
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplayFilter
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73ExactInternalCurveProbability
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- The literal accepted alpha lies in the exact fixed causal degree-three
target built from any already-authenticated chronological word.  This is the
word-parametric form needed by the corrected pre-q16 classifier: the word is
fixed at its chronological anchor rather than reconstructed from the later
completed transcript. -/
theorem exactAcceptedFoldWordsOneFoldFailure_mem_exactRawTarget
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoded : Fin 641 → QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder)
    (words : ExtractedWords)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (source : ExactParsedProofSourceBinding input decoded)
    (failure : OneFoldReductionFailure (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder)
      (parsedK13Transcript words (exactK13ParsedProof input))) :
    successfulOrdinaryExactValue
        (exactAcceptedFoldCoordinateRaw transitionRoom programmedCover input
          fold) ∈
      exactRawOneFoldTarget
        (exactAcceptedFoldOneFoldContext decoder initialEncoderExact
          finalEncoderExact words input fold source)
        (successfulOrdinaryExactFactorization
          (exactAcceptedFoldCoordinateRaw transitionRoom programmedCover input
            fold)).1 := by
  let raw := exactAcceptedFoldCoordinateRaw transitionRoom programmedCover input
    fold
  let actual := exactAcceptedFoldCoordinateAttempt transitionRoom
    programmedCover input fold
  let oracle := exactAcceptedFoldReplayOracle words input fold
  let skeleton := (successfulOrdinaryExactFactorization raw).1
  have actualValue : successfulDuplexOrdinaryValue actual =
      successfulOrdinaryExactValue raw := by rfl
  have actualSkeleton :
      (successfulDuplexOrdinaryFactorization actual).1 =
        (skeleton, fun _ => fold.answer) := by
    apply Prod.ext
    · rfl
    · rfl
  have bad0 := exactAcceptedFoldWordsActualOneFoldBadResponse transitionRoom
    programmedCover decoder initialEncoderExact finalEncoderExact words input
    fold source failure
  rw [exactRawOneFoldTarget_exactAcceptedFoldOneFoldContext]
  rw [← actualValue, ← actualSkeleton]
  rw [mem_causalOneFoldFailureTarget_iff]
  exact bad0

/-- The literal accepted alpha lies in its exact fixed causal degree-three
target whenever the production classifier supplies a genuine one-fold
failure.  The following probability layer transports this target through the
already-proved raw-stream/product equivalence. -/
theorem exactAcceptedFoldOneFoldFailure_mem_exactRawTarget
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoded : Fin 641 → QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (decoder : ExactDecoderInstantiation QM31Exact)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (k12 : ExactPrefixK12Certificate input)
    (fold : ExactAcceptedFoldTrial input)
    (source : ExactParsedProofSourceBinding input decoded)
    (failure : OneFoldReductionFailure (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) (exactK13Transcript input k12)) :
    successfulOrdinaryExactValue
        (exactAcceptedFoldCoordinateRaw transitionRoom programmedCover input
          fold) ∈
      exactRawOneFoldTarget
        (exactAcceptedFoldOneFoldContext decoder initialEncoderExact
          finalEncoderExact k12.words input fold source)
        (successfulOrdinaryExactFactorization
          (exactAcceptedFoldCoordinateRaw transitionRoom programmedCover input
            fold)).1 := by
  let raw := exactAcceptedFoldCoordinateRaw transitionRoom programmedCover input
    fold
  let actual := exactAcceptedFoldCoordinateAttempt transitionRoom
    programmedCover input fold
  let oracle := exactAcceptedFoldReplayOracle k12.words input fold
  let skeleton := (successfulOrdinaryExactFactorization raw).1
  have actualValue : successfulDuplexOrdinaryValue actual =
      successfulOrdinaryExactValue raw := by rfl
  have actualSkeleton :
      (successfulDuplexOrdinaryFactorization actual).1 =
        (skeleton, fun _ => fold.answer) := by
    apply Prod.ext
    · rfl
    · rfl
  have bad0 := exactAcceptedFoldActualOneFoldBadResponse transitionRoom
    programmedCover decoder initialEncoderExact finalEncoderExact input k12 fold
    source failure
  rw [exactRawOneFoldTarget_exactAcceptedFoldOneFoldContext]
  rw [← actualValue, ← actualSkeleton]
  rw [mem_causalOneFoldFailureTarget_iff]
  exact bad0

#print axioms exactAcceptedFoldWordsOneFoldFailure_mem_exactRawTarget
#print axioms exactAcceptedFoldOneFoldFailure_mem_exactRawTarget

end
end AspisK1.V7Tag73ExactBidirectionalFoldOneFoldBadTarget
