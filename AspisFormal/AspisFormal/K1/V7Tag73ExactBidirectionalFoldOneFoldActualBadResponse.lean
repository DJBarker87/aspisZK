import AspisFormal.K1.V7Tag73CounterfactualOneFoldFailureBridge
import AspisFormal.K1.V7Tag73ExactBidirectionalFoldOneFoldBadTargetCore

/-!
# Accepted production failure as an exact causal bad response

This leaf ends at the algebraic causal-response predicate.  Target membership
and raw-stream normalization live in the following leaf so Lean never has to
normalize the complete production replay and probability event at once.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000

namespace AspisK1.V7Tag73ExactBidirectionalFoldOneFoldActualBadResponse

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CausalOneFoldProbability
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73CounterfactualOneFoldProvider
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldBadTarget
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplay
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplayFilter
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- Word-parametric source form of the accepted one-fold bad-response bridge.
The corrected classifier supplies the chronological pre-q16 word directly,
so this theorem does not identify it with the legacy completed K1.2 word. -/
theorem exactAcceptedFoldWordsActualOneFoldBadResponse
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
    CausalOneFoldBadResponse (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder)
      (exactOneFoldAlgebraBinding (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) initialEncoderExact finalEncoderExact
        source.inverseTablesExact)
      (counterfactualOneFoldBase
        (exactAcceptedFoldReplayOracle words input fold))
      (counterfactualOneFoldStrategy decoder
        (exactAcceptedFoldReplayOracle words input fold)
        (successfulDuplexOrdinaryFactorization
          (exactAcceptedFoldCoordinateAttempt transitionRoom programmedCover
            input fold)).1)
      (successfulDuplexOrdinaryValue
        (exactAcceptedFoldCoordinateAttempt transitionRoom programmedCover
          input fold)) := by
  let actual := exactAcceptedFoldCoordinateAttempt transitionRoom
    programmedCover input fold
  let oracle := exactAcceptedFoldReplayOracle words input fold
  have proofExact : oracle.proof? actual = some (exactK13ParsedProof input) :=
    exactAcceptedFoldReplayOracle_actualProof transitionRoom programmedCover
      words input fold source
  exact actual_oneFold_failure_is_counterfactual_bad_response decoder
    (exactOneFoldAlgebraBinding (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder) initialEncoderExact finalEncoderExact
      source.inverseTablesExact)
    oracle actual (exactK13ParsedProof input) proofExact failure

/-- Literal production failure at the accepted alpha is a bad response for the
future-free replay family fixed before that alpha value is returned. -/
theorem exactAcceptedFoldActualOneFoldBadResponse
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
    CausalOneFoldBadResponse (exactK13ParsedProof input).schedule
      (exactK13Encoders decoder)
      (exactOneFoldAlgebraBinding (exactK13ParsedProof input).schedule
        (exactK13Encoders decoder) initialEncoderExact finalEncoderExact
        source.inverseTablesExact)
      (counterfactualOneFoldBase
        (exactAcceptedFoldReplayOracle k12.words input fold))
      (counterfactualOneFoldStrategy decoder
        (exactAcceptedFoldReplayOracle k12.words input fold)
        (successfulDuplexOrdinaryFactorization
          (exactAcceptedFoldCoordinateAttempt transitionRoom programmedCover
            input fold)).1)
      (successfulDuplexOrdinaryValue
        (exactAcceptedFoldCoordinateAttempt transitionRoom programmedCover
          input fold)) := by
  have failure' := failure
  change OneFoldReductionFailure (exactK13ParsedProof input).schedule
    (decoderCodeEncoders decoder)
    (parsedK13Transcript k12.words (exactK13ParsedProof input)) at failure'
  exact exactAcceptedFoldWordsActualOneFoldBadResponse transitionRoom
    programmedCover decoder initialEncoderExact finalEncoderExact k12.words
    input fold source failure'

#print axioms exactAcceptedFoldWordsActualOneFoldBadResponse
#print axioms exactAcceptedFoldActualOneFoldBadResponse

end
end AspisK1.V7Tag73ExactBidirectionalFoldOneFoldActualBadResponse
