import AspisFormal.K1.V7Tag73ExactBidirectionalFoldOneFoldFibreReplay

/-!
# Exact bad-target transport across one fold/alpha fibre

The probability context is chosen from one representative of a fixed
residual/fold fibre.  This leaf records the precise pre-alpha semantic data
which must agree across that fibre and proves that every other accepted
member's literal one-fold failure lies in the representative's fixed target.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

namespace AspisK1.V7Tag73ExactBidirectionalFoldOneFoldFibreTarget

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73CausalOneFoldProbability
open AspisK1.V7Tag73CausalFoldOneFoldTapeBridge
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldRawOneFoldProduct
open AspisK1.V7Tag73CausalRawOneFoldProbability
open AspisK1.V7Tag73CausalRawOneFoldProductProbability
open AspisK1.V7Tag73CausalRawOneFoldTarget
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73CounterfactualOneFoldProvider
open AspisK1.V7Tag73CounterfactualOneFoldReplayFilter
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldBadTarget
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldFibreReplay
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldProjection
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplay
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplayFilter
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldTrialEvent
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK12PrefixClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactOneFoldRestorationStrategy
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73ParsedK13K14Classifier
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- Exact semantic data which must be fixed before alpha on one residual/fold
fibre.  The schedule conclusion permits exactly the new alpha and keeps every
inverse-table entry fixed. -/
def ExactBidirectionalK13OneFoldFibreInvariant
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat)
    (configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters)
    (projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload)
    (fixedInstance : PublicInstance Statement)
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop :=
  ∀ (trial : ExactCompilerExposureTrial parameters) (hidden : HiddenTape)
      (left right : FreshAnswerTape Digest256
        (exactCompilerTargetCaps parameters).length)
      (leftWitness : ExactBidirectionalK13OneFoldTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, left) trial)
      (rightWitness : ExactBidirectionalK13OneFoldTrialWitness transitionFuel
        configuration projection fixedInstance decoder (hidden, right) trial),
    (let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
      transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        left).1 =
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        right).1) →
    (let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
      transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
    (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        left).2.1 =
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        right).2.1) →
    leftWitness.k12.words = rightWitness.k12.words ∧
      (exactK13ParsedProof leftWitness.input).gamma =
        (exactK13ParsedProof rightWitness.input).gamma ∧
      (exactK13ParsedProof rightWitness.input).schedule =
        scheduleAtAlpha (exactK13ParsedProof leftWitness.input).schedule
          (exactOperationalChallenge rightWitness.input (.alpha 0))

/-- The representative's executable filter exposes the right member's
literal parsed proof at the right member's successful alpha coordinate. -/
theorem exactBidirectionalFoldOneFoldReplayOracle_crossProof
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {trial : ExactCompilerExposureTrial parameters}
    {hidden : HiddenTape}
    {left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (leftWitness : ExactBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) trial)
    (residualExact :
      let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
        transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        left).1 =
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        right).1)
    (foldExact :
      let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
        transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        left).2.1 =
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        right).2.1)
    (gammaExact : (exactK13ParsedProof leftWitness.input).gamma =
      (exactK13ParsedProof rightWitness.input).gamma)
    (scheduleExact : (exactK13ParsedProof rightWitness.input).schedule =
      scheduleAtAlpha (exactK13ParsedProof leftWitness.input).schedule
        (exactOperationalChallenge rightWitness.input (.alpha 0))) :
    (exactAcceptedFoldReplayOracle leftWitness.k12.words leftWitness.input
        leftWitness.fold).proof?
      (exactAcceptedFoldCoordinateAttempt transitionRoom programmedCover
        rightWitness.input rightWitness.fold) =
      some (exactK13ParsedProof rightWitness.input) := by
  let actual := exactAcceptedFoldCoordinateAttempt transitionRoom
    programmedCover rightWitness.input rightWitness.fold
  let replay := fun attempt : SuccessfulTag73DuplexOrdinaryAttempt =>
    exactBidirectionalFoldOneFoldRawReplay transitionFuel configuration hidden
      (exactAcceptedFoldBidirectionalRouter leftWitness.input leftWitness.fold)
      (exactAcceptedFoldBidirectionalCoordinates leftWitness.input
        leftWitness.fold).1
      (exactAcceptedFoldBidirectionalCoordinates leftWitness.input
        leftWitness.fold).2.1 attempt.1
  have returned : (replay actual).terminal =
      .returned (.completed (exactK12Runtime rightWitness.input)
        rightWitness.input.package.root.full.clientRun) := by
    have runExact := exactBidirectionalFoldOneFoldRawReplay_cross
      transitionRoom programmedCover leftWitness rightWitness residualExact
        foldExact
    rw [show replay actual = runExactPlainRom transitionFuel configuration
        (hidden, right) by exact runExact]
    exact exactOperationalPlainRom_terminal rightWitness.input
  have alphaExact : successfulDuplexOrdinaryValue actual =
      exactOperationalChallenge rightWitness.input (.alpha 0) :=
    exactAcceptedFoldCoordinateRaw_value transitionRoom programmedCover
      rightWitness.input rightWitness.fold
  apply plainRomReplayOracle_actualProof
    (words := leftWitness.k12.words)
    (exactK13ParsedProof leftWitness.input).gamma
    (exactK13ParsedProof leftWitness.input).schedule
    (exactK13ParsedProof leftWitness.input).disclosedFinal replay actual
    (exactK12Runtime rightWitness.input)
    rightWitness.input.package.root.full.clientRun returned
  · exact gammaExact.symm
  · rw [alphaExact]
    exact scheduleExact

/-- Every accepted right member lies in the fixed degree-three target chosen
from a left representative of the same residual/fold fibre. -/
theorem exactBidirectionalFoldOneFoldFailure_mem_leftRawTarget
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {trial : ExactCompilerExposureTrial parameters}
    {hidden : HiddenTape}
    {left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length}
    {leftDecoded : Fin 641 → QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (initialEncoderExact : decoder.initialEncoder = exactInitialEncoder)
    (finalEncoderExact : decoder.finalEncoder = exactFinalEncoder)
    (leftWitness : ExactBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) trial)
    (leftSource : ExactParsedProofSourceBinding leftWitness.input leftDecoded)
    (residualExact :
      let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
        transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        left).1 =
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        right).1)
    (foldExact :
      let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
        transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        left).2.1 =
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        right).2.1)
    (wordsExact : leftWitness.k12.words = rightWitness.k12.words)
    (gammaExact : (exactK13ParsedProof leftWitness.input).gamma =
      (exactK13ParsedProof rightWitness.input).gamma)
    (scheduleExact : (exactK13ParsedProof rightWitness.input).schedule =
      scheduleAtAlpha (exactK13ParsedProof leftWitness.input).schedule
        (exactOperationalChallenge rightWitness.input (.alpha 0))) :
    successfulOrdinaryExactValue
        (exactAcceptedFoldCoordinateRaw transitionRoom programmedCover
          rightWitness.input rightWitness.fold) ∈
      exactRawOneFoldTarget
        (exactAcceptedFoldOneFoldContext decoder initialEncoderExact
          finalEncoderExact leftWitness.k12.words leftWitness.input
          leftWitness.fold leftSource)
        (successfulOrdinaryExactFactorization
          (exactAcceptedFoldCoordinateRaw transitionRoom programmedCover
            rightWitness.input rightWitness.fold)).1 := by
  let actual := exactAcceptedFoldCoordinateAttempt transitionRoom
    programmedCover rightWitness.input rightWitness.fold
  let oracle := exactAcceptedFoldReplayOracle leftWitness.k12.words
    leftWitness.input leftWitness.fold
  have proofExact : oracle.proof? actual =
      some (exactK13ParsedProof rightWitness.input) :=
    exactBidirectionalFoldOneFoldReplayOracle_crossProof transitionRoom
      programmedCover leftWitness rightWitness residualExact foldExact
        gammaExact scheduleExact
  have failure := rightWitness.failure
  change OneFoldReductionFailure (exactK13ParsedProof rightWitness.input).schedule
    (decoderCodeEncoders decoder)
    (parsedK13Transcript rightWitness.k12.words
      (exactK13ParsedProof rightWitness.input)) at failure
  rw [← wordsExact] at failure
  have bad := actual_oneFold_failure_is_counterfactual_bad_response decoder
    (exactOneFoldAlgebraBinding (exactK13ParsedProof leftWitness.input).schedule
      (exactK13Encoders decoder) initialEncoderExact finalEncoderExact
      leftSource.inverseTablesExact)
    oracle actual (exactK13ParsedProof rightWitness.input) proofExact failure
  rw [exactRawOneFoldTarget_exactAcceptedFoldOneFoldContext]
  rw [mem_causalOneFoldFailureTarget_iff]
  exact bad

end

#print axioms ExactBidirectionalK13OneFoldFibreInvariant
#print axioms exactBidirectionalFoldOneFoldReplayOracle_crossProof
#print axioms exactBidirectionalFoldOneFoldFailure_mem_leftRawTarget

end AspisK1.V7Tag73ExactBidirectionalFoldOneFoldFibreTarget
