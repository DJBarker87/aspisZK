import AspisFormal.K1.V7Tag73ExactCleanBidirectionalFoldOneFoldComponents
import AspisFormal.K1.V7Tag73ExactBidirectionalFoldOneFoldFibreTarget

/-!
# Corrected chronological one-fold target transport

This leaf transports a corrected pre-q16 one-fold failure across a fixed
residual/fold fibre.  It deliberately uses the chronological word carried by
`ExactPreQ16K13StageOneFoldFailure`; no equality with the legacy completed K1.2
word is introduced.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

namespace AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldFibreTarget

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73CausalOneFoldProbability
open AspisK1.V7Tag73CausalRawOneFoldTarget
open AspisK1.V7Tag73CompleteCausalOrdinaryProbability
open AspisK1.V7Tag73CounterfactualOneFoldProvider
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactBidirectionalFoldAnchor
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldBadTarget
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldFibreTarget
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldProjection
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplay
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplayFilter
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldTrialEvent
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactFixedK13K14FailureReduction
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactOneFoldRestorationStrategy
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7MerkleQueryExtractor
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

noncomputable section

/-- Every corrected right-hand failure lies in the fixed causal target chosen
from a left representative once the genuine pre-alpha semantic fields agree.
The remaining source work is therefore exactly the three stated equalities. -/
theorem exact_clean_bidirectional_onefold_failure_mem_leftRawTarget
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
    (leftWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) trial)
    (rightWitness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
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
    (wordsExact : leftWitness.failure.words = rightWitness.failure.words)
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
          finalEncoderExact leftWitness.failure.words leftWitness.input
          leftWitness.fold leftSource)
        (successfulOrdinaryExactFactorization
          (exactAcceptedFoldCoordinateRaw transitionRoom programmedCover
            rightWitness.input rightWitness.fold)).1 := by
  let actual := exactAcceptedFoldCoordinateAttempt transitionRoom
    programmedCover rightWitness.input rightWitness.fold
  let oracle := exactAcceptedFoldReplayOracle leftWitness.failure.words
    leftWitness.input leftWitness.fold
  have proofExact : oracle.proof? actual =
      some (exactK13ParsedProof rightWitness.input) :=
    exactBidirectionalFoldOneFoldReplayOracle_crossProof_inputs transitionRoom
      programmedCover leftWitness.failure.words leftWitness.input
        rightWitness.input leftWitness.fold rightWitness.fold
          leftWitness.trialExact rightWitness.trialExact residualExact foldExact
            gammaExact scheduleExact
  have failure := rightWitness.failure.failure
  rw [← wordsExact] at failure
  have bad := actual_oneFold_failure_is_counterfactual_bad_response decoder
    (exactOneFoldAlgebraBinding (exactK13ParsedProof leftWitness.input).schedule
      (exactK13Encoders decoder) initialEncoderExact finalEncoderExact
      leftSource.inverseTablesExact)
    oracle actual (exactK13ParsedProof rightWitness.input) proofExact failure
  rw [exactRawOneFoldTarget_exactAcceptedFoldOneFoldContext]
  rw [mem_causalOneFoldFailureTarget_iff]
  exact bad

#print axioms exact_clean_bidirectional_onefold_failure_mem_leftRawTarget

end

end AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldFibreTarget
