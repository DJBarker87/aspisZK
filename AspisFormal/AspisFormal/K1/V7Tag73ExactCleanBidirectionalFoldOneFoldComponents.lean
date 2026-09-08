import AspisFormal.K1.V7Tag73ExactCleanBidirectionalFoldOneFoldTrialEvent
import AspisFormal.K1.V7Tag73ExactBidirectionalFoldOneFoldBadTarget
import AspisFormal.K1.V7Tag73FoldOneFoldComponentMembership

/-!
# Corrected pre-q16 one-fold component facts

This leaf connects one clean chronological pre-q16 failure to the exact five
coordinates used by the bidirectional fold/alpha probability theorem.  It is
deliberately word-parametric: the target is built from the word retained by
`ExactPreQ16K13StageOneFoldFailure`, not the legacy completed K1.2 word.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldComponents

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Probability
open AspisK1.V7Tag73CausalFoldOneFoldTapeBridge
open AspisK1.V7Tag73CausalRawOneFoldTarget
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldBadTarget
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldProjection
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplay
open AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldTrialEvent
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldOneFoldComponentMembership
open AspisK1.V7Tag73K13PreQ16JointEventHandoff
open AspisK1.V7Tag73SuccessfulSamplerConditioningBridge
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7C1ConcreteProjectionBinding
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- A corrected clean witness uses exactly its fixed exposure-indexed
bidirectional router. -/
theorem exact_clean_preQ16_onefold_router_exact
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {sample : ExactCompilerSample HiddenTape parameters}
    {trial : ExactCompilerExposureTrial parameters}
    (witness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder sample trial) :
    exactAcceptedFoldBidirectionalRouter witness.input witness.fold =
      exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
        trial.val (exactPlainRomCursor configuration sample.1).erase := by
  unfold exactAcceptedFoldBidirectionalRouter
  rw [witness.trialExact]

/-- The fixed-trial coordinate is literally the accepted fold coordinate. -/
theorem exact_clean_preQ16_onefold_coordinate_eq_accepted
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {sample : ExactCompilerSample HiddenTape parameters}
    {trial : ExactCompilerExposureTrial parameters}
    (witness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder sample trial) :
    exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
        (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
          trial.val (exactPlainRomCursor configuration sample.1).erase)
        sample.2 =
      exactAcceptedFoldBidirectionalCoordinates witness.input witness.fold := by
  let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
    transitionFuel trial.val
    (exactPlainRomCursor configuration sample.1).erase
  change
    exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        sample.2 =
      exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
        (exactAcceptedFoldBidirectionalRouter witness.input witness.fold)
        sample.2
  rw [exact_clean_preQ16_onefold_router_exact witness]

/-- The actual four alpha blocks at a corrected clean trial pass the deployed
bounded decoder. -/
theorem exact_clean_preQ16_onefold_alpha_succeeds
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {sample : ExactCompilerSample HiddenTape parameters}
    {trial : ExactCompilerExposureTrial parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (witness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder sample trial) :
    foldAlphaTotalSucceeds
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
        (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
          trial.val (exactPlainRomCursor configuration sample.1).erase)
        sample.2).2 := by
  rw [exact_clean_preQ16_onefold_coordinate_eq_accepted witness]
  exact exact_accepted_fold_probability_coordinate_alpha_succeeds
    transitionRoom programmedCover witness.input witness.fold

/-- The distinguished fold coordinate at a corrected clean trial satisfies
the literal deployed 31-bit work predicate. -/
theorem exact_clean_preQ16_onefold_work_accepted
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {sample : ExactCompilerSample HiddenTape parameters}
    {trial : ExactCompilerExposureTrial parameters}
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (witness : ExactCleanBidirectionalK13OneFoldTrialWitness transitionFuel
      configuration projection fixedInstance decoder sample trial) :
    FoldWork31Accepted
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
        (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
          trial.val (exactPlainRomCursor configuration sample.1).erase)
        sample.2).2.1 := by
  rw [exact_clean_preQ16_onefold_coordinate_eq_accepted witness]
  have foldCoordinate :
      (exactAcceptedFoldBidirectionalCoordinates witness.input
        witness.fold).2.1 = witness.fold.answer :=
    exact_accepted_fold_work_is_probability_coordinate programmedCover
      witness.input witness.fold
  rw [foldCoordinate]
  exact witness.fold.accepted

#print axioms exact_clean_preQ16_onefold_router_exact
#print axioms exact_clean_preQ16_onefold_coordinate_eq_accepted
#print axioms exact_clean_preQ16_onefold_alpha_succeeds
#print axioms exact_clean_preQ16_onefold_work_accepted

end

end AspisK1.V7Tag73ExactCleanBidirectionalFoldOneFoldComponents
