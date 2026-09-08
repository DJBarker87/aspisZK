import AspisFormal.K1.V7Tag73ExactBidirectionalFoldOneFoldTrialEvent

/-!
# Exact replay across one bidirectional fold/alpha fibre

Two tapes in the same hidden/trial fibre may differ in the four alpha output
blocks.  If their residual and fold-work coordinate agree, rebuilding the
left residual with the right alpha blocks is definitionally the right master
tape.  This is the deterministic coupling needed before any probability
argument.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactBidirectionalFoldOneFoldFibreReplay

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldReplay
open AspisK1.V7Tag73ExactBidirectionalFoldOneFoldTrialEvent
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisK1.V7Tag73VariablePrefixGammaFlatRouting
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Coordinate inversion with the right alpha block vector and common
left/right residual and fold answer returns the right tape exactly. -/
theorem exactBidirectionalFoldOneFoldTape_cross
    (parameters : ExactCompilerResourceParameters)
    (router : ExactCompilerCausalBidirectionalFoldOneFoldRouter parameters)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (residualExact :
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        left).1 =
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        right).1)
    (foldExact :
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        left).2.1 =
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
        right).2.1) :
    exactBidirectionalFoldOneFoldTape parameters router
        (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          left).1
        ((exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
          router left).2.1,
          (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
            router right).2.2) = right := by
  rw [residualExact, foldExact]
  exact exactBidirectionalFoldOneFoldTape_of_actual parameters router right

/-- Replaying the left accepted family at the right accepted raw alpha returns
the right literal production scheduler run. -/
theorem exactBidirectionalFoldOneFoldRawReplay_cross
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : AspisPool.AlgorithmicCircleDecoderV7.ExactDecoderInstantiation
      QM31Exact}
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
        right).2.1) :
    exactBidirectionalFoldOneFoldRawReplay transitionFuel configuration hidden
        (exactAcceptedFoldBidirectionalRouter leftWitness.input leftWitness.fold)
        (exactAcceptedFoldBidirectionalCoordinates leftWitness.input
          leftWitness.fold).1
        (exactAcceptedFoldBidirectionalCoordinates leftWitness.input
          leftWitness.fold).2.1
        (exactAcceptedFoldCoordinateRaw transitionRoom programmedCover
          rightWitness.input rightWitness.fold) =
      runExactPlainRom transitionFuel configuration (hidden, right) := by
  let router := exactCompilerBidirectionalFoldOneFoldRouter parameters
    transitionFuel trial.val (exactPlainRomCursor configuration hidden).erase
  have leftRouter := leftWitness.routerExact
  have rightRouter := rightWitness.routerExact
  have tapeExact := exactBidirectionalFoldOneFoldTape_cross parameters router
    left right residualExact foldExact
  have rightRaw :
      (fourGammaBlocksRawEquiv).symm
          (exactAcceptedFoldCoordinateRaw transitionRoom programmedCover
            rightWitness.input rightWitness.fold).1 =
        (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters router
          right).2.2 := by
    unfold exactAcceptedFoldCoordinateRaw
    rw [fourGammaBlocksRawEquiv.symm_apply_apply]
    unfold exactAcceptedFoldBidirectionalCoordinates
    rw [rightRouter]
  unfold exactBidirectionalFoldOneFoldRawReplay
  congr 1
  apply Prod.ext
  · rfl
  · rw [leftRouter]
    unfold exactAcceptedFoldBidirectionalCoordinates
    rw [leftRouter, rightRaw]
    exact tapeExact

end

#print axioms exactBidirectionalFoldOneFoldTape_cross
#print axioms exactBidirectionalFoldOneFoldRawReplay_cross

end AspisK1.V7Tag73ExactBidirectionalFoldOneFoldFibreReplay
