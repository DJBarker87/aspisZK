import AspisFormal.K1.V7Tag73ExactFoldArmedAlphaChainDisposition
import AspisFormal.K1.V7Tag73ExactPairAlphaHybridEquality
import AspisFormal.K1.V7Tag73K13CorrectedAlphaGammaClosure

/-!
# Corrected K1.3 alpha pair equality

The exact fold-armed disposition traces now classify every consumed alpha
output.  This leaf compares two traces at equal non-q16 coordinates.  Shared
prefix records use first-input uniqueness; post-fold records use the common
named coordinate.  The result is equality of the full decoded alpha input,
without an adversary-anchor or retrospective role classifier.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13CorrectedAlphaPairEquality

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactFoldArmedAlphaChainDisposition
open AspisK1.V7Tag73ExactPairAlphaHybridEquality
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73K13CorrectedAlphaGammaClosure
open AspisK1.V7Tag73K13CorrectedPairTrialProbability
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Two disposition traces with the same state/advance chain and equal alpha
coordinate tapes have byte-identical output lists. -/
theorem exact_pair_fold_alpha_output_dispositions_eq
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftInput : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance (hidden, left))
    (rightInput : ExactK12OperationalInput transitionFuel configuration
      projection fixedInstance (hidden, right))
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (leftFold : ExactAcceptedFoldTrial leftInput)
    (rightFold : ExactAcceptedFoldTrial rightInput)
    (leftTrialExact : leftFold.trial = foldTrial)
    (rightTrialExact : rightFold.trial = foldTrial)
    (leftCommon rightCommon : List UnifiedExposureRecord)
    (commonExact : leftCommon = rightCommon)
    (leftFoldMember : ∀ record, record ∈ leftFold.prior →
      record ∈ leftCommon)
    (rightFoldMember : ∀ record, record ∈ rightFold.prior →
      record ∈ rightCommon)
    (leftCommonRoot : ∀ record, record ∈ leftCommon →
      record ∈ exactFixedRootRecords leftInput.package.root)
    (rightCommonRoot : ∀ record, record ∈ rightCommon →
      record ∈ exactFixedRootRecords rightInput.package.root)
    (contextExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1) :
    ∀ {offset : Nat} {leftState rightState : Digest256}
      {leftOutputs leftAdvances rightOutputs rightAdvances : List Digest256}
      (leftTrace : ExactFoldAlphaOutputDispositions leftInput leftFold
        finalTrial offset leftState leftOutputs leftAdvances)
      (rightTrace : ExactFoldAlphaOutputDispositions rightInput rightFold
        finalTrial offset rightState rightOutputs rightAdvances)
      (stateExact : leftState = rightState)
      (advancesExact : leftAdvances = rightAdvances),
      leftOutputs = rightOutputs := by
  intro offset leftState rightState leftOutputs leftAdvances rightOutputs
    rightAdvances leftTrace
  induction leftTrace generalizing rightState rightOutputs rightAdvances with
  | done offset state =>
      intro rightTrace stateExact advancesExact
      cases rightTrace with
      | done => rfl
      | next blockBound outputLookup disposition tail =>
          simp at advancesExact
  | @next offset state leftOutput leftAdvanced leftOutputs leftAdvances
      leftBlockBound leftLookup leftDisposition leftTail ih =>
      intro rightTrace stateExact advancesExact
      cases rightTrace with
      | done => simp at advancesExact
      | @next _ rightState rightOutput rightAdvanced rightOutputs rightAdvances
          rightBlockBound rightLookup rightDisposition rightTail =>
          subst rightState
          have advancedExact : leftAdvanced = rightAdvanced :=
            (List.cons.inj advancesExact).1
          have tailAdvancesExact : leftAdvances = rightAdvances :=
            (List.cons.inj advancesExact).2
          subst rightAdvanced
          let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
            transitionFuel foldTrial.val finalTrial.val
            (exactPlainRomCursor configuration hidden).erase
          have leftDisposition' :
              (∃ actor,
                (.machineFresh actor (gammaOutputInput state) leftOutput :
                  UnifiedExposureRecord) ∈ leftFold.prior) ∨
              causalRoutedAnswer? (some (Sum.inl
                (⟨offset, leftBlockBound⟩ : Fin 4))) router
                (foldAlphaFinalWorkQ16NamedSlotInputTape
                  (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters
                    left)) = some leftOutput := by
            rw [leftTrialExact] at leftDisposition
            exact leftDisposition
          have rightDisposition' :
              (∃ actor,
                (.machineFresh actor (gammaOutputInput state) rightOutput :
                  UnifiedExposureRecord) ∈ rightFold.prior) ∨
              causalRoutedAnswer? (some (Sum.inl
                (⟨offset, leftBlockBound⟩ : Fin 4))) router
                (foldAlphaFinalWorkQ16NamedSlotInputTape
                  (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters
                    right)) = some rightOutput := by
            have blockExact : (⟨offset, rightBlockBound⟩ : Fin 4) =
                ⟨offset, leftBlockBound⟩ := by
              apply Fin.ext
              rfl
            rw [rightTrialExact, blockExact] at rightDisposition
            exact rightDisposition
          have alphaCoordinateExact :
              (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
                  router left).1.2 (⟨offset, leftBlockBound⟩ : Fin 4) =
                (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters
                  router right).1.2 (⟨offset, leftBlockBound⟩ : Fin 4) := by
            exact congrFun (congrArg Prod.snd contextExact)
              ⟨offset, leftBlockBound⟩
          have leftDispositionCommon :
              (∃ actor,
                (.machineFresh actor (gammaOutputInput state) leftOutput :
                  UnifiedExposureRecord) ∈ leftCommon) ∨
              causalRoutedAnswer? (some (Sum.inl
                (⟨offset, leftBlockBound⟩ : Fin 4))) router
                (foldAlphaFinalWorkQ16NamedSlotInputTape
                  (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters
                    left)) = some leftOutput := by
            rcases leftDisposition' with cached | routed
            · left
              obtain ⟨actor, member⟩ := cached
              exact ⟨actor, leftFoldMember _ member⟩
            · exact Or.inr routed
          have rightDispositionCommon :
              (∃ actor,
                (.machineFresh actor (gammaOutputInput state) rightOutput :
                  UnifiedExposureRecord) ∈ rightCommon) ∨
              causalRoutedAnswer? (some (Sum.inl
                (⟨offset, leftBlockBound⟩ : Fin 4))) router
                (foldAlphaFinalWorkQ16NamedSlotInputTape
                  (exactCompilerFoldAlphaFinalWorkQ16InputTape parameters
                    right)) = some rightOutput := by
            rcases rightDisposition' with cached | routed
            · left
              obtain ⟨actor, member⟩ := cached
              exact ⟨actor, rightFoldMember _ member⟩
            · exact Or.inr routed
          have headExact := exact_pair_alpha_answer_eq_of_cached_or_routed
            leftInput rightInput router leftCommon rightCommon
              ⟨offset, leftBlockBound⟩ (gammaOutputInput state) leftOutput
              rightOutput leftLookup rightLookup commonExact leftCommonRoot
              rightCommonRoot leftDispositionCommon rightDispositionCommon
              alphaCoordinateExact
          have tailExact := ih rightTail rfl tailAdvancesExact
          rw [headExact, tailExact]

/-- Complete corrected K1.3 alpha equality on the equal-fold-prefix branch.
The exact accepted fold package supplies both the literal source chain and the
deployed decoder inputs; no independently selected alpha witness appears. -/
theorem exact_preQ16_clean_pair_alpha_zero_eq_of_fold_priors_eq
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {decoder : ExactDecoderInstantiation QM31Exact}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 518 ≤ 2 * parameters.forkRequestCap)
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (hidden : HiddenTape)
    (left right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (leftWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, left) foldTrial
        finalTrial)
    (rightWitness : ExactPreQ16CleanK13PairTrialWitness transitionFuel
      configuration projection fixedInstance decoder (hidden, right) foldTrial
        finalTrial)
    (jointPriorExact : leftWitness.joint.prior = rightWitness.joint.prior)
    (foldPriorExact :
      (exactAcceptedFoldTrial leftWitness.joint.input).prior =
        (exactAcceptedFoldTrial rightWitness.joint.input).prior)
    (contextExact :
      let router := exactCompilerFoldArmedAlphaFinalWorkQ16Router parameters
        transitionFuel foldTrial.val finalTrial.val
        (exactPlainRomCursor configuration hidden).erase
      (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          left).1 =
        (exactCompilerCausalFoldAlphaFinalWorkQ16Coordinates parameters router
          right).1) :
    exactOperationalChallenge leftWitness.joint.input (.alpha 0) =
      exactOperationalChallenge rightWitness.joint.input (.alpha 0) := by
  let leftFold := exactAcceptedFoldTrial leftWitness.joint.input
  let rightFold := exactAcceptedFoldTrial rightWitness.joint.input
  obtain ⟨initialExact, advancesExact, lengthsExact, _pointwise⟩ :=
    exact_preQ16_clean_pair_accepted_fold_alpha_advance_states_eq
      transitionRoom foldTrial finalTrial hidden left right leftWitness
        rightWitness jointPriorExact
  have leftTrace := exact_accepted_fold_alpha_output_dispositions
    transitionRoom programmedCover leftWitness.joint.input leftFold finalTrial
  have rightTrace := exact_accepted_fold_alpha_output_dispositions
    transitionRoom programmedCover rightWitness.joint.input rightFold finalTrial
  have outputsExact : leftFold.alphaOutputs = rightFold.alphaOutputs :=
    exact_pair_fold_alpha_output_dispositions_eq hidden left right
      leftWitness.joint.input rightWitness.joint.input foldTrial finalTrial
      leftFold rightFold leftWitness.foldExact rightWitness.foldExact
      leftFold.prior rightFold.prior foldPriorExact
      (fun _ member => member) (fun _ member => member)
      (by
        intro record member
        rw [leftFold.rootDecomposition]
        exact List.mem_append_left _ member)
      (by
        intro record member
        rw [rightFold.rootDecomposition]
        exact List.mem_append_left _ member)
      contextExact leftTrace rightTrace initialExact advancesExact
  have pointwise : ∀ index (leftBound : index < leftFold.alphaOutputs.length),
      let rightBound : index < rightFold.alphaOutputs.length := by
        simpa only [outputsExact] using leftBound
      leftFold.alphaOutputs[index] = rightFold.alphaOutputs[index] := by
    intro index leftBound
    simpa [outputsExact]
  exact exact_operational_alpha_zero_eq_of_pointwise_outputs
    leftWitness.joint.input rightWitness.joint.input leftFold.alphaOutputs
      rightFold.alphaOutputs
      ((exactOperationalTape leftWitness.joint.input).messages.challengeValue
        (.alpha 0))
      ((exactOperationalTape rightWitness.joint.input).messages.challengeValue
        (.alpha 0))
      leftFold.alphaExactValue rightFold.alphaExactValue lengthsExact pointwise
      leftFold.alphaAccepted rightFold.alphaAccepted leftFold.alphaExactDecode
      rightFold.alphaExactDecode (by
        simpa [exactOperationalChallenge] using leftFold.alphaOperational)
      (by simpa [exactOperationalChallenge] using rightFold.alphaOperational)

#print axioms exact_pair_fold_alpha_output_dispositions_eq
#print axioms exact_preQ16_clean_pair_alpha_zero_eq_of_fold_priors_eq

end

end AspisK1.V7Tag73K13CorrectedAlphaPairEquality
