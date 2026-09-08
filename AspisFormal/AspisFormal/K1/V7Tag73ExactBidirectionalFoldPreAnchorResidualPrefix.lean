import AspisFormal.K1.V7Tag73CausalResidualCoordinatePrefix
import AspisFormal.K1.V7Tag73ExactBidirectionalFoldRootRouting

/-!
# Exact bidirectional fold pre-anchor residual prefix

Before the selected fold/boundary pair anchor, all controller labels are
residual.  Equality of the bidirectional residual coordinate therefore fixes
the literal master-tape answer prefix before that anchor, without fixing any
alpha output block.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactBidirectionalFoldPreAnchorResidualPrefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73BidirectionalFoldAlphaPrefix
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalResidualCoordinatePrefix
open AspisK1.V7Tag73ExactBidirectionalFoldRootRouting
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- A literal pre-anchor root segment fits in the five-slot router's residual
component. -/
theorem exact_bidirectional_pre_anchor_residual_enough
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (prior later : List UnifiedExposureRecord)
    (rootExact : exactFixedRootRecords input.package.root = prior ++ later)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap) :
    residualTraceSteps
      (indexedControllerLabeledRecords transitionFuel
        (exactBidirectionalFoldController transitionFuel trial)
        (exactBidirectionalFoldInitialState input) prior) ≤
      (exactCompilerTargetCaps parameters).length - 5 := by
  let controller := exactBidirectionalFoldController transitionFuel trial
  let initial := exactBidirectionalFoldInitialState input
  let prefixLabels := indexedControllerLabeledRecords transitionFuel
    controller initial prior
  let suffixLabels := indexedControllerLabeledRecords transitionFuel
    controller (indexedStateAfterRecords transitionFuel controller prior initial)
      later
  have labelsExact : exactBidirectionalFoldRootLabels input trial =
      prefixLabels ++ suffixLabels := by
    unfold exactBidirectionalFoldRootLabels
    rw [rootExact, indexed_controller_labeled_records_append]
  have fullEnough :=
    exact_bidirectional_fold_root_residual_enough_of_programmed_cover input trial
      programmedCover
  rw [labelsExact, residual_trace_steps_append] at fullEnough
  have prefixLe : residualTraceSteps prefixLabels ≤
      residualTraceSteps prefixLabels + residualTraceSteps suffixLabels := by
    omega
  simpa only [prefixLabels, suffixLabels] using prefixLe.trans fullEnough

/-- Equal residual coordinates replay the complete literal answer prefix
strictly before the selected bidirectional pair anchor. -/
theorem exact_bidirectional_residual_coordinate_forces_pre_anchor_tape_prefix
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (prior later : List UnifiedExposureRecord)
    (rootExact : exactFixedRootRecords input.package.root = prior ++ later)
    (trialExact : trial.val = prior.length)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (right : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length)
    (coordinateExact :
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
        (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
          trial.val (exactPlainRomCursor configuration sample.1).erase)
        sample.2).1 =
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
        (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
          trial.val (exactPlainRomCursor configuration sample.1).erase)
        right).1) :
    ∃ rightRemaining,
      freshAnswerTapeToList right =
        prior.map UnifiedExposureRecord.answer ++ rightRemaining := by
  let controller := exactBidirectionalFoldController transitionFuel trial
  let initial := exactBidirectionalFoldInitialState input
  let prefixLabels := indexedControllerLabeledRecords transitionFuel
    controller initial prior
  let suffixLabels := indexedControllerLabeledRecords transitionFuel
    controller (indexedStateAfterRecords transitionFuel controller prior initial)
      later
  have labelsExact : exactBidirectionalFoldRootLabels input trial =
      prefixLabels ++ suffixLabels := by
    unfold exactBidirectionalFoldRootLabels
    rw [rootExact, indexed_controller_labeled_records_append]
  obtain ⟨prefixState, prefixTrace⟩ : ∃ prefixState,
      MachineLabeledTrace (controller.machine transitionFuel) initial
        prefixLabels prefixState := by
    have rootTrace := exact_bidirectional_fold_root_labels_form_trace input trial
    have splitTrace : MachineLabeledTrace (controller.machine transitionFuel)
        initial (prefixLabels ++ suffixLabels)
        (indexedStateAfterRecords transitionFuel controller
          (exactFixedRootRecords input.package.root) initial) := by
      simpa only [controller, initial, labelsExact] using rootTrace
    obtain ⟨middle, prefixTracePart, _suffix⟩ :=
      machine_labeled_trace_append_split prefixLabels suffixLabels splitTrace
    exact ⟨middle, prefixTracePart⟩
  have allResidual : namedTraceSlots prefixLabels = [] := by
    apply bidirectional_labeled_records_before_anchor_all_residual
      transitionFuel trial.val prior initial
    · simp [initial, exactBidirectionalFoldInitialState, trialExact,
        bidirectionalFoldAlphaInitialState]
    · exact inactive_bidirectional_pre_anchor
  have residualEnough : residualTraceSteps prefixLabels ≤
      (exactCompilerTargetCaps parameters).length - 5 := by
    simpa only [controller, initial, prefixLabels] using
      exact_bidirectional_pre_anchor_residual_enough input trial prior later
        rootExact programmedCover
  have leftPrefix : freshAnswerTapeToList
      (bidirectionalFoldNamedSlotInputTape parameters sample.2) =
      prefixLabels.map Prod.snd ++
        (suffixLabels.map Prod.snd ++
          input.package.root.full.projection.rootPrefixes.verifier.remaining) := by
    rw [exact_bidirectional_fold_root_labels_tape_prefix input trial,
      labelsExact, List.map_append, List.append_assoc]
  have leftTraceExact : freshAnswerTapeToList
      (bidirectionalFoldNamedSlotInputTape parameters sample.2) =
      prefixLabels.map Prod.snd ++
        (freshAnswerTapeToList
          (bidirectionalFoldNamedSlotInputTape parameters sample.2)).drop
            prefixLabels.length := by
    rw [leftPrefix]
    have prefixLength : (prefixLabels.map Prod.snd).length =
        prefixLabels.length := by simp
    rw [← prefixLength, List.drop_append_of_le_length (Nat.le_refl _)]
    simp
  have routerCoordinateExact :
      (((controller.machine transitionFuel).fullRouter
        ((exactCompilerTargetCaps parameters).length - 5) initial).coordinateEquiv
          (bidirectionalFoldNamedSlotInputTape parameters sample.2)).2 =
      (((controller.machine transitionFuel).fullRouter
        ((exactCompilerTargetCaps parameters).length - 5) initial).coordinateEquiv
          (bidirectionalFoldNamedSlotInputTape parameters right)).2 := by
    change
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
        (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
          trial.val (exactPlainRomCursor configuration sample.1).erase)
        sample.2).1 =
      (exactCompilerCausalBidirectionalFoldOneFoldCoordinates parameters
        (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
          trial.val (exactPlainRomCursor configuration sample.1).erase)
        right).1 at coordinateExact
    exact coordinateExact
  obtain ⟨rightRemaining, rightPrefix⟩ :=
    all_residual_trace_forces_right_prefix prefixTrace allResidual residualEnough
      (bidirectionalFoldNamedSlotInputTape parameters sample.2)
      (bidirectionalFoldNamedSlotInputTape parameters right) leftTraceExact
      routerCoordinateExact
  have prefixAnswers : prefixLabels.map Prod.snd =
      prior.map UnifiedExposureRecord.answer := by
    exact indexed_controller_labeled_records_answers transitionFuel controller
      initial prior
  rw [prefixAnswers,
    bidirectional_fold_named_slot_input_tape_preserves_list] at rightPrefix
  exact ⟨rightRemaining, rightPrefix⟩

#print axioms exact_bidirectional_pre_anchor_residual_enough
#print axioms
  exact_bidirectional_residual_coordinate_forces_pre_anchor_tape_prefix

end

end AspisK1.V7Tag73ExactBidirectionalFoldPreAnchorResidualPrefix
