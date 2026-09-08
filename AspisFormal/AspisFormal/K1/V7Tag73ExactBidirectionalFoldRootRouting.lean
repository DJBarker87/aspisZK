import AspisFormal.K1.V7Tag73BidirectionalFoldAlphaOneShot
import AspisFormal.K1.V7Tag73ExactBidirectionalFoldAnchor
import AspisFormal.K1.V7Tag73ExactCausalRouterTapeAlignment
import AspisFormal.K1.V7Tag73ExactCandidateLabeledRootRouting
import AspisFormal.K1.V7Tag73ExactFinalWorkPairControllerCompletion

/-!
# Exact root routing for the bidirectional fold/alpha controller

This module connects the controller's answer-independent five-slot inventory
to the literal exact root and compiler tape.  It deliberately remains generic
about which source record receives which slot; later source lemmas only need
to establish the pre-answer `preferredSlot` fact for their selected record.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactBidirectionalFoldRootRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73BidirectionalFoldAlphaController
open AspisK1.V7Tag73BidirectionalFoldAlphaOneShot
open AspisK1.V7Tag73BidirectionalFoldAlphaPrefix
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactBidirectionalFoldAnchor
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerSourceAnchoredCut
open AspisK1.V7Tag73ExactCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactCausalRouterTapeAlignment
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPlainRomTraceResourceCaps
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def exactBidirectionalFoldController
    {parameters : ExactCompilerResourceParameters}
    (transitionFuel : Nat) (trial : ExactCompilerExposureTrial parameters) :=
  bidirectionalFoldAlphaController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel trial.val

def exactBidirectionalFoldInitialState
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (_input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :=
  bidirectionalFoldAlphaInitialState
    (exactPlainRomCursor configuration sample.1).erase

def exactBidirectionalFoldRootLabels
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
    (trial : ExactCompilerExposureTrial parameters) :
    List (Option FoldOneFoldDigestSlot × Digest256) :=
  indexedControllerLabeledRecords transitionFuel
    (exactBidirectionalFoldController transitionFuel trial)
    (exactBidirectionalFoldInitialState input)
    (exactFixedRootRecords input.package.root)

/-- The master tape cast to the controller's five named destinations plus
residual.  This is a length proof only and preserves chronological values. -/
def bidirectionalFoldNamedSlotInputTape
    (parameters : ExactCompilerResourceParameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    FreshAnswerTape Digest256
      ((Finset.univ : Finset FoldOneFoldDigestSlot).card +
        ((exactCompilerTargetCaps parameters).length - 5)) :=
  castFreshAnswerTape (by
    rw [Finset.card_univ, fold_onefold_digest_slot_card]
    exact (Nat.add_sub_of_le
      (exact_compiler_tape_has_bidirectional_fold_onefold_capacity
        parameters)).symm) tape

theorem bidirectional_fold_named_slot_input_tape_preserves_list
    (parameters : ExactCompilerResourceParameters)
    (tape : FreshAnswerTape Digest256
      (exactCompilerTargetCaps parameters).length) :
    freshAnswerTapeToList
        (bidirectionalFoldNamedSlotInputTape parameters tape) =
      freshAnswerTapeToList tape := by
  unfold bidirectionalFoldNamedSlotInputTape
  rw [fresh_answer_tape_to_list_cast]

theorem exact_bidirectional_fold_root_labels_form_trace
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
    (trial : ExactCompilerExposureTrial parameters) :
    MachineLabeledTrace
      ((exactBidirectionalFoldController transitionFuel trial).machine
        transitionFuel)
      (exactBidirectionalFoldInitialState input)
      (exactBidirectionalFoldRootLabels input trial)
      (indexedStateAfterRecords transitionFuel
        (exactBidirectionalFoldController transitionFuel trial)
        (exactFixedRootRecords input.package.root)
        (exactBidirectionalFoldInitialState input)) := by
  exact indexed_controller_labeled_records_form_trace transitionFuel
    (exactBidirectionalFoldController transitionFuel trial)
    (exactBidirectionalFoldInitialState input)
    (exactFixedRootRecords input.package.root)

theorem exact_bidirectional_fold_root_named_slots_nodup
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
    (trial : ExactCompilerExposureTrial parameters) :
    (namedTraceSlots (exactBidirectionalFoldRootLabels input trial)).Nodup := by
  exact bidirectional_labeled_records_named_slots_nodup transitionFuel trial.val
    (exactFixedRootRecords input.package.root)
    (exactBidirectionalFoldInitialState input)

theorem exact_bidirectional_fold_root_labels_tape_prefix
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
    (trial : ExactCompilerExposureTrial parameters) :
    freshAnswerTapeToList
        (bidirectionalFoldNamedSlotInputTape parameters sample.2) =
      (exactBidirectionalFoldRootLabels input trial).map Prod.snd ++
        input.package.root.full.projection.rootPrefixes.verifier.remaining := by
  unfold exactBidirectionalFoldRootLabels
  rw [bidirectional_fold_named_slot_input_tape_preserves_list,
    indexed_controller_labeled_records_answers,
    exact_fixed_root_records_map_answer]
  exact (exactCompilerInitialGammaCursorAlignment input).answersExact

theorem exact_bidirectional_fold_root_residual_enough_of_programmed_cover
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
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap) :
    residualTraceSteps (exactBidirectionalFoldRootLabels input trial) ≤
      (exactCompilerTargetCaps parameters).length - 5 := by
  let rootRecords := exactFixedRootRecords input.package.root
  let labels := exactBidirectionalFoldRootLabels input trial
  have labelsLength : labels.length = rootRecords.length := by
    have answers := congrArg List.length
      (indexed_controller_labeled_records_answers transitionFuel
        (exactBidirectionalFoldController transitionFuel trial)
        (exactBidirectionalFoldInitialState input) rootRecords)
    simpa [labels, exactBidirectionalFoldRootLabels, rootRecords] using answers
  have residualLeLabels : residualTraceSteps labels ≤ labels.length := by
    have split := labeled_trace_length_split labels
    omega
  have projectedLength (actor : QueryActor) :
      ∀ queries : List (ShaInput × Digest256),
        (projectedMachineFreshRecords actor queries).length = queries.length := by
    intro queries
    induction queries with
    | nil => rfl
    | cons query queries ih =>
        rcases query with ⟨queryInput, answer⟩
        simp [projectedMachineFreshRecords, ih]
  have rootCountExact : rootRecords.length =
      machineFreshCoordinateCount rootRecords := by
    unfold rootRecords exactFixedRootRecords fullProjectedRootRecords
    simp [projectedLength]
  have rootMachineLe : machineFreshCoordinateCount rootRecords ≤
      machineFreshCoordinateCount
        (runExactPlainRom transitionFuel configuration sample).trace := by
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    unfold exactFixedOperationalStateMapTrace
    simp [rootRecords]
  have rootLengthLe : rootRecords.length ≤
      full256MachineFreshCap parameters := by
    rw [rootCountExact]
    exact rootMachineLe.trans input.package.root.traceCaps.1
  have fullCapLe : full256MachineFreshCap parameters ≤
      (exactCompilerTargetCaps parameters).length - 5 := by
    rw [exact_compiler_target_caps_length]
    unfold unifiedFull256ExposureCap sameTapeStartCap
    omega
  exact residualLeLabels.trans
    (labelsLength.le.trans (rootLengthLe.trans fullCapLe))

private theorem route_selected_root_answer_core
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
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (target : FoldOneFoldDigestSlot)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (residualEnough :
      residualTraceSteps (exactBidirectionalFoldRootLabels input trial) ≤
        (exactCompilerTargetCaps parameters).length - 5)
    (preferred :
      (exactBidirectionalFoldController transitionFuel trial).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (exactBidirectionalFoldController transitionFuel trial) prior
          (exactBidirectionalFoldInitialState input)) = some target) :
    causalRoutedAnswer? target
        (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
          trial.val (exactPlainRomCursor configuration sample.1).erase)
        (bidirectionalFoldNamedSlotInputTape parameters sample.2) =
      some answer := by
  let controller := exactBidirectionalFoldController transitionFuel trial
  let initial := exactBidirectionalFoldInitialState input
  let priorLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let laterLabels := indexedControllerLabeledRecords transitionFuel controller
    (controller.afterAnswer transitionFuel reached answer) later
  have labelsDecomposition : exactBidirectionalFoldRootLabels input trial =
      priorLabels ++ (some target, answer) :: laterLabels := by
    unfold exactBidirectionalFoldRootLabels
    rw [decomposition, indexed_controller_labeled_records_append]
    simpa only [indexedControllerLabeledRecords,
      UnifiedExposureRecord.answer, controller, initial, reached,
      laterLabels, priorLabels, preferred]
  exact machine_labeled_trace_routes_named_answer
    (exact_bidirectional_fold_root_labels_form_trace input trial)
    (exact_bidirectional_fold_root_named_slots_nodup input trial)
    (fun slot _member => Finset.mem_univ slot) residualEnough
    (bidirectionalFoldNamedSlotInputTape parameters sample.2)
    input.package.root.full.projection.rootPrefixes.verifier.remaining
    (exact_bidirectional_fold_root_labels_tape_prefix input trial)
    priorLabels laterLabels target answer labelsDecomposition

/-- An aligned machine-only segment that avoids an armed work input preserves
the boundary-first waiting state. -/
theorem aligned_machine_records_preserve_bidirectional_waiting
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (workInput : ShaInput) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        BidirectionalFoldAlphaMemory),
      IndexedRecordsAligned transitionFuel
        (bidirectionalFoldAlphaController transitionFuel anchorIndex)
        state records →
      OnlyMachineFreshRecords records →
      (∀ record ∈ records, causalInput? record ≠ some workInput) →
      anchorIndex < state.exposureIndex →
      BidirectionalWaitingForWork state.memory workInput →
      BidirectionalWaitingForWork
        (indexedStateAfterRecords transitionFuel
          (bidirectionalFoldAlphaController transitionFuel anchorIndex)
          records state).memory workInput := by
  intro records
  induction records with
  | nil =>
      intro state _aligned _onlyMachine _avoids _afterAnchor waiting
      simpa only [indexed_state_after_records_nil] using waiting
  | cons record records ih =>
      intro state aligned onlyMachine avoids afterAnchor waiting
      obtain ⟨actor, queryInput, answer, recordExact⟩ :=
        onlyMachine record (List.mem_cons_self)
      subst record
      have headAligned := aligned []
        (.machineFresh actor queryInput answer) records rfl
      have inputExact : currentBidirectionalInput? transitionFuel state =
          some queryInput := by
        exact aligned_machine_record_has_exact_input transitionFuel state.cursor
          actor queryInput answer headAligned
      have queryNe : queryInput ≠ workInput := by
        intro equal
        apply avoids (.machineFresh actor queryInput answer)
          List.mem_cons_self
        simp [causalInput?, equal]
      have inputAvoids : currentBidirectionalInput? transitionFuel state ≠
          some workInput := by
        rw [inputExact]
        exact fun equal => queryNe (Option.some.inj equal)
      let controller := bidirectionalFoldAlphaController
        (globalOracleCalls := globalOracleCalls) transitionFuel anchorIndex
      let next := controller.afterAnswer transitionFuel state answer
      have nextWaiting : BidirectionalWaitingForWork next.memory workInput := by
        simpa [next, controller, bidirectionalFoldAlphaController,
          IndexedUnifiedExposureController.afterAnswer] using
          bidirectional_waiting_for_work_step transitionFuel anchorIndex state
            answer workInput (Nat.ne_of_lt afterAnchor).symm inputAvoids waiting
      have tailAligned : IndexedRecordsAligned transitionFuel controller next
          records := by
        apply indexed_records_aligned_segment transitionFuel controller state
          ((.machineFresh actor queryInput answer) :: records)
          [(.machineFresh actor queryInput answer)] records [] aligned
        simp
      have tailOnly : OnlyMachineFreshRecords records := by
        intro tailRecord member
        exact onlyMachine tailRecord (List.mem_cons_of_mem _ member)
      have tailAvoids : ∀ tailRecord ∈ records,
          causalInput? tailRecord ≠ some workInput := by
        intro tailRecord member
        exact avoids tailRecord (List.mem_cons_of_mem _ member)
      have nextAfterAnchor : anchorIndex < next.exposureIndex := by
        simp only [next, indexed_after_answer_exposure_index]
        omega
      rw [indexed_state_after_records_cons]
      exact ih next tailAligned tailOnly tailAvoids nextAfterAnchor nextWaiting

/-- The selected fold-work answer occupies the distinguished fold slot in
both literal source orders: work before boundary and adversary-first boundary
before work. -/
theorem exact_accepted_fold_work_is_bidirectionally_routed
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input) :
    let trial := exactAcceptedFoldPairTrial input fold
    causalRoutedAnswer? none
        (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
          trial.val (exactPlainRomCursor configuration sample.1).erase)
        (bidirectionalFoldNamedSlotInputTape parameters sample.2) =
      some fold.answer := by
  let trial := exactAcceptedFoldPairTrial input fold
  let controller := exactBidirectionalFoldController transitionFuel trial
  let initial := exactBidirectionalFoldInitialState input
  let root := exactFixedRootRecords input.package.root
  let workInput := selectedFoldWorkInput input fold
  let boundaryInput := selectedFoldBoundaryInput input fold
  let workRecord : UnifiedExposureRecord :=
    .machineFresh fold.actor workInput fold.answer
  have aligned : IndexedRecordsAligned transitionFuel controller initial root := by
    simpa [controller, exactBidirectionalFoldController, initial,
      exactBidirectionalFoldInitialState, root] using
      exact_root_records_aligned_for_bidirectional_fold_controller input trial
  have residualEnough :
      residualTraceSteps (exactBidirectionalFoldRootLabels input trial) ≤
        (exactCompilerTargetCaps parameters).length - 5 :=
    exact_bidirectional_fold_root_residual_enough_of_programmed_cover
      input trial programmedCover
  have pair := exactAcceptedFoldPairTrial_labeled input fold
  rcases pair with workFirst | boundaryFirst
  · obtain ⟨prior, middle, later, boundaryActor, decomposition, anchorExact⟩ :=
      workFirst
    change trial.val = prior.length at anchorExact
    let reached := indexedStateAfterRecords transitionFuel controller prior initial
    have reachedIndex : reached.exposureIndex = trial.val := by
      rw [show reached.exposureIndex = initial.exposureIndex + prior.length by
        exact indexed_state_after_records_exposure_index transitionFuel
          controller prior initial]
      simp [initial, exactBidirectionalFoldInitialState,
        bidirectionalFoldAlphaInitialState, anchorExact]
    have preInvariant : BidirectionalPreAnchorInvariant reached.memory := by
      apply bidirectional_pre_anchor_invariant_replay transitionFuel trial.val
        prior initial inactive_bidirectional_pre_anchor
      simp [initial, exactBidirectionalFoldInitialState,
        bidirectionalFoldAlphaInitialState, anchorExact]
    have selectedAligned := aligned prior workRecord
      (middle ++
        (.machineFresh boundaryActor boundaryInput fold.boundaryAnswer :
          UnifiedExposureRecord) :: later) (by
            simpa [root, workRecord, workInput, boundaryInput,
              List.append_assoc] using decomposition)
    have inputExact : currentBidirectionalInput? transitionFuel reached =
        some workInput := by
      simpa [currentBidirectionalInput?, reached, workRecord] using
        aligned_machine_record_has_exact_input transitionFuel reached.cursor
          fold.actor workInput fold.answer selectedAligned
    have preferred : controller.preferredSlot reached = some none := by
      simpa [controller, exactBidirectionalFoldController, workInput,
        selectedFoldWorkInput] using
        bidirectional_preferred_at_literal_work_anchor transitionFuel trial.val
          reached fold.digest
          (exactOperationalTape input).messages.foldGrinding.selected
          reachedIndex preInvariant.1 (by
            simpa [workInput, selectedFoldWorkInput] using inputExact)
    apply route_selected_root_answer_core
      input trial prior
        (middle ++
          (.machineFresh boundaryActor boundaryInput fold.boundaryAnswer :
            UnifiedExposureRecord) :: later)
        fold.actor workInput fold.answer none
    · simpa [root, workRecord, workInput, boundaryInput,
        List.append_assoc] using decomposition
    · exact residualEnough
    · simpa [reached] using preferred
  · obtain ⟨prior, middle, later, boundaryActor, decomposition, anchorExact⟩ :=
      boundaryFirst
    change trial.val = prior.length at anchorExact
    let boundaryRecord : UnifiedExposureRecord :=
      .machineFresh boundaryActor boundaryInput fold.boundaryAnswer
    let reachedBoundary := indexedStateAfterRecords transitionFuel controller
      prior initial
    let afterBoundary := controller.afterAnswer transitionFuel reachedBoundary
      fold.boundaryAnswer
    have reachedBoundaryIndex : reachedBoundary.exposureIndex = trial.val := by
      rw [show reachedBoundary.exposureIndex =
          initial.exposureIndex + prior.length by
        exact indexed_state_after_records_exposure_index transitionFuel
          controller prior initial]
      simp [initial, exactBidirectionalFoldInitialState,
        bidirectionalFoldAlphaInitialState, anchorExact]
    have preInvariant :
        BidirectionalPreAnchorInvariant reachedBoundary.memory := by
      apply bidirectional_pre_anchor_invariant_replay transitionFuel trial.val
        prior initial inactive_bidirectional_pre_anchor
      simp [initial, exactBidirectionalFoldInitialState,
        bidirectionalFoldAlphaInitialState, anchorExact]
    have boundaryAligned := aligned prior boundaryRecord
      (middle ++ workRecord :: later) (by
        simpa [root, boundaryRecord, boundaryInput, workRecord, workInput,
          List.append_assoc] using decomposition)
    have boundaryInputExact :
        currentBidirectionalInput? transitionFuel reachedBoundary =
          some boundaryInput := by
      simpa [currentBidirectionalInput?, reachedBoundary, boundaryRecord] using
        aligned_machine_record_has_exact_input transitionFuel
          reachedBoundary.cursor boundaryActor boundaryInput fold.boundaryAnswer
          boundaryAligned
    have waitingAfter : BidirectionalWaitingForWork afterBoundary.memory
        workInput := by
      have installed := bidirectional_boundary_anchor_waits_for_work
        transitionFuel trial.val reachedBoundary fold.digest
          (exactOperationalTape input).messages.foldGrinding.selected
          fold.boundaryAnswer reachedBoundaryIndex preInvariant.1 (by
            simpa [boundaryInput, selectedFoldBoundaryInput] using
              boundaryInputExact)
      change BidirectionalWaitingForWork
        (bidirectionalFoldAlphaAfterMemory transitionFuel trial.val
          reachedBoundary fold.boundaryAnswer) workInput
      simpa [BidirectionalWaitingForWork, workInput,
        selectedFoldWorkInput] using installed
    have middleAligned : IndexedRecordsAligned transitionFuel controller
        afterBoundary middle := by
      have segment := indexed_records_aligned_segment transitionFuel controller
        initial root (prior ++ [boundaryRecord]) middle (workRecord :: later)
        aligned (by
          simpa [root, boundaryRecord, boundaryInput, workRecord, workInput,
            List.append_assoc] using decomposition)
      simpa [afterBoundary, reachedBoundary, boundaryRecord,
        UnifiedExposureRecord.answer,
        indexed_state_after_records_append] using segment
    have middleOnly : OnlyMachineFreshRecords middle := by
      apply only_machine_fresh_records_segment root
        (prior ++ [boundaryRecord]) middle (workRecord :: later)
      · simpa [root] using exact_root_records_only_machine_fresh input
      · simpa [root, boundaryRecord, boundaryInput, workRecord, workInput,
          List.append_assoc] using decomposition
    have middleAvoids : ∀ record ∈ middle,
        causalInput? record ≠ some workInput := by
      have avoids := strict_record_middle_avoids_second_input root prior middle
        later boundaryRecord workRecord
        (by simpa [root] using exact_root_record_causal_inputs_nodup input)
        (by simpa [root, boundaryRecord, boundaryInput, workRecord, workInput,
          List.append_assoc] using decomposition)
      intro record member
      simpa [workRecord, causalInput?] using avoids record member
    have afterBoundaryIndex : trial.val < afterBoundary.exposureIndex := by
      simp [afterBoundary, reachedBoundaryIndex]
    let reachedWork := indexedStateAfterRecords transitionFuel controller middle
      afterBoundary
    have waitingWork : BidirectionalWaitingForWork reachedWork.memory
        workInput := by
      exact aligned_machine_records_preserve_bidirectional_waiting
        transitionFuel trial.val workInput middle afterBoundary middleAligned
          middleOnly middleAvoids afterBoundaryIndex waitingAfter
    have workAligned := aligned (prior ++ boundaryRecord :: middle) workRecord
      later (by
        simpa [root, boundaryRecord, boundaryInput, workRecord, workInput,
          List.append_assoc] using decomposition)
    have prefixStateExact :
        indexedStateAfterRecords transitionFuel controller
            (prior ++ boundaryRecord :: middle) initial = reachedWork := by
      simp [reachedWork, afterBoundary, reachedBoundary, boundaryRecord,
        UnifiedExposureRecord.answer, indexed_state_after_records_append]
    have workInputExact : currentBidirectionalInput? transitionFuel reachedWork =
        some workInput := by
      have literal := aligned_machine_record_has_exact_input transitionFuel
        (indexedStateAfterRecords transitionFuel controller
          (prior ++ boundaryRecord :: middle) initial).cursor
        fold.actor workInput fold.answer workAligned
      simpa [currentBidirectionalInput?, prefixStateExact] using literal
    have workNotAnchor : reachedWork.exposureIndex ≠ trial.val := by
      have indexExact := indexed_state_after_records_exposure_index
        transitionFuel controller middle afterBoundary
      rw [show reachedWork.exposureIndex =
          afterBoundary.exposureIndex + middle.length by
        exact indexExact]
      omega
    have preferred : controller.preferredSlot reachedWork = some none := by
      simpa [controller, exactBidirectionalFoldController] using
        bidirectional_preferred_at_expected_work transitionFuel trial.val
          reachedWork workInput workNotAnchor waitingWork.1 waitingWork.2
          workInputExact
    apply route_selected_root_answer_core
      input trial (prior ++ boundaryRecord :: middle) later fold.actor
        workInput fold.answer none
    · simpa [root, boundaryRecord, boundaryInput, workRecord, workInput,
        List.append_assoc] using decomposition
    · exact residualEnough
    · change controller.preferredSlot
        (indexedStateAfterRecords transitionFuel controller
          (prior ++ boundaryRecord :: middle) initial) = some none
      rw [prefixStateExact]
      exact preferred

/-- Once a literal root record is selected by the controller, the causal
router returns exactly that record's answer from the original compiler tape. -/
theorem exact_bidirectional_fold_router_routes_selected_root_answer
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
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (target : FoldOneFoldDigestSlot)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (residualEnough :
      residualTraceSteps (exactBidirectionalFoldRootLabels input trial) ≤
        (exactCompilerTargetCaps parameters).length - 5)
    (preferred :
      (exactBidirectionalFoldController transitionFuel trial).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (exactBidirectionalFoldController transitionFuel trial) prior
          (exactBidirectionalFoldInitialState input)) = some target) :
    causalRoutedAnswer? target
        (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
          trial.val (exactPlainRomCursor configuration sample.1).erase)
        (bidirectionalFoldNamedSlotInputTape parameters sample.2) =
      some answer := by
  let controller := exactBidirectionalFoldController transitionFuel trial
  let initial := exactBidirectionalFoldInitialState input
  let priorLabels := indexedControllerLabeledRecords transitionFuel controller
    initial prior
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let laterLabels := indexedControllerLabeledRecords transitionFuel controller
    (controller.afterAnswer transitionFuel reached answer) later
  have labelsDecomposition : exactBidirectionalFoldRootLabels input trial =
      priorLabels ++ (some target, answer) :: laterLabels := by
    unfold exactBidirectionalFoldRootLabels
    rw [decomposition, indexed_controller_labeled_records_append]
    simpa only [indexedControllerLabeledRecords,
      UnifiedExposureRecord.answer, controller, initial, reached,
      laterLabels, priorLabels, preferred]
  exact machine_labeled_trace_routes_named_answer
    (exact_bidirectional_fold_root_labels_form_trace input trial)
    (exact_bidirectional_fold_root_named_slots_nodup input trial)
    (fun slot _member => Finset.mem_univ slot) residualEnough
    (bidirectionalFoldNamedSlotInputTape parameters sample.2)
    input.package.root.full.projection.rootPrefixes.verifier.remaining
    (exact_bidirectional_fold_root_labels_tape_prefix input trial)
    priorLabels laterLabels target answer labelsDecomposition

end


#print axioms exact_bidirectional_fold_root_labels_form_trace
#print axioms bidirectional_fold_named_slot_input_tape_preserves_list
#print axioms exact_bidirectional_fold_root_named_slots_nodup
#print axioms exact_bidirectional_fold_root_labels_tape_prefix
#print axioms exact_bidirectional_fold_root_residual_enough_of_programmed_cover
#print axioms aligned_machine_records_preserve_bidirectional_waiting
#print axioms exact_accepted_fold_work_is_bidirectionally_routed
#print axioms exact_bidirectional_fold_router_routes_selected_root_answer

end AspisK1.V7Tag73ExactBidirectionalFoldRootRouting
