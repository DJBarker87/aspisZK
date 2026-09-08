import AspisFormal.K1.V7Tag73BidirectionalFoldAlphaProjection
import AspisFormal.K1.V7Tag73ExactAcceptedFoldAlphaChainOrder
import AspisFormal.K1.V7Tag73ExactAlphaZeroChainRouting
import AspisFormal.K1.V7Tag73ExactBidirectionalFoldRootRouting

/-!
# Exact accepted-source routing of selected-fold alpha outputs

This module transports the standalone alpha-zero labels into the five-slot
bidirectional fold/alpha controller.  The selected work and boundary may be
first-exposed in either order; every consumed alpha output is routed from the
literal accepted root rather than classified by verifier query order.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactBidirectionalFoldAlphaRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73BidirectionalFoldAlphaController
open AspisK1.V7Tag73BidirectionalFoldAlphaProjection
open AspisK1.V7Tag73BidirectionalFoldAlphaPrefix
open AspisK1.V7Tag73BidirectionalFoldOneFoldCoordinates
open AspisK1.V7Tag73CausalSlotRouterLookup
open AspisK1.V7Tag73ExactAcceptedFoldAlphaChainOrder
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactAlphaZeroPrefixCoordinates
open AspisK1.V7Tag73ExactAlphaZeroChainRouting
open AspisK1.V7Tag73ExactAlphaZeroControllerAlignment
open AspisK1.V7Tag73ExactBidirectionalFoldAnchor
open AspisK1.V7Tag73ExactBidirectionalFoldRootRouting
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFoldArmedAlphaSourceAlignment
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootRecordOrderLift
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Replaying the same answer records advances the production cursor
independently of protocol-specific controller memory. -/
theorem indexed_state_after_records_cursor_eq
    {globalOracleCalls : Nat}
    {LeftSlot RightSlot LeftMemory RightMemory : Type}
    (transitionFuel : Nat)
    (leftController : IndexedUnifiedExposureController globalOracleCalls
      Digest256 LeftSlot LeftMemory)
    (rightController : IndexedUnifiedExposureController globalOracleCalls
      Digest256 RightSlot RightMemory) :
    ∀ (records : List UnifiedExposureRecord)
      (left : IndexedUnifiedExposureState globalOracleCalls LeftMemory)
      (right : IndexedUnifiedExposureState globalOracleCalls RightMemory),
      left.cursor = right.cursor →
      (indexedStateAfterRecords transitionFuel leftController records left).cursor =
        (indexedStateAfterRecords transitionFuel rightController records
          right).cursor := by
  intro records
  induction records with
  | nil =>
      intro left right cursorExact
      exact cursorExact
  | cons record records ih =>
      intro left right cursorExact
      rw [indexed_state_after_records_cons, indexed_state_after_records_cons]
      apply ih
      simp [cursorExact]

/-- Any selected-fold boundary decomposition at its literal root ordinal
installs the exact standalone block-zero producer.  Actor identity is retained
only by the root record; source uniqueness fixes every alternate
decomposition of the same boundary coordinate. -/
theorem exact_selected_fold_boundary_installs_standalone
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
    (fold : ExactAcceptedFoldTrial input)
    (boundaryIndex : Nat)
    (prior later : List UnifiedExposureRecord) (actor : QueryActor)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++
        (.machineFresh actor (selectedFoldBoundaryInput input fold)
          fold.boundaryAnswer : UnifiedExposureRecord) :: later)
    (indexExact : boundaryIndex = prior.length) :
    ExactAlphaZeroProducerInstalled input boundaryIndex
      { digest := fold.boundaryAnswer, block := 0,
        sourceInput := selectedFoldBoundaryInput input fold } := by
  let producer : AlphaZeroProducer :=
    { digest := fold.boundaryAnswer, block := 0,
      sourceInput := selectedFoldBoundaryInput input fold }
  intro arbitraryPrior arbitraryLater arbitraryActor arbitraryExact
  have prefixExact : prior = arbitraryPrior := by
    apply alpha_mapped_nodup_selected_prefix_eq causalInput?
      (exactFixedRootRecords input.package.root) prior later arbitraryPrior
        arbitraryLater
      (.machineFresh actor producer.sourceInput producer.digest :
        UnifiedExposureRecord)
      (.machineFresh arbitraryActor producer.sourceInput producer.digest :
        UnifiedExposureRecord)
      (exact_root_record_causal_inputs_nodup input)
    · simpa [producer] using rootExact
    · simpa [producer] using arbitraryExact
    · simp [causalInput?]
  subst arbitraryPrior
  refine ⟨by omega, ?_⟩
  let controller := alphaZeroCausalController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel boundaryIndex
  let initial := exactAlphaZeroInitialState input
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let selected : UnifiedExposureRecord :=
    .machineFresh actor producer.sourceInput producer.digest
  have selectedAligned : unifiedRecordAtAnswer transitionFuel reached.cursor
      producer.digest = selected := by
    have rootAligned := exact_root_records_aligned_for_alpha_zero_controller
      input boundaryIndex
    exact rootAligned prior selected later (by simpa [selected, producer] using
      rootExact)
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some producer.sourceInput :=
    aligned_machine_record_has_exact_input transitionFuel reached.cursor actor
      producer.sourceInput producer.digest (by simpa [selected] using
        selectedAligned)
  have reachedIndex : reached.exposureIndex = boundaryIndex := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller prior initial
    simpa [reached, initial, exactAlphaZeroInitialState, indexExact] using count
  have boundaryTrue : isAlphaZeroBoundaryInput producer.sourceInput = true := by
    simp [producer, selectedFoldBoundaryInput, isAlphaZeroBoundaryInput,
      alphaZeroBoundaryPayload,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data]
  rw [indexed_state_after_records_append,
    indexed_state_after_records_cons, indexed_state_after_records_nil]
  change producer ∈
    (alphaZeroAfterMemory transitionFuel boundaryIndex reached
      producer.digest).producers
  rw [alpha_zero_after_boundary_has_block_zero_producer transitionFuel
    boundaryIndex reached producer.sourceInput producer.digest inputExact
    reachedIndex boundaryTrue]
  simp [producer]

/-- Every consumed selected-fold alpha output has one actor-tagged exact-root
decomposition strictly after the literal boundary record. -/
theorem exact_selected_fold_boundary_before_consumed_output
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (index : Nat) (inOutputs : index < fold.alphaOutputs.length) :
    ∃ boundaryPrior between outputLater boundaryActor outputActor outputInput,
      outputInput.length = 33 ∧
      exactFixedRootRecords input.package.root =
        boundaryPrior ++
          (.machineFresh boundaryActor
            (selectedFoldBoundaryInput input fold) fold.boundaryAnswer :
              UnifiedExposureRecord) ::
          between ++
          (.machineFresh outputActor outputInput fold.alphaOutputs[index] :
            UnifiedExposureRecord) :: outputLater := by
  have chain := exact_accepted_fold_alpha_chain_has_root_order transitionRoom
    input fold
  obtain ⟨outputInput, outputLength, rootBefore, rootMiddle, rootAfter,
      ordered⟩ :=
    exact_ordered_chain_initial_before_output_at chain index inOutputs
  obtain ⟨boundaryPrior, between, outputLater, boundaryActor, outputActor,
      lifted⟩ :=
    exact_root_pair_order_lifts_to_records input
      (selectedFoldBoundaryInput input fold) outputInput fold.boundaryAnswer
      fold.alphaOutputs[index] rootBefore rootMiddle rootAfter (by
        simpa [selectedFoldBoundaryInput] using ordered)
  exact ⟨boundaryPrior, between, outputLater, boundaryActor, outputActor,
    outputInput, outputLength, lifted⟩

/-- In the boundary-first source order, replaying from the exact pair anchor
to any consumed alpha output projects the bidirectional controller to the
standalone alpha controller at that literal pre-answer prefix. -/
theorem exact_boundary_first_alpha_projection_before_output
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (trial : ExactCompilerExposureTrial parameters)
    (pairPrior pairMiddle pairLater : List UnifiedExposureRecord)
    (pairBoundaryActor : QueryActor)
    (pairRoot : exactFixedRootRecords input.package.root =
      pairPrior ++
        (.machineFresh pairBoundaryActor
          (selectedFoldBoundaryInput input fold) fold.boundaryAnswer :
            UnifiedExposureRecord) ::
        pairMiddle ++
        (.machineFresh fold.actor (selectedFoldWorkInput input fold)
          fold.answer : UnifiedExposureRecord) :: pairLater)
    (anchorExact : trial.val = pairPrior.length)
    (index : Nat) (inOutputs : index < fold.alphaOutputs.length) :
    ∃ outputPrefix outputLater outputActor outputInput,
      outputInput.length = 33 ∧
      exactFixedRootRecords input.package.root =
        outputPrefix ++
          (.machineFresh outputActor outputInput fold.alphaOutputs[index] :
            UnifiedExposureRecord) :: outputLater ∧
      BidirectionalAlphaProjection trial.val pairPrior.length
        (selectedFoldBoundaryInput input fold)
        (some (selectedFoldWorkInput input fold))
        (indexedStateAfterRecords transitionFuel
          (exactBidirectionalFoldController transitionFuel trial) outputPrefix
          (exactBidirectionalFoldInitialState input))
        (indexedStateAfterRecords transitionFuel
          (alphaZeroCausalController transitionFuel pairPrior.length)
          outputPrefix (exactAlphaZeroInitialState input)) := by
  obtain ⟨boundaryPrior, between, outputLater, boundaryActor, outputActor,
      outputInput, outputLength, boundaryOutputRoot⟩ :=
    exact_selected_fold_boundary_before_consumed_output transitionRoom input
      fold index inOutputs
  let boundaryRecord : UnifiedExposureRecord :=
    .machineFresh boundaryActor (selectedFoldBoundaryInput input fold)
      fold.boundaryAnswer
  let pairBoundaryRecord : UnifiedExposureRecord :=
    .machineFresh pairBoundaryActor (selectedFoldBoundaryInput input fold)
      fold.boundaryAnswer
  let outputRecord : UnifiedExposureRecord :=
    .machineFresh outputActor outputInput fold.alphaOutputs[index]
  have boundaryPrefixExact : pairPrior = boundaryPrior := by
    apply alpha_mapped_nodup_selected_prefix_eq causalInput?
      (exactFixedRootRecords input.package.root) pairPrior
      (pairMiddle ++
        (.machineFresh fold.actor (selectedFoldWorkInput input fold)
          fold.answer : UnifiedExposureRecord) :: pairLater)
      boundaryPrior (between ++ outputRecord :: outputLater)
      pairBoundaryRecord boundaryRecord
      (exact_root_record_causal_inputs_nodup input)
    · simpa [pairBoundaryRecord, List.append_assoc] using pairRoot
    · simpa [boundaryRecord, outputRecord, List.append_assoc] using
        boundaryOutputRoot
    · simp [pairBoundaryRecord, boundaryRecord, causalInput?]
  subst boundaryPrior
  have boundaryRecordExact : pairBoundaryRecord = boundaryRecord := by
    apply List.inj_on_of_nodup_map
      (exact_root_record_causal_inputs_nodup input)
    · rw [pairRoot]
      simp [pairBoundaryRecord]
    · rw [boundaryOutputRoot]
      simp [boundaryRecord]
    · simp [pairBoundaryRecord, boundaryRecord, causalInput?]
  let controller := exactBidirectionalFoldController transitionFuel trial
  let standaloneController := alphaZeroCausalController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel pairPrior.length
  let initial := exactBidirectionalFoldInitialState input
  let standaloneInitial := exactAlphaZeroInitialState input
  let reached := indexedStateAfterRecords transitionFuel controller pairPrior
    initial
  let standaloneReached := indexedStateAfterRecords transitionFuel
    standaloneController pairPrior standaloneInitial
  have reachedIndex : reached.exposureIndex = trial.val := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller pairPrior initial
    rw [count]
    simp [initial, exactBidirectionalFoldInitialState,
      bidirectionalFoldAlphaInitialState, anchorExact]
  have exposureExact : reached.exposureIndex = standaloneReached.exposureIndex := by
    rw [indexed_state_after_records_exposure_index,
      indexed_state_after_records_exposure_index]
    simp [initial, standaloneInitial, exactBidirectionalFoldInitialState,
      bidirectionalFoldAlphaInitialState, exactAlphaZeroInitialState]
  have cursorExact : reached.cursor = standaloneReached.cursor := by
    apply indexed_state_after_records_cursor_eq transitionFuel controller
      standaloneController pairPrior initial standaloneInitial
    rfl
  have preInvariant : BidirectionalPreAnchorInvariant reached.memory := by
    apply bidirectional_pre_anchor_invariant_replay transitionFuel trial.val
      pairPrior initial inactive_bidirectional_pre_anchor
    simpa [initial, exactBidirectionalFoldInitialState,
      bidirectionalFoldAlphaInitialState, anchorExact]
  have standaloneInactive : standaloneReached.memory =
      inactiveAlphaZeroMemory := by
    apply alpha_zero_inactive_replay_before_boundary transitionFuel
      pairPrior.length pairPrior standaloneInitial
    · simp [standaloneInitial, exactAlphaZeroInitialState]
    · simp [standaloneInitial, exactAlphaZeroInitialState]
  have rootAligned :=
    exact_root_records_aligned_for_bidirectional_fold_controller input trial
  have boundaryAligned : unifiedRecordAtAnswer transitionFuel reached.cursor
      fold.boundaryAnswer = pairBoundaryRecord := by
    exact rootAligned pairPrior pairBoundaryRecord
      (pairMiddle ++
        (.machineFresh fold.actor (selectedFoldWorkInput input fold)
          fold.answer : UnifiedExposureRecord) :: pairLater)
      (by simpa [pairBoundaryRecord, List.append_assoc] using pairRoot)
  have boundaryInputExact : currentBidirectionalInput? transitionFuel reached =
      some (selectedFoldBoundaryInput input fold) := by
    exact aligned_machine_record_has_exact_input transitionFuel reached.cursor
      pairBoundaryActor (selectedFoldBoundaryInput input fold)
      fold.boundaryAnswer (by simpa [pairBoundaryRecord] using boundaryAligned)
  let afterBoundary := controller.afterAnswer transitionFuel reached
    fold.boundaryAnswer
  let standaloneAfterBoundary := standaloneController.afterAnswer
    transitionFuel standaloneReached fold.boundaryAnswer
  have afterProjection : BidirectionalAlphaProjection trial.val
      pairPrior.length (selectedFoldBoundaryInput input fold)
      (some (selectedFoldWorkInput input fold)) afterBoundary
      standaloneAfterBoundary := by
    simpa [controller, exactBidirectionalFoldController, standaloneController,
      afterBoundary, standaloneAfterBoundary, selectedFoldBoundaryInput,
      selectedFoldWorkInput, anchorExact] using
      boundary_first_anchor_establishes_alpha_projection transitionFuel
        trial.val reached standaloneReached fold.digest
        (exactOperationalTape input).messages.foldGrinding.selected
        fold.boundaryAnswer reachedIndex exposureExact cursorExact preInvariant
        standaloneInactive (by
          simpa [selectedFoldBoundaryInput] using boundaryInputExact)
  have betweenAligned : IndexedRecordsAligned transitionFuel controller
      afterBoundary between := by
    have segment := indexed_records_aligned_segment transitionFuel controller initial
      (exactFixedRootRecords input.package.root)
      (pairPrior ++ [pairBoundaryRecord]) between
      (outputRecord :: outputLater) (by
        simpa [controller, exactBidirectionalFoldController, initial,
          exactBidirectionalFoldInitialState] using rootAligned) (by
        simpa [boundaryRecordExact, boundaryRecord, outputRecord,
          List.append_assoc] using boundaryOutputRoot)
    simpa [afterBoundary, reached, pairBoundaryRecord,
      UnifiedExposureRecord.answer, indexed_state_after_records_append] using
      segment
  have betweenOnly : OnlyMachineFreshRecords between := by
    apply only_machine_fresh_records_segment
      (exactFixedRootRecords input.package.root)
      (pairPrior ++ [pairBoundaryRecord]) between
      (outputRecord :: outputLater)
      (exact_root_records_only_machine_fresh input)
    simpa [boundaryRecordExact, boundaryRecord, outputRecord,
      List.append_assoc] using boundaryOutputRoot
  have betweenAvoids : ∀ record ∈ between,
      causalInput? record ≠ some (selectedFoldBoundaryInput input fold) := by
    intro record member equal
    have rootNodup := exact_root_record_causal_inputs_nodup input
    rw [boundaryOutputRoot] at rootNodup
    simp only [List.map_append, List.map_cons] at rootNodup
    have leftNodup := (List.nodup_append.mp rootNodup).1
    have suffixNodup := (List.nodup_append.mp leftNodup).2.1
    have boundaryMissing := (List.nodup_cons.mp suffixNodup).1
    apply boundaryMissing
    exact List.mem_map.mpr ⟨record, member, equal⟩
  have afterBoundaryIndex : pairPrior.length < afterBoundary.exposureIndex := by
    simp [afterBoundary, reached, reachedIndex, anchorExact]
  have replayProjection := bidirectional_alpha_projection_replay
    transitionFuel trial.val pairPrior.length
    (selectedFoldBoundaryInput input fold)
    (some (selectedFoldWorkInput input fold)) between afterBoundary
    standaloneAfterBoundary afterProjection afterBoundaryIndex betweenAligned
    betweenOnly betweenAvoids (by
      intro workInput expected
      have workExact : workInput = selectedFoldWorkInput input fold :=
        Option.some.inj expected.symm
      subst workInput
      simp [selectedFoldWorkInput, literal_fold_work_length])
  let outputPrefix := pairPrior ++ pairBoundaryRecord :: between
  refine ⟨outputPrefix, outputLater, outputActor, outputInput, outputLength,
    ?_, ?_⟩
  · change exactFixedRootRecords input.package.root =
      (pairPrior ++ pairBoundaryRecord :: between) ++
        (.machineFresh outputActor outputInput fold.alphaOutputs[index] :
          UnifiedExposureRecord) :: outputLater
    rw [boundaryRecordExact]
    simpa [boundaryRecord, outputRecord, List.append_assoc] using
      boundaryOutputRoot
  · simpa [outputPrefix, controller, standaloneController, initial,
      standaloneInitial, reached, standaloneReached, afterBoundary,
      standaloneAfterBoundary, pairBoundaryRecord,
      exactBidirectionalFoldController, exactBidirectionalFoldInitialState,
      UnifiedExposureRecord.answer, indexed_state_after_records_append] using
      replayProjection

/-- In the work-first source order, the pair anchor arms the literal later
boundary without reading its answer from the future.  Replaying through that
boundary and onward to a consumed alpha output then gives the same exact
standalone projection as the boundary-first case. -/
theorem exact_work_first_alpha_projection_before_output
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (trial : ExactCompilerExposureTrial parameters)
    (pairPrior pairMiddle pairLater : List UnifiedExposureRecord)
    (pairBoundaryActor : QueryActor)
    (pairRoot : exactFixedRootRecords input.package.root =
      pairPrior ++
        (.machineFresh fold.actor (selectedFoldWorkInput input fold)
          fold.answer : UnifiedExposureRecord) ::
        pairMiddle ++
        (.machineFresh pairBoundaryActor
          (selectedFoldBoundaryInput input fold) fold.boundaryAnswer :
            UnifiedExposureRecord) :: pairLater)
    (anchorExact : trial.val = pairPrior.length)
    (index : Nat) (inOutputs : index < fold.alphaOutputs.length) :
    ∃ outputPrefix outputLater outputActor outputInput,
      outputInput.length = 33 ∧
      exactFixedRootRecords input.package.root =
        outputPrefix ++
          (.machineFresh outputActor outputInput fold.alphaOutputs[index] :
            UnifiedExposureRecord) :: outputLater ∧
      BidirectionalAlphaProjection trial.val
        (pairPrior ++
          [(.machineFresh fold.actor (selectedFoldWorkInput input fold)
            fold.answer : UnifiedExposureRecord)] ++ pairMiddle).length
        (selectedFoldBoundaryInput input fold) none
        (indexedStateAfterRecords transitionFuel
          (exactBidirectionalFoldController transitionFuel trial) outputPrefix
          (exactBidirectionalFoldInitialState input))
        (indexedStateAfterRecords transitionFuel
          (alphaZeroCausalController transitionFuel
            (pairPrior ++
              [(.machineFresh fold.actor (selectedFoldWorkInput input fold)
                fold.answer : UnifiedExposureRecord)] ++ pairMiddle).length)
          outputPrefix (exactAlphaZeroInitialState input)) := by
  obtain ⟨boundaryPrior, between, outputLater, boundaryActor, outputActor,
      outputInput, outputLength, boundaryOutputRoot⟩ :=
    exact_selected_fold_boundary_before_consumed_output transitionRoom input
      fold index inOutputs
  let workRecord : UnifiedExposureRecord :=
    .machineFresh fold.actor (selectedFoldWorkInput input fold) fold.answer
  let pairBoundaryRecord : UnifiedExposureRecord :=
    .machineFresh pairBoundaryActor (selectedFoldBoundaryInput input fold)
      fold.boundaryAnswer
  let boundaryRecord : UnifiedExposureRecord :=
    .machineFresh boundaryActor (selectedFoldBoundaryInput input fold)
      fold.boundaryAnswer
  let outputRecord : UnifiedExposureRecord :=
    .machineFresh outputActor outputInput fold.alphaOutputs[index]
  have boundaryPrefixExact :
      pairPrior ++ workRecord :: pairMiddle = boundaryPrior := by
    apply alpha_mapped_nodup_selected_prefix_eq causalInput?
      (exactFixedRootRecords input.package.root)
      (pairPrior ++ workRecord :: pairMiddle) pairLater
      boundaryPrior (between ++ outputRecord :: outputLater)
      pairBoundaryRecord boundaryRecord
      (exact_root_record_causal_inputs_nodup input)
    · simpa [workRecord, pairBoundaryRecord, List.append_assoc] using pairRoot
    · simpa [boundaryRecord, outputRecord, List.append_assoc] using
        boundaryOutputRoot
    · simp [pairBoundaryRecord, boundaryRecord, causalInput?]
  have boundaryRecordExact : pairBoundaryRecord = boundaryRecord := by
    apply List.inj_on_of_nodup_map
      (exact_root_record_causal_inputs_nodup input)
    · rw [pairRoot]
      simp [pairBoundaryRecord]
    · rw [boundaryOutputRoot]
      simp [boundaryRecord]
    · simp [pairBoundaryRecord, boundaryRecord, causalInput?]
  let boundaryIndex :=
    (pairPrior ++ [workRecord] ++ pairMiddle).length
  let controller := exactBidirectionalFoldController transitionFuel trial
  let standaloneController := alphaZeroCausalController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel boundaryIndex
  let initial := exactBidirectionalFoldInitialState input
  let standaloneInitial := exactAlphaZeroInitialState input
  let reached := indexedStateAfterRecords transitionFuel controller pairPrior
    initial
  let standaloneReached := indexedStateAfterRecords transitionFuel
    standaloneController pairPrior standaloneInitial
  have reachedIndex : reached.exposureIndex = trial.val := by
    rw [indexed_state_after_records_exposure_index]
    simp [reached, initial, exactBidirectionalFoldInitialState,
      bidirectionalFoldAlphaInitialState, anchorExact]
  have anchorBeforeBoundary : trial.val < boundaryIndex := by
    simp only [boundaryIndex, List.length_append, List.length_singleton,
      List.length_cons, List.length_nil]
    omega
  have exposureExact : reached.exposureIndex = standaloneReached.exposureIndex := by
    rw [indexed_state_after_records_exposure_index,
      indexed_state_after_records_exposure_index]
    simp [initial, standaloneInitial, exactBidirectionalFoldInitialState,
      bidirectionalFoldAlphaInitialState, exactAlphaZeroInitialState]
  have cursorExact : reached.cursor = standaloneReached.cursor := by
    apply indexed_state_after_records_cursor_eq transitionFuel controller
      standaloneController pairPrior initial standaloneInitial
    rfl
  have preInvariant : BidirectionalPreAnchorInvariant reached.memory := by
    apply bidirectional_pre_anchor_invariant_replay transitionFuel trial.val
      pairPrior initial inactive_bidirectional_pre_anchor
    simpa [initial, exactBidirectionalFoldInitialState,
      bidirectionalFoldAlphaInitialState, anchorExact]
  have standaloneInactive : standaloneReached.memory =
      inactiveAlphaZeroMemory := by
    apply alpha_zero_inactive_replay_before_boundary transitionFuel
      boundaryIndex pairPrior standaloneInitial
    · simp [standaloneInitial, exactAlphaZeroInitialState]
    · simp only [standaloneInitial, exactAlphaZeroInitialState, boundaryIndex,
        List.length_append, List.length_singleton]
      omega
  have rootAligned :=
    exact_root_records_aligned_for_bidirectional_fold_controller input trial
  have workAligned : unifiedRecordAtAnswer transitionFuel reached.cursor
      fold.answer = workRecord := by
    exact rootAligned pairPrior workRecord
      (pairMiddle ++ pairBoundaryRecord :: pairLater)
      (by simpa [workRecord, pairBoundaryRecord, List.append_assoc] using pairRoot)
  have workInputExact : currentBidirectionalInput? transitionFuel reached =
      some (selectedFoldWorkInput input fold) := by
    exact aligned_machine_record_has_exact_input transitionFuel reached.cursor
      fold.actor (selectedFoldWorkInput input fold) fold.answer
      (by simpa [workRecord] using workAligned)
  have reachedSeen : reached.memory.alpha.seenMachine =
      pairPrior.filterMap bidirectionalMachineFreshPair? := by
    have replayExact := bidirectional_pre_anchor_seen_machine_replay_exact
      transitionFuel trial.val pairPrior initial
    have alignedPrior : IndexedRecordsAligned transitionFuel controller initial
        pairPrior := by
      apply indexed_records_aligned_segment transitionFuel controller initial
        (exactFixedRootRecords input.package.root) [] pairPrior
        (workRecord :: pairMiddle ++ pairBoundaryRecord :: pairLater)
      · simpa [controller, initial, exactBidirectionalFoldController,
          exactBidirectionalFoldInitialState] using rootAligned
      · simpa [workRecord, pairBoundaryRecord, List.append_assoc] using pairRoot
    have onlyPrior : OnlyMachineFreshRecords pairPrior := by
      apply only_machine_fresh_records_segment
        (exactFixedRootRecords input.package.root) [] pairPrior
        (workRecord :: pairMiddle ++ pairBoundaryRecord :: pairLater)
        (exact_root_records_only_machine_fresh input)
      simpa [workRecord, pairBoundaryRecord, List.append_assoc] using pairRoot
    have := replayExact alignedPrior onlyPrior (by
      simp [initial, exactBidirectionalFoldInitialState,
        bidirectionalFoldAlphaInitialState, anchorExact])
    simpa [reached, controller, exactBidirectionalFoldController, initial,
      exactBidirectionalFoldInitialState, bidirectionalFoldAlphaInitialState,
      inactiveBidirectionalFoldAlphaMemory, inactiveFoldArmedAlphaZeroMemory]
      using this
  have boundaryNotCached : seenMachineAnswer?
      (bidirectionalAlphaState reached).memory
      (selectedFoldBoundaryInput input fold) = none := by
    change seenMachineAnswer? reached.memory.alpha
      (selectedFoldBoundaryInput input fold) = none
    unfold seenMachineAnswer?
    cases found : reached.memory.alpha.seenMachine.find?
        (fun pair => pair.1 = selectedFoldBoundaryInput input fold) with
    | none => simp
    | some pair =>
        have pairMember := List.mem_of_find?_eq_some found
        rw [reachedSeen] at pairMember
        obtain ⟨record, recordMember, pairExact⟩ :=
          List.mem_filterMap.mp pairMember
        obtain ⟨actor, recordInput, recordAnswer, recordExact⟩ :=
          exact_root_records_only_machine_fresh input record (by
            rw [pairRoot]
            exact List.mem_append_left _
              (List.mem_append_left _ recordMember))
        subst record
        simp [bidirectionalMachineFreshPair?] at pairExact
        subst pair
        have inputExact : recordInput = selectedFoldBoundaryInput input fold :=
          of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1
        have nodup := exact_root_record_causal_inputs_nodup input
        rw [pairRoot] at nodup
        simp only [List.map_append, List.map_cons] at nodup
        have separated := (List.nodup_append.mp nodup).2.2
        have leftMember : some (selectedFoldBoundaryInput input fold) ∈
            (pairPrior.map causalInput? ++
              causalInput? workRecord :: pairMiddle.map causalInput?) := by
          rw [List.mem_append]
          exact Or.inl (List.mem_map.mpr ⟨
            .machineFresh actor recordInput recordAnswer, recordMember,
            by simp [causalInput?, inputExact]⟩)
        have rightMember : some (selectedFoldBoundaryInput input fold) ∈
            (causalInput? pairBoundaryRecord :: pairLater.map causalInput?) := by
          simp [pairBoundaryRecord, causalInput?]
        exact (separated _ leftMember _ rightMember rfl).elim
  let afterWork := controller.afterAnswer transitionFuel reached fold.answer
  let standaloneAfterWork := standaloneController.afterAnswer transitionFuel
    standaloneReached fold.answer
  have afterWorkProjection : BidirectionalAlphaProjection trial.val
      boundaryIndex (selectedFoldBoundaryInput input fold) none afterWork
      standaloneAfterWork := by
    simpa [controller, exactBidirectionalFoldController, standaloneController,
      afterWork, standaloneAfterWork, selectedFoldBoundaryInput,
      selectedFoldWorkInput] using
      work_first_anchor_establishes_alpha_projection transitionFuel trial.val
        boundaryIndex reached standaloneReached fold.digest
        (exactOperationalTape input).messages.foldGrinding.selected fold.answer
        reachedIndex anchorBeforeBoundary exposureExact cursorExact preInvariant
        standaloneInactive (by simpa [selectedFoldBoundaryInput] using
          boundaryNotCached) (by simpa [selectedFoldWorkInput] using
            workInputExact)
  have middleAligned : IndexedRecordsAligned transitionFuel controller
      afterWork pairMiddle := by
    have segment := indexed_records_aligned_segment transitionFuel controller
      initial (exactFixedRootRecords input.package.root)
      (pairPrior ++ [workRecord]) pairMiddle
      (pairBoundaryRecord :: pairLater)
      (by simpa [controller, initial, exactBidirectionalFoldController,
        exactBidirectionalFoldInitialState] using rootAligned)
      (by simpa [workRecord, pairBoundaryRecord, List.append_assoc] using pairRoot)
    simpa [afterWork, reached, workRecord, UnifiedExposureRecord.answer,
      indexed_state_after_records_append] using segment
  have middleOnly : OnlyMachineFreshRecords pairMiddle := by
    apply only_machine_fresh_records_segment
      (exactFixedRootRecords input.package.root) (pairPrior ++ [workRecord])
      pairMiddle (pairBoundaryRecord :: pairLater)
      (exact_root_records_only_machine_fresh input)
    simpa [workRecord, pairBoundaryRecord, List.append_assoc] using pairRoot
  have middleAvoids : ∀ record ∈ pairMiddle,
      causalInput? record ≠ some (selectedFoldBoundaryInput input fold) := by
    intro record member equal
    have nodup := exact_root_record_causal_inputs_nodup input
    rw [pairRoot] at nodup
    simp only [List.map_append, List.map_cons] at nodup
    have separated := (List.nodup_append.mp nodup).2.2
    apply separated (some (selectedFoldBoundaryInput input fold))
      (by
        rw [List.mem_append]
        exact Or.inr (List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨record, member, equal⟩)))
      (some (selectedFoldBoundaryInput input fold)) (by
        simp [pairBoundaryRecord, causalInput?]) rfl
  have beforeBoundaryProjection :=
    bidirectional_alpha_projection_replay_before_boundary transitionFuel
      trial.val boundaryIndex (selectedFoldBoundaryInput input fold) none
      pairMiddle afterWork standaloneAfterWork afterWorkProjection
      (by
        simp only [afterWork, indexed_after_answer_exposure_index,
          boundaryIndex, List.length_append, List.length_singleton]
        omega)
      middleAligned middleOnly middleAvoids (by simp)
  let beforeBoundary := indexedStateAfterRecords transitionFuel controller
    pairMiddle afterWork
  let standaloneBeforeBoundary := indexedStateAfterRecords transitionFuel
    standaloneController pairMiddle standaloneAfterWork
  have beforeBoundaryIndex : beforeBoundary.exposureIndex = boundaryIndex := by
    rw [indexed_state_after_records_exposure_index]
    simp [beforeBoundary, afterWork, reached, reachedIndex, boundaryIndex,
      workRecord, anchorExact]
  have boundaryAligned : unifiedRecordAtAnswer transitionFuel
      beforeBoundary.cursor fold.boundaryAnswer = pairBoundaryRecord := by
    have segment := rootAligned
      (pairPrior ++ workRecord :: pairMiddle) pairBoundaryRecord pairLater
      (by simpa [workRecord, pairBoundaryRecord, List.append_assoc] using pairRoot)
    simpa [beforeBoundary, afterWork, reached, workRecord,
      UnifiedExposureRecord.answer, indexed_state_after_records_append,
      controller, initial, exactBidirectionalFoldController,
      exactBidirectionalFoldInitialState] using segment
  have boundaryInputExact : currentBidirectionalInput? transitionFuel
      beforeBoundary = some (selectedFoldBoundaryInput input fold) := by
    exact aligned_machine_record_has_exact_input transitionFuel
      beforeBoundary.cursor pairBoundaryActor
      (selectedFoldBoundaryInput input fold) fold.boundaryAnswer
      (by simpa [pairBoundaryRecord] using boundaryAligned)
  let afterBoundary := controller.afterAnswer transitionFuel beforeBoundary
    fold.boundaryAnswer
  let standaloneAfterBoundary := standaloneController.afterAnswer
    transitionFuel standaloneBeforeBoundary fold.boundaryAnswer
  have afterBoundaryProjection : BidirectionalAlphaProjection trial.val
      boundaryIndex (selectedFoldBoundaryInput input fold) none afterBoundary
      standaloneAfterBoundary := by
    simpa [controller, exactBidirectionalFoldController, standaloneController,
      afterBoundary, standaloneAfterBoundary, beforeBoundary,
      standaloneBeforeBoundary, selectedFoldBoundaryInput] using
      work_first_boundary_establishes_postboundary_projection transitionFuel
        trial.val boundaryIndex beforeBoundary standaloneBeforeBoundary
        fold.digest (exactOperationalTape input).messages.foldGrinding.selected
        fold.boundaryAnswer (by simpa [beforeBoundary, standaloneBeforeBoundary,
          controller, exactBidirectionalFoldController, standaloneController,
          selectedFoldBoundaryInput] using beforeBoundaryProjection)
          beforeBoundaryIndex (by
            simpa [selectedFoldBoundaryInput] using boundaryInputExact)
  have betweenAligned : IndexedRecordsAligned transitionFuel controller
      afterBoundary between := by
    have segment := indexed_records_aligned_segment transitionFuel controller initial
      (exactFixedRootRecords input.package.root)
      (pairPrior ++ workRecord :: pairMiddle ++ [pairBoundaryRecord]) between
      (outputRecord :: outputLater)
      (by simpa [controller, initial, exactBidirectionalFoldController,
        exactBidirectionalFoldInitialState] using rootAligned)
      (by rw [boundaryPrefixExact, boundaryRecordExact]
          simpa [boundaryRecord, outputRecord, List.append_assoc] using
            boundaryOutputRoot)
    simpa [afterBoundary, beforeBoundary, afterWork, reached, workRecord,
      pairBoundaryRecord, UnifiedExposureRecord.answer,
      indexed_state_after_records_append] using segment
  have betweenOnly : OnlyMachineFreshRecords between := by
    apply only_machine_fresh_records_segment
      (exactFixedRootRecords input.package.root)
      (pairPrior ++ workRecord :: pairMiddle ++ [pairBoundaryRecord]) between
      (outputRecord :: outputLater) (exact_root_records_only_machine_fresh input)
    rw [boundaryPrefixExact, boundaryRecordExact]
    simpa [boundaryRecord, outputRecord, List.append_assoc] using
      boundaryOutputRoot
  have betweenAvoids : ∀ record ∈ between,
      causalInput? record ≠ some (selectedFoldBoundaryInput input fold) := by
    intro record member equal
    have nodup := exact_root_record_causal_inputs_nodup input
    rw [boundaryOutputRoot] at nodup
    simp only [List.map_append, List.map_cons] at nodup
    have leftNodup := (List.nodup_append.mp nodup).1
    have suffixNodup := (List.nodup_append.mp leftNodup).2.1
    have boundaryMissing := (List.nodup_cons.mp suffixNodup).1
    apply boundaryMissing
    exact List.mem_map.mpr ⟨record, member, equal⟩
  have afterBoundaryIndex : boundaryIndex < afterBoundary.exposureIndex := by
    simp [afterBoundary, beforeBoundaryIndex]
  have replayProjection := bidirectional_alpha_projection_replay
    transitionFuel trial.val boundaryIndex
    (selectedFoldBoundaryInput input fold) none between afterBoundary
    standaloneAfterBoundary afterBoundaryProjection afterBoundaryIndex
    betweenAligned betweenOnly betweenAvoids (by simp)
  let outputPrefix :=
    (pairPrior ++ [workRecord] ++ pairMiddle) ++ [pairBoundaryRecord] ++ between
  refine ⟨outputPrefix, outputLater, outputActor, outputInput, outputLength,
    ?_, ?_⟩
  · change exactFixedRootRecords input.package.root =
      ((pairPrior ++ [workRecord] ++ pairMiddle) ++
          [pairBoundaryRecord] ++ between) ++
        (.machineFresh outputActor outputInput fold.alphaOutputs[index] :
          UnifiedExposureRecord) :: outputLater
    calc
      exactFixedRootRecords input.package.root =
          boundaryPrior ++ boundaryRecord :: between ++ outputRecord ::
            outputLater := by
              simpa [boundaryRecord, outputRecord, List.append_assoc] using
                boundaryOutputRoot
      _ = ((pairPrior ++ [workRecord] ++ pairMiddle) ++
            [pairBoundaryRecord] ++ between) ++
          (.machineFresh outputActor outputInput fold.alphaOutputs[index] :
            UnifiedExposureRecord) :: outputLater := by
              rw [← boundaryPrefixExact, ← boundaryRecordExact]
              simp [workRecord, pairBoundaryRecord, outputRecord,
                List.append_assoc]
  · change BidirectionalAlphaProjection trial.val boundaryIndex
      (selectedFoldBoundaryInput input fold) none
      (indexedStateAfterRecords transitionFuel
        (exactBidirectionalFoldController transitionFuel trial) outputPrefix
        (exactBidirectionalFoldInitialState input))
      (indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex) outputPrefix
        (exactAlphaZeroInitialState input))
    simpa [outputPrefix, controller, standaloneController,
      initial, standaloneInitial, reached, standaloneReached, afterWork,
      standaloneAfterWork, beforeBoundary, standaloneBeforeBoundary,
      afterBoundary, standaloneAfterBoundary, workRecord, pairBoundaryRecord,
      exactBidirectionalFoldController, exactBidirectionalFoldInitialState,
      UnifiedExposureRecord.answer, indexed_state_after_records_append] using
      replayProjection

/-- The exact accepted pair trial supplies one source-order-independent
projection at every consumed alpha output.  It also retains the exact
standalone producer installation and the only fact needed about a possible
outstanding work coordinate: its deployed input has length 41. -/
theorem exact_bidirectional_alpha_projection_before_consumed_output
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input)
    (index : Nat) (inOutputs : index < fold.alphaOutputs.length) :
    let trial := exactAcceptedFoldPairTrial input fold
    let producer : AlphaZeroProducer :=
      { digest := fold.boundaryAnswer, block := 0,
        sourceInput := selectedFoldBoundaryInput input fold }
    ∃ boundaryIndex expectedWork outputPrefix outputLater outputActor outputInput,
      outputInput.length = 33 ∧
      exactFixedRootRecords input.package.root =
        outputPrefix ++
          (.machineFresh outputActor outputInput fold.alphaOutputs[index] :
            UnifiedExposureRecord) :: outputLater ∧
      BidirectionalAlphaProjection trial.val boundaryIndex
        (selectedFoldBoundaryInput input fold) expectedWork
        (indexedStateAfterRecords transitionFuel
          (exactBidirectionalFoldController transitionFuel trial) outputPrefix
          (exactBidirectionalFoldInitialState input))
        (indexedStateAfterRecords transitionFuel
          (alphaZeroCausalController transitionFuel boundaryIndex) outputPrefix
          (exactAlphaZeroInitialState input)) ∧
      (∀ workInput, expectedWork = some workInput → workInput.length = 41) ∧
      ExactAlphaZeroProducerInstalled input boundaryIndex producer := by
  let trial := exactAcceptedFoldPairTrial input fold
  let producer : AlphaZeroProducer :=
    { digest := fold.boundaryAnswer, block := 0,
      sourceInput := selectedFoldBoundaryInput input fold }
  have pair := exactAcceptedFoldPairTrial_labeled input fold
  rcases pair with workFirst | boundaryFirst
  · obtain ⟨prior, middle, later, boundaryActor, rootExact, anchorExact⟩ :=
      workFirst
    let workRecord : UnifiedExposureRecord :=
      .machineFresh fold.actor (selectedFoldWorkInput input fold) fold.answer
    let boundaryRecord : UnifiedExposureRecord :=
      .machineFresh boundaryActor (selectedFoldBoundaryInput input fold)
        fold.boundaryAnswer
    let boundaryIndex := (prior ++ [workRecord] ++ middle).length
    obtain ⟨outputPrefix, outputLater, outputActor, outputInput, outputLength,
        outputRoot, projected⟩ :=
      exact_work_first_alpha_projection_before_output transitionRoom input fold
        trial prior middle later boundaryActor rootExact anchorExact index
        inOutputs
    have installed : ExactAlphaZeroProducerInstalled input boundaryIndex
        producer := by
      apply exact_selected_fold_boundary_installs_standalone input fold
        boundaryIndex (prior ++ [workRecord] ++ middle) later boundaryActor
      · simpa [workRecord, boundaryRecord, producer, List.append_assoc] using
          rootExact
      · rfl
    have projectedExact : BidirectionalAlphaProjection trial.val boundaryIndex
        (selectedFoldBoundaryInput input fold) none
        (indexedStateAfterRecords transitionFuel
          (exactBidirectionalFoldController transitionFuel trial) outputPrefix
          (exactBidirectionalFoldInitialState input))
        (indexedStateAfterRecords transitionFuel
          (alphaZeroCausalController transitionFuel boundaryIndex) outputPrefix
          (exactAlphaZeroInitialState input)) := by
      convert projected using 1 <;>
        simp [trial, boundaryIndex, workRecord] <;> omega
    exact ⟨boundaryIndex, none, outputPrefix, outputLater, outputActor,
      outputInput, outputLength, outputRoot, projectedExact, by simp, installed⟩
  · obtain ⟨prior, middle, later, boundaryActor, rootExact, anchorExact⟩ :=
      boundaryFirst
    let boundaryRecord : UnifiedExposureRecord :=
      .machineFresh boundaryActor (selectedFoldBoundaryInput input fold)
        fold.boundaryAnswer
    obtain ⟨outputPrefix, outputLater, outputActor, outputInput, outputLength,
        outputRoot, projected⟩ :=
      exact_boundary_first_alpha_projection_before_output transitionRoom input
        fold trial prior middle later boundaryActor rootExact anchorExact index
        inOutputs
    have installed : ExactAlphaZeroProducerInstalled input prior.length
        producer := by
      apply exact_selected_fold_boundary_installs_standalone input fold
        prior.length prior
        (middle ++
          (.machineFresh fold.actor (selectedFoldWorkInput input fold)
            fold.answer : UnifiedExposureRecord) :: later)
        boundaryActor
      · simpa [boundaryRecord, producer, List.append_assoc] using rootExact
      · rfl
    exact ⟨prior.length, some (selectedFoldWorkInput input fold), outputPrefix,
      outputLater, outputActor, outputInput, outputLength, outputRoot, by
        simpa [trial] using projected, by
          intro workInput exact
          have workExact := Option.some.inj exact
          subst workInput
          exact literal_fold_work_length fold.digest
            (exactOperationalTape input).messages.foldGrinding.selected,
      installed⟩

/-- Every deployed alpha block consumed by the selected one-fold decoder is
one of the four answer-independent named coordinates of the bidirectional
router, and the router returns the exact accepted-root answer. -/
theorem exact_accepted_fold_alpha_outputs_are_bidirectionally_routed
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (programmedCover : 5 ≤ 2 * parameters.forkRequestCap)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (fold : ExactAcceptedFoldTrial input) :
    let trial := exactAcceptedFoldPairTrial input fold
    ∀ index (inOutputs : index < fold.alphaOutputs.length),
      ∃ block : Fin 4, block.val = index ∧
        causalRoutedAnswer? (some block)
          (exactCompilerBidirectionalFoldOneFoldRouter parameters transitionFuel
            trial.val (exactPlainRomCursor configuration sample.1).erase)
          (bidirectionalFoldNamedSlotInputTape parameters sample.2) =
        some fold.alphaOutputs[index] := by
  dsimp only
  intro index inOutputs
  let trial := exactAcceptedFoldPairTrial input fold
  let block : Fin 4 := ⟨index, by
    apply inOutputs.trans_le
    rw [fold.alphaOutputsLength]
    simpa [samplerMode, samplerBlockCap] using
      ((exactOperationalTape input).messages.challengeUse
        (.alpha 0)).withinDeployedCap⟩
  obtain ⟨boundaryIndex, expectedWork, outputPrefix, outputLater, outputActor,
      outputInput, outputLength, outputRoot, projected, workSafe, installed⟩ :=
    exact_bidirectional_alpha_projection_before_consumed_output transitionRoom
      input fold index inOutputs
  have chain := exact_accepted_fold_alpha_chain_has_root_order transitionRoom
    input fold
  have lengthCap : (0 : Fin 4).val + fold.alphaOutputs.length ≤ 4 := by
    simp only [Fin.val_zero, Nat.zero_add]
    rw [fold.alphaOutputsLength]
    simpa [samplerMode, samplerBlockCap] using
      ((exactOperationalTape input).messages.challengeUse
        (.alpha 0)).withinDeployedCap
  obtain ⟨preferredPrefix, preferredLater, preferredActor, preferredInput,
      preferredRoot, standalonePreferredRaw⟩ :=
    exact_ordered_alpha_zero_chain_has_preferred_slots input boundaryIndex
      (0 : Fin 4) chain lengthCap installed index inOutputs
  let outputRecord : UnifiedExposureRecord :=
    .machineFresh outputActor outputInput fold.alphaOutputs[index]
  let preferredRecord : UnifiedExposureRecord :=
    .machineFresh preferredActor preferredInput fold.alphaOutputs[index]
  have prefixExact : outputPrefix = preferredPrefix := by
    apply alpha_mapped_nodup_selected_prefix_eq UnifiedExposureRecord.answer
      (exactFixedRootRecords input.package.root) outputPrefix outputLater
      preferredPrefix preferredLater outputRecord preferredRecord
      (exact_root_record_answers_nodup input)
    · simpa [outputRecord] using outputRoot
    · simpa [preferredRecord] using preferredRoot
    · rfl
  subst preferredPrefix
  have standalonePreferred :
      alphaZeroPreferredSlot transitionFuel
        (indexedStateAfterRecords transitionFuel
          (alphaZeroCausalController transitionFuel boundaryIndex) outputPrefix
          (exactAlphaZeroInitialState input)) = some block := by
    simpa [block] using standalonePreferredRaw
  let bidirectionalState := indexedStateAfterRecords transitionFuel
    (exactBidirectionalFoldController transitionFuel trial) outputPrefix
    (exactBidirectionalFoldInitialState input)
  let standaloneState := indexedStateAfterRecords transitionFuel
    (alphaZeroCausalController transitionFuel boundaryIndex) outputPrefix
    (exactAlphaZeroInitialState input)
  have rootAligned :=
    exact_root_records_aligned_for_bidirectional_fold_controller input trial
  have outputAligned : unifiedRecordAtAnswer transitionFuel
      bidirectionalState.cursor fold.alphaOutputs[index] = outputRecord := by
    simpa [bidirectionalState, exactBidirectionalFoldController,
      exactBidirectionalFoldInitialState, outputRecord,
      UnifiedExposureRecord.answer] using
      rootAligned outputPrefix outputRecord outputLater (by
        simpa [outputRecord] using outputRoot)
  have outputInputExact : currentBidirectionalInput? transitionFuel
      bidirectionalState = some outputInput := by
    exact aligned_machine_record_has_exact_input transitionFuel
      bidirectionalState.cursor outputActor outputInput fold.alphaOutputs[index]
      (by simpa [outputRecord] using outputAligned)
  have noWorkMatch : ¬ (bidirectionalState.memory.foldUsed = false ∧
      matchesExpectedFoldWork
        (currentBidirectionalInput? transitionFuel bidirectionalState)
        bidirectionalState.memory.expectedWork) := by
    intro matched
    rcases matched.2 with ⟨workInput, currentExact, expectedExact⟩
    have workExpected : expectedWork = some workInput := by
      exact projected.2.2.2.2.1.symm.trans expectedExact
    have workLength := workSafe workInput workExpected
    have inputsExact : outputInput = workInput :=
      Option.some.inj (outputInputExact.symm.trans currentExact)
    rw [← inputsExact, outputLength] at workLength
    omega
  have notAnchor : bidirectionalState.exposureIndex ≠ trial.val := by
    exact (Nat.ne_of_lt projected.2.2.2.2.2).symm
  have preferred :
      (exactBidirectionalFoldController transitionFuel trial).preferredSlot
        bidirectionalState = some (some block) := by
    change bidirectionalFoldAlphaPreferred transitionFuel trial.val
      bidirectionalState = some (some block)
    exact bidirectional_preferred_alpha_of_projection transitionFuel trial.val
        boundaryIndex (selectedFoldBoundaryInput input fold) expectedWork
        bidirectionalState standaloneState block (by
          simpa [bidirectionalState, standaloneState] using projected)
        notAnchor noWorkMatch (by simpa [standaloneState] using
          standalonePreferred)
  have residualEnough :=
    exact_bidirectional_fold_root_residual_enough_of_programmed_cover input
      trial programmedCover
  refine ⟨block, rfl, ?_⟩
  exact exact_bidirectional_fold_router_routes_selected_root_answer input trial
      outputPrefix outputLater outputActor outputInput fold.alphaOutputs[index]
      (some block) (by simpa [outputRecord] using outputRoot) residualEnough
      (by simpa [bidirectionalState] using preferred)

#print axioms exact_selected_fold_boundary_installs_standalone
#print axioms exact_selected_fold_boundary_before_consumed_output
#print axioms indexed_state_after_records_cursor_eq
#print axioms exact_boundary_first_alpha_projection_before_output
#print axioms exact_work_first_alpha_projection_before_output
#print axioms exact_bidirectional_alpha_projection_before_consumed_output
#print axioms exact_accepted_fold_alpha_outputs_are_bidirectionally_routed

end

end AspisK1.V7Tag73ExactBidirectionalFoldAlphaRouting
