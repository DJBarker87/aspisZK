import AspisFormal.K1.V7Tag73ExactQueryBatchAlphaProducerSeparation
import AspisFormal.K1.V7Tag73ExactFoldArmedAlphaPrefixInvariant
import AspisFormal.K1.V7Tag73ExactFoldArmedAlphaQ16Disjoint
import AspisFormal.K1.V7Tag73ExactFoldArmedFinalWorkRouting

/-!
# Query-batch residuality for the fold-armed controller

The fixed candidate experiment must not guess the alpha-boundary exposure.
This file rebuilds the query-batch/alpha separation argument for the dynamic
fold-armed controller.  Before the selected fold its alpha inventory is empty;
afterward the accepted-root prefix invariant supplies exact inventory validity,
43-byte block-zero sources, and literal source provenance.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactFoldArmedQueryBatchResidual

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroProducerInvariant
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73ExactAcceptedFoldTrialPackage
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldArmedAlphaPrefixInvariant
open AspisK1.V7Tag73ExactFoldArmedAlphaQ16Disjoint
open AspisK1.V7Tag73ExactFoldArmedAlphaSourceAlignment
open AspisK1.V7Tag73ExactFoldArmedFinalWorkRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactQueryBatchAlphaProducerSeparation
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldArmedAlphaCoreInvariant
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73FoldArmedPreFinalPrefix
open AspisK1.V7Tag73FoldOuterSourceSeparation
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- At any literal accepted-root prefix, the fold-armed alpha inventory has
the three facts needed by the query-batch separation argument. -/
theorem exact_fold_armed_prefix_alpha_facts
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
    (finalTrial : ExactCompilerExposureTrial parameters)
    (prior later : List UnifiedExposureRecord)
    (record : UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ record :: later) :
    let controller := foldArmedCompleteController
      (globalOracleCalls := globalFull256OracleCallCap parameters)
      transitionFuel fold.trial.val finalTrial.val
    let reached := indexedStateAfterRecords transitionFuel controller prior
      (foldArmedInitialState
        (exactPlainRomCursor configuration sample.1).erase)
    AlphaZeroMemoryProducerInvariant reached.memory.2.1.alpha ∧
      AlphaBlockZeroSourcesHaveLength43 reached.memory.2.1.alpha.producers ∧
      (∀ producer ∈ reached.memory.2.1.alpha.producers,
        ∃ actor,
          (.machineFresh actor producer.sourceInput producer.digest :
            UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root) := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  dsimp only
  by_cases beforeOrAt : prior.length ≤ fold.trial.val
  · have empty := fold_armed_alpha_empty_before_selected_fold transitionFuel
      fold.trial.val finalTrial.val prior initial (by
        simpa [initial, foldArmedInitialState] using beforeOrAt) (by rfl) (by rfl)
    change reached.memory.2.1.expectedBoundary = none ∧
      reached.memory.2.1.alpha.producers = [] at empty
    have producersEmpty : reached.memory.2.1.alpha.producers = [] := empty.2
    refine ⟨?_, ?_, ?_⟩
    · refine
        { inventoryValid := ?_
          blocksNodup := ?_
          sourceInputsNodup := ?_ }
      · rw [producersEmpty]
        simp [AlphaZeroProducerInventoryValid]
      · rw [producersEmpty]
        simp
      · rw [producersEmpty]
        simp
    · intro producer member _
      rw [producersEmpty] at member
      simp at member
    · intro producer member
      rw [producersEmpty] at member
      simp at member
  · have after : fold.trial.val < prior.length := by omega
    let selected : UnifiedExposureRecord := .machineFresh fold.actor
      (bytes fold.digest ++ [domGrind] ++
        bytes (exactOperationalTape input).messages.foldGrinding.selected)
      fold.answer
    obtain ⟨segment, priorExact, laterExact⟩ := selected_prefix_split_of_lt
      (exactFixedRootRecords input.package.root) fold.prior prior selected record
        fold.later later (by simpa [selected] using fold.rootDecomposition)
        decomposition (by simpa [fold.trialExact] using after)
    have invariant := exact_fold_armed_post_fold_prefix_invariant input fold
      finalTrial segment (record :: later) (by simpa [selected] using laterExact)
    have reachedExact : reached = indexedStateAfterRecords transitionFuel
        controller segment
        (controller.afterAnswer transitionFuel
          (indexedStateAfterRecords transitionFuel controller fold.prior initial)
          fold.answer) := by
      change indexedStateAfterRecords transitionFuel controller prior initial = _
      rw [priorExact]
      simp [selected, indexed_state_after_records_append,
        UnifiedExposureRecord.answer]
    have invariant' : FoldArmedAlphaPrefixInvariant prior
        reached.memory.2.1 := by
      rw [reachedExact]
      simpa [controller, initial, selected, priorExact] using invariant
    refine ⟨invariant'.core.producer, ?_, ?_⟩
    · exact invariant'.core.blockZeroBoundary
    · intro producer member
      obtain ⟨actor, sourceMember⟩ := invariant'.sourcesLiteral producer member
      exact ⟨actor, by rw [decomposition, List.mem_append]; exact Or.inl sourceMember⟩

/-- A literal query-batch output is residual for the dynamically armed alpha
component.  Equal 33-byte inputs would identify a query state with a live
alpha producer, contradicting the exact accepted-root chain separation. -/
theorem exact_fold_armed_query_batch_output_is_alpha_residual
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
    (finalTrial : ExactCompilerExposureTrial parameters)
    {producerInput : ShaInput} {initialDigest : Digest256}
    {outputs advances : List Digest256}
    (chain : ExactRootOrderedQ16Chain input producerInput initialDigest outputs
      advances)
    (boundaryLength : producerInput.length = 34)
    (state : Digest256)
    (stateMember : state ∈ initialDigest :: advances)
    (output : Digest256) (actor : QueryActor)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root = prior ++
      (.machineFresh actor (gammaOutputInput state) output :
        UnifiedExposureRecord) :: later) :
    alphaZeroPreferredSlot transitionFuel
      (foldArmedAlphaIndexedState
        (foldArmedAlphaState
          (indexedStateAfterRecords transitionFuel
            (foldArmedCompleteController transitionFuel fold.trial.val
              finalTrial.val) prior
            (foldArmedInitialState
              (exactPlainRomCursor configuration sample.1).erase)))) = none := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let alphaReached := foldArmedAlphaIndexedState (foldArmedAlphaState reached)
  obtain ⟨inventory, zeroSources, provenance⟩ :=
    exact_fold_armed_prefix_alpha_facts input fold finalTrial prior later
      (.machineFresh actor (gammaOutputInput state) output) decomposition
  have avoids := exact_root_ordered_query_batch_chain_avoids_alpha_producers
    input reached.memory.2.1.alpha.producers inventory.inventoryValid zeroSources
      provenance chain boundaryLength
  have stateAvoid : ∀ producer ∈ reached.memory.2.1.alpha.producers,
      state ≠ producer.digest := avoids state stateMember
  have aligned := exact_root_records_aligned_for_fold_armed_controller input
    fold.trial finalTrial prior
      (.machineFresh actor (gammaOutputInput state) output) later decomposition
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some (gammaOutputInput state) :=
    aligned_machine_record_has_exact_input transitionFuel reached.cursor actor
      (gammaOutputInput state) output (by
        simpa [reached, controller, initial, UnifiedExposureRecord.answer]
          using aligned)
  change alphaZeroPreferredSlot transitionFuel alphaReached = none
  cases preferred : alphaZeroPreferredSlot transitionFuel alphaReached with
  | none => rfl
  | some slot =>
      obtain ⟨selectedInput, producer, selectedExact, producerMember,
          outputExact, _slotExact⟩ :=
        alpha_zero_preferred_slot_has_producer transitionFuel alphaReached slot
          preferred
      exfalso
      apply stateAvoid producer (by
        simpa [alphaReached, foldArmedAlphaIndexedState, foldArmedAlphaState,
          foldArmedUnderlyingState, alphaIndexedState] using producerMember)
      apply output_input_eq_implies_state_eq state producer.digest
      have inputsEqual : gammaOutputInput state = selectedInput := by
        apply Option.some.inj
        exact inputExact.symm.trans (by
          simpa [alphaReached, foldArmedAlphaIndexedState, foldArmedAlphaState,
            foldArmedUnderlyingState, alphaIndexedState] using selectedExact)
      simpa [gammaOutputInput] using inputsEqual.trans outputExact

/-- A query-batch advance input cannot be an alpha output input, so it is
residual for the dynamically armed alpha component without any inventory
case split. -/
theorem exact_fold_armed_query_batch_advance_is_alpha_residual
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
    (finalTrial : ExactCompilerExposureTrial parameters)
    (state advanced : Digest256) (actor : QueryActor)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root = prior ++
      (.machineFresh actor (gammaAdvanceInput state) advanced :
        UnifiedExposureRecord) :: later) :
    alphaZeroPreferredSlot transitionFuel
      (foldArmedAlphaIndexedState
        (foldArmedAlphaState
          (indexedStateAfterRecords transitionFuel
            (foldArmedCompleteController transitionFuel fold.trial.val
              finalTrial.val) prior
            (foldArmedInitialState
              (exactPlainRomCursor configuration sample.1).erase)))) = none := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  let alphaReached := foldArmedAlphaIndexedState (foldArmedAlphaState reached)
  have aligned := exact_root_records_aligned_for_fold_armed_controller input
    fold.trial finalTrial prior
      (.machineFresh actor (gammaAdvanceInput state) advanced) later decomposition
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some (gammaAdvanceInput state) :=
    aligned_machine_record_has_exact_input transitionFuel reached.cursor actor
      (gammaAdvanceInput state) advanced (by
        simpa [reached, controller, initial, UnifiedExposureRecord.answer]
          using aligned)
  change alphaZeroPreferredSlot transitionFuel alphaReached = none
  cases preferred : alphaZeroPreferredSlot transitionFuel alphaReached with
  | none => rfl
  | some slot =>
      obtain ⟨selectedInput, producer, selectedExact, _producerMember,
          outputExact, _slotExact⟩ :=
        alpha_zero_preferred_slot_has_producer transitionFuel alphaReached slot
          preferred
      exfalso
      apply advance_input_ne_output_input state producer.digest
      have inputsEqual : gammaAdvanceInput state = selectedInput := by
        apply Option.some.inj
        exact inputExact.symm.trans (by
          simpa [alphaReached, foldArmedAlphaIndexedState, foldArmedAlphaState,
            foldArmedUnderlyingState, alphaIndexedState] using selectedExact)
      simpa [gammaAdvanceInput] using inputsEqual.trans outputExact

/-- The complete dynamically fold-armed 518-slot base is residual at a
literal query-batch output. -/
theorem exact_fold_armed_query_batch_output_is_518_residual
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
    (finalTrial : ExactCompilerExposureTrial parameters)
    (beforeDomainDigest initialDigest : Digest256)
    {outputs advances : List Digest256}
    (chain : ExactRootOrderedQ16Chain input
      (bytes beforeDomainDigest ++ [domAbsorb, queryBatchChallengeLabel])
      initialDigest outputs advances)
    (state : Digest256) (stateMember : state ∈ initialDigest :: advances)
    (output : Digest256) (actor : QueryActor)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root = prior ++
      (.machineFresh actor (gammaOutputInput state) output :
        UnifiedExposureRecord) :: later) :
    (foldArmedCompleteController transitionFuel fold.trial.val
      finalTrial.val).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (foldArmedCompleteController transitionFuel fold.trial.val
          finalTrial.val) prior
        (foldArmedInitialState
          (exactPlainRomCursor configuration sample.1).erase)) = none := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  have alphaNone := exact_fold_armed_query_batch_output_is_alpha_residual input
    fold finalTrial chain (by simp) state stateMember output actor prior later
      decomposition
  have dagNone := exact_query_batch_state_output_is_dag_residual input finalTrial
    beforeDomainDigest initialDigest chain state stateMember output actor prior
      later decomposition
  have dagProjection : foldArmedPreFinalDagState reached =
      indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel finalTrial) prior
        (exactDagCandidateInitialState input) := by
    rw [show foldArmedPreFinalDagState reached =
        indexedStateAfterRecords transitionFuel
          (finalWorkQ16DagController (globalFull256OracleCallCap parameters)
            transitionFuel finalTrial.val) prior
          (foldArmedPreFinalDagState initial) by
      exact fold_armed_dag_state_after_records transitionFuel fold.trial.val
        finalTrial.val prior initial]
    rw [fold_armed_initial_dag_state_eq input]
    rfl
  have dagProjected :
      (finalWorkQ16DagController (globalFull256OracleCallCap parameters)
        transitionFuel finalTrial.val).preferredSlot
          (foldArmedPreFinalDagState reached) = none := by
    rw [dagProjection]
    simpa [exactDagTrialController] using dagNone
  have underlyingNone :
      (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
        (foldArmedAlphaZeroController transitionFuel)).preferredSlot
          (foldArmedUnderlyingState reached) = none := by
    have alphaProjected :
        (foldArmedAlphaZeroController transitionFuel).preferredSlot
          (alphaIndexedState (foldArmedUnderlyingState reached)) = none := by
      simpa [foldArmedAlphaZeroController, foldArmedAlphaState] using alphaNone
    have dagProjected' :
        (finalWorkQ16DagController
          (globalFull256OracleCallCap parameters) transitionFuel
          finalTrial.val).preferredSlot
            (finalWorkQ16IndexedState (foldArmedUnderlyingState reached)) =
          none := by
      simpa [foldArmedPreFinalDagState] using dagProjected
    have alphaProjected' := alphaProjected
    change alphaZeroPreferredSlot transitionFuel
      (foldArmedAlphaIndexedState
        (alphaIndexedState (foldArmedUnderlyingState reached))) = none at alphaProjected'
    simp [alphaFinalWorkQ16DagController, alphaProjected', dagProjected']
  have distinct : prior.length ≠ fold.trial.val :=
    exact_33_byte_root_prefix_ne_fold_trial input fold.trial fold.digest
      fold.answer fold.actor fold.prior fold.later fold.rootDecomposition
      fold.trialExact actor (gammaOutputInput state) output prior later
      decomposition (by simp [gammaOutputInput])
  have reachedIndex : reached.exposureIndex = prior.length := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller prior initial
    simpa [reached, initial, foldArmedInitialState] using count
  have notFold : reached.exposureIndex ≠ fold.trial.val := by
    simpa [reachedIndex] using distinct
  change controller.preferredSlot reached = none
  simp [controller, foldArmedCompleteController, notFold, underlyingNone]

/-- The complete dynamically fold-armed 518-slot base is residual at a
literal query-batch advance. -/
theorem exact_fold_armed_query_batch_advance_is_518_residual
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
    (finalTrial : ExactCompilerExposureTrial parameters)
    (state advanced : Digest256) (actor : QueryActor)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root = prior ++
      (.machineFresh actor (gammaAdvanceInput state) advanced :
        UnifiedExposureRecord) :: later) :
    (foldArmedCompleteController transitionFuel fold.trial.val
      finalTrial.val).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (foldArmedCompleteController transitionFuel fold.trial.val
          finalTrial.val) prior
        (foldArmedInitialState
          (exactPlainRomCursor configuration sample.1).erase)) = none := by
  let controller := foldArmedCompleteController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel fold.trial.val finalTrial.val
  let initial := foldArmedInitialState
    (exactPlainRomCursor configuration sample.1).erase
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  have alphaNone := exact_fold_armed_query_batch_advance_is_alpha_residual input
    fold finalTrial state advanced actor prior later decomposition
  have dagNone := exact_query_batch_state_advance_is_dag_residual input finalTrial
    state advanced actor prior later decomposition
  have dagProjection : foldArmedPreFinalDagState reached =
      indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel finalTrial) prior
        (exactDagCandidateInitialState input) := by
    rw [show foldArmedPreFinalDagState reached =
        indexedStateAfterRecords transitionFuel
          (finalWorkQ16DagController (globalFull256OracleCallCap parameters)
            transitionFuel finalTrial.val) prior
          (foldArmedPreFinalDagState initial) by
      exact fold_armed_dag_state_after_records transitionFuel fold.trial.val
        finalTrial.val prior initial]
    rw [fold_armed_initial_dag_state_eq input]
    rfl
  have dagProjected :
      (finalWorkQ16DagController (globalFull256OracleCallCap parameters)
        transitionFuel finalTrial.val).preferredSlot
          (foldArmedPreFinalDagState reached) = none := by
    rw [dagProjection]
    simpa [exactDagTrialController] using dagNone
  have underlyingNone :
      (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
        (foldArmedAlphaZeroController transitionFuel)).preferredSlot
          (foldArmedUnderlyingState reached) = none := by
    have alphaProjected :
        (foldArmedAlphaZeroController transitionFuel).preferredSlot
          (alphaIndexedState (foldArmedUnderlyingState reached)) = none := by
      simpa [foldArmedAlphaZeroController, foldArmedAlphaState] using alphaNone
    have dagProjected' :
        (finalWorkQ16DagController
          (globalFull256OracleCallCap parameters) transitionFuel
          finalTrial.val).preferredSlot
            (finalWorkQ16IndexedState (foldArmedUnderlyingState reached)) =
          none := by
      simpa [foldArmedPreFinalDagState] using dagProjected
    have alphaProjected' := alphaProjected
    change alphaZeroPreferredSlot transitionFuel
      (foldArmedAlphaIndexedState
        (alphaIndexedState (foldArmedUnderlyingState reached))) = none at alphaProjected'
    simp [alphaFinalWorkQ16DagController, alphaProjected', dagProjected']
  have distinct : prior.length ≠ fold.trial.val :=
    exact_33_byte_root_prefix_ne_fold_trial input fold.trial fold.digest
      fold.answer fold.actor fold.prior fold.later fold.rootDecomposition
      fold.trialExact actor (gammaAdvanceInput state) advanced prior later
      decomposition (by simp [gammaAdvanceInput])
  have reachedIndex : reached.exposureIndex = prior.length := by
    have count := indexed_state_after_records_exposure_index transitionFuel
      controller prior initial
    simpa [reached, initial, foldArmedInitialState] using count
  have notFold : reached.exposureIndex ≠ fold.trial.val := by
    simpa [reachedIndex] using distinct
  change controller.preferredSlot reached = none
  simp [controller, foldArmedCompleteController, notFold, underlyingNone]

#print axioms exact_fold_armed_prefix_alpha_facts
#print axioms exact_fold_armed_query_batch_output_is_alpha_residual
#print axioms exact_fold_armed_query_batch_advance_is_alpha_residual
#print axioms exact_fold_armed_query_batch_output_is_518_residual
#print axioms exact_fold_armed_query_batch_advance_is_518_residual

end
end AspisK1.V7Tag73ExactFoldArmedQueryBatchResidual
