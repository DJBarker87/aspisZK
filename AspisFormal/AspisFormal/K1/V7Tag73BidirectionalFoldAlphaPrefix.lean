import AspisFormal.K1.V7Tag73BidirectionalFoldAlphaController
import AspisFormal.K1.V7Tag73IndexedAlignedRecordReplay

/-!
# Prefix invariants for the bidirectional fold/alpha controller

Before the selected pair anchor, the controller may record causal machine
history but cannot allocate the fold slot, install an expected sibling, seed
an alpha producer, or consume an alpha slot.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73BidirectionalFoldAlphaPrefix

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73BidirectionalFoldAlphaController
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def bidirectionalMachineFreshPair? : UnifiedExposureRecord →
    Option (ShaInput × Digest256)
  | .machineFresh _ input answer => some (input, answer)
  | .padding _ | .forkOutput _ _ _ _ _ | .forkAdvance _ => none

def BidirectionalPreAnchorInvariant
    (memory : BidirectionalFoldAlphaMemory) : Prop :=
  memory.foldUsed = false ∧
    memory.expectedWork = none ∧
    memory.alpha.expectedBoundary = none ∧
    memory.alpha.alpha.producers = [] ∧
    memory.alpha.alpha.usedSlots = ∅

def BidirectionalWaitingForWork
    (memory : BidirectionalFoldAlphaMemory) (workInput : ShaInput) : Prop :=
  memory.foldUsed = false ∧ memory.expectedWork = some workInput

@[simp] theorem inactive_bidirectional_pre_anchor :
    BidirectionalPreAnchorInvariant inactiveBidirectionalFoldAlphaMemory := by
  simp [BidirectionalPreAnchorInvariant,
    inactiveBidirectionalFoldAlphaMemory,
    AspisK1.V7Tag73FoldArmedAlphaZeroController.inactiveFoldArmedAlphaZeroMemory,
    AspisK1.V7Tag73AlphaZeroCausalController.inactiveAlphaZeroMemory]

/-- One exposure before the anchor preserves the complete inactive routing
inventory.  The causal `seenMachine` cache is intentionally unrestricted. -/
theorem bidirectional_pre_anchor_invariant_step
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory)
    (answer : Digest256)
    (beforeAnchor : state.exposureIndex ≠ anchorIndex)
    (invariant : BidirectionalPreAnchorInvariant state.memory) :
    BidirectionalPreAnchorInvariant
      (bidirectionalFoldAlphaAfterMemory transitionFuel anchorIndex state
        answer) := by
  rcases invariant with
    ⟨foldUnused, noWork, noBoundary, noProducers, noUsed⟩
  unfold BidirectionalPreAnchorInvariant
  unfold bidirectionalFoldAlphaAfterMemory
  simp only [beforeAnchor, ↓reduceDIte]
  unfold AspisK1.V7Tag73FoldArmedAlphaZeroController.foldArmedAlphaAfterMemory
  cases inputExact : currentBidirectionalInput? transitionFuel state with
  | none =>
      simp [currentBidirectionalInput?] at inputExact
      simp [inputExact, foldUnused, noWork, noBoundary, noProducers, noUsed,
        matchesExpectedFoldWork, bidirectionalAlphaState]
  | some input =>
      simp [currentBidirectionalInput?] at inputExact
      simp [inputExact, foldUnused, noWork, noBoundary, noProducers, noUsed,
        matchesExpectedFoldWork, bidirectionalAlphaState,
        AspisK1.V7Tag73FoldArmedAlphaZeroController.foldArmedAlphaIndexedState,
        AspisK1.V7Tag73AlphaZeroCausalController.alphaZeroPreferredSlot,
        AspisK1.V7Tag73AlphaZeroCausalController.alphaZeroOutputSlot?,
        AspisK1.V7Tag73AlphaZeroCausalController.updateAlphaZeroProducers,
        AspisK1.V7Tag73AlphaZeroCausalController.alphaZeroAdvancedSlot?]

/-- The inactive routing inventory is preserved through any prefix ending no
later than the selected anchor. -/
theorem bidirectional_pre_anchor_invariant_replay
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        BidirectionalFoldAlphaMemory),
      BidirectionalPreAnchorInvariant state.memory →
      state.exposureIndex + records.length ≤ anchorIndex →
      BidirectionalPreAnchorInvariant
        (indexedStateAfterRecords transitionFuel
          (bidirectionalFoldAlphaController transitionFuel anchorIndex)
          records state).memory := by
  intro records
  induction records with
  | nil =>
      intro state invariant _bounded
      simpa only [indexed_state_after_records_nil] using invariant
  | cons record records ih =>
      intro state invariant bounded
      let controller := bidirectionalFoldAlphaController
        (globalOracleCalls := globalOracleCalls) transitionFuel anchorIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      have beforeAnchor : state.exposureIndex ≠ anchorIndex := by
        simp only [List.length_cons] at bounded
        omega
      have nextInvariant : BidirectionalPreAnchorInvariant next.memory := by
        simpa [next, controller,
          bidirectionalFoldAlphaController,
          IndexedUnifiedExposureController.afterAnswer] using
          bidirectional_pre_anchor_invariant_step transitionFuel anchorIndex
            state record.answer beforeAnchor invariant
      have nextBounded : next.exposureIndex + records.length ≤ anchorIndex := by
        simp only [next, controller, indexed_after_answer_exposure_index,
          List.length_cons] at bounded ⊢
        omega
      rw [indexed_state_after_records_cons]
      exact ih next nextInvariant nextBounded

/-- Every record strictly before the selected bidirectional pair anchor is
residual.  The controller cannot allocate the fold slot or any alpha slot
until the anchor itself has been consumed. -/
theorem bidirectional_labeled_records_before_anchor_all_residual
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        BidirectionalFoldAlphaMemory),
      state.exposureIndex + records.length = anchorIndex →
      BidirectionalPreAnchorInvariant state.memory →
      namedTraceSlots
        (indexedControllerLabeledRecords transitionFuel
          (bidirectionalFoldAlphaController transitionFuel anchorIndex)
          state records) = [] := by
  intro records
  induction records with
  | nil =>
      intro state _anchorExact _invariant
      rfl
  | cons record records ih =>
      intro state anchorExact invariant
      rcases invariant with
        ⟨foldUnused, noWork, noBoundary, noProducers, noUsed⟩
      have beforeAnchor : state.exposureIndex ≠ anchorIndex := by
        intro equal
        rw [equal] at anchorExact
        simp only [List.length_cons] at anchorExact
        omega
      let controller := bidirectionalFoldAlphaController
        (globalOracleCalls := globalOracleCalls) transitionFuel anchorIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      have preferredNone : controller.preferredSlot state = none := by
        change bidirectionalFoldAlphaPreferred transitionFuel anchorIndex state =
          none
        unfold bidirectionalFoldAlphaPreferred
        rw [dif_neg beforeAnchor]
        have noMatch : ¬ (state.memory.foldUsed = false ∧
            matchesExpectedFoldWork
              (currentBidirectionalInput? transitionFuel state)
              state.memory.expectedWork) := by
          simp [noWork, matchesExpectedFoldWork]
        rw [if_neg noMatch]
        have alphaNone : alphaZeroPreferredSlot transitionFuel
            (foldArmedAlphaIndexedState (bidirectionalAlphaState state)) =
              none := by
          unfold alphaZeroPreferredSlot
          rw [show
            (foldArmedAlphaIndexedState
              (bidirectionalAlphaState state)).memory.producers = [] by
                exact noProducers]
          cases unifiedInputBeforeAnswer? transitionFuel
              (foldArmedAlphaIndexedState
                (bidirectionalAlphaState state)).cursor <;>
            simp [alphaZeroOutputSlot?]
        simp [alphaNone]
      have nextInvariant : BidirectionalPreAnchorInvariant next.memory := by
        simpa [next, controller, bidirectionalFoldAlphaController,
          IndexedUnifiedExposureController.afterAnswer] using
          bidirectional_pre_anchor_invariant_step transitionFuel anchorIndex
            state record.answer beforeAnchor
              ⟨foldUnused, noWork, noBoundary, noProducers, noUsed⟩
      have nextAnchor : next.exposureIndex + records.length = anchorIndex := by
        simp only [next, indexed_after_answer_exposure_index,
          List.length_cons] at anchorExact ⊢
        omega
      have tailResidual := ih next nextAnchor nextInvariant
      change namedTraceSlots
        ((controller.preferredSlot state, record.answer) ::
          indexedControllerLabeledRecords transitionFuel controller next
            records) = []
      rw [preferredNone]
      exact tailResidual

/-- Once a boundary-first anchor has installed its missing work sibling,
any non-anchor exposure at a different literal input preserves that waiting
state.  Alpha producers and output-slot consumption remain unrestricted. -/
theorem bidirectional_waiting_for_work_step
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory)
    (answer : Digest256) (workInput : ShaInput)
    (notAnchor : state.exposureIndex ≠ anchorIndex)
    (inputAvoids : currentBidirectionalInput? transitionFuel state ≠
      some workInput)
    (waiting : BidirectionalWaitingForWork state.memory workInput) :
    BidirectionalWaitingForWork
      (bidirectionalFoldAlphaAfterMemory transitionFuel anchorIndex state
        answer) workInput := by
  have noMatch : ¬ matchesExpectedFoldWork
      (currentBidirectionalInput? transitionFuel state)
      state.memory.expectedWork := by
    intro matched
    rcases matched with ⟨input, currentExact, expectedExact⟩
    rw [waiting.2] at expectedExact
    have inputExact : workInput = input := Option.some.inj expectedExact
    subst input
    exact inputAvoids currentExact
  have noMatch' : ¬ matchesExpectedFoldWork
      (currentBidirectionalInput? transitionFuel state) (some workInput) := by
    simpa [waiting.2] using noMatch
  unfold BidirectionalWaitingForWork
  unfold bidirectionalFoldAlphaAfterMemory
  simp only [notAnchor, ↓reduceDIte]
  simp [waiting.1, waiting.2, noMatch']

/-- Before the selected pair anchor, one aligned machine-fresh record is
appended exactly to the nested causal machine cache. -/
theorem bidirectional_pre_anchor_seen_machine_step_exact
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory)
    (actor : QueryActor) (input : ShaInput) (answer : Digest256)
    (beforeAnchor : state.exposureIndex ≠ anchorIndex)
    (aligned : unifiedRecordAtAnswer transitionFuel state.cursor answer =
      .machineFresh actor input answer) :
    (bidirectionalFoldAlphaAfterMemory transitionFuel anchorIndex state
      answer).alpha.seenMachine =
        state.memory.alpha.seenMachine ++ [(input, answer)] := by
  have machineInput : unifiedMachineFreshInputBefore? transitionFuel
      state.cursor = some input := by
    unfold unifiedRecordAtAnswer at aligned
    unfold unifiedMachineFreshInputBefore?
    generalize requestExact : seekUnifiedExposure transitionFuel state.cursor =
      request at aligned ⊢
    cases request <;> simp_all
  have causalInput : currentBidirectionalInput? transitionFuel state =
      some input := by
    exact unified_machine_fresh_input_is_unified_input transitionFuel
      state.cursor input machineInput
  have unifiedInput : unifiedInputBeforeAnswer? transitionFuel state.cursor =
      some input := by
    simpa [currentBidirectionalInput?] using causalInput
  have projectedInput : unifiedInputBeforeAnswer? transitionFuel
      (bidirectionalAlphaState state).cursor = some input := by
    simpa [bidirectionalAlphaState] using unifiedInput
  unfold bidirectionalFoldAlphaAfterMemory
  simp only [beforeAnchor, ↓reduceDIte]
  by_cases consumes : state.memory.foldUsed = false ∧
      matchesExpectedFoldWork
        (currentBidirectionalInput? transitionFuel state)
        state.memory.expectedWork
  · rw [if_pos consumes]
    change (foldArmedAlphaAfterMemory transitionFuel
      (bidirectionalAlphaState state) answer).seenMachine = _
    unfold foldArmedAlphaAfterMemory
    rw [projectedInput]
    simp [bidirectionalAlphaState, rememberCurrentMachine, machineInput]
  · rw [if_neg consumes]
    change (foldArmedAlphaAfterMemory transitionFuel
      (bidirectionalAlphaState state) answer).seenMachine = _
    unfold foldArmedAlphaAfterMemory
    rw [projectedInput]
    simp [bidirectionalAlphaState, rememberCurrentMachine, machineInput]

/-- Exact machine-cache contents at every aligned machine-only prefix ending
at the selected pair anchor. -/
theorem bidirectional_pre_anchor_seen_machine_replay_exact
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        BidirectionalFoldAlphaMemory),
      IndexedRecordsAligned transitionFuel
        (bidirectionalFoldAlphaController transitionFuel anchorIndex)
        state records →
      OnlyMachineFreshRecords records →
      state.exposureIndex + records.length = anchorIndex →
      (indexedStateAfterRecords transitionFuel
        (bidirectionalFoldAlphaController transitionFuel anchorIndex)
        records state).memory.alpha.seenMachine =
          state.memory.alpha.seenMachine ++
            records.filterMap bidirectionalMachineFreshPair? := by
  intro records
  induction records with
  | nil =>
      intro state _aligned _only _endExact
      simp
  | cons record records ih =>
      intro state aligned onlyMachine endExact
      obtain ⟨actor, input, answer, recordExact⟩ :=
        onlyMachine record List.mem_cons_self
      subst record
      have headAligned := aligned []
        (.machineFresh actor input answer) records rfl
      have beforeAnchor : state.exposureIndex ≠ anchorIndex := by
        simp only [List.length_cons] at endExact
        omega
      let controller := bidirectionalFoldAlphaController
        (globalOracleCalls := globalOracleCalls) transitionFuel anchorIndex
      let next := controller.afterAnswer transitionFuel state answer
      have stepExact : next.memory.alpha.seenMachine =
          state.memory.alpha.seenMachine ++ [(input, answer)] := by
        simpa [next, controller, bidirectionalFoldAlphaController,
          IndexedUnifiedExposureController.afterAnswer] using
          bidirectional_pre_anchor_seen_machine_step_exact transitionFuel
            anchorIndex state actor input answer beforeAnchor headAligned
      have tailAligned : IndexedRecordsAligned transitionFuel controller next
          records := by
        apply indexed_records_aligned_segment transitionFuel controller state
          ((.machineFresh actor input answer) :: records)
          [(.machineFresh actor input answer)] records []
        · simpa [controller] using aligned
        · simp [next, UnifiedExposureRecord.answer]
      have tailOnly : OnlyMachineFreshRecords records := by
        intro tailRecord member
        exact onlyMachine tailRecord (List.mem_cons_of_mem _ member)
      have nextEnd : next.exposureIndex + records.length = anchorIndex := by
        simp only [next, controller, indexed_after_answer_exposure_index,
          List.length_cons] at endExact ⊢
        omega
      rw [indexed_state_after_records_cons]
      change (indexedStateAfterRecords transitionFuel controller records
        next).memory.alpha.seenMachine = _
      rw [ih next tailAligned tailOnly nextEnd, stepExact]
      simp [List.append_assoc, bidirectionalMachineFreshPair?]

end

#print axioms inactive_bidirectional_pre_anchor
#print axioms bidirectional_pre_anchor_invariant_step
#print axioms bidirectional_pre_anchor_invariant_replay
#print axioms bidirectional_labeled_records_before_anchor_all_residual
#print axioms bidirectional_waiting_for_work_step
#print axioms bidirectional_pre_anchor_seen_machine_step_exact
#print axioms bidirectional_pre_anchor_seen_machine_replay_exact

end AspisK1.V7Tag73BidirectionalFoldAlphaPrefix
