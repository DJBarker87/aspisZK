import AspisFormal.K1.V7Tag73BidirectionalFoldAlphaController

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
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73BidirectionalFoldAlphaController
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

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

end

#print axioms inactive_bidirectional_pre_anchor
#print axioms bidirectional_pre_anchor_invariant_step
#print axioms bidirectional_pre_anchor_invariant_replay
#print axioms bidirectional_waiting_for_work_step

end AspisK1.V7Tag73BidirectionalFoldAlphaPrefix
