import AspisFormal.K1.V7Tag73BidirectionalFoldAlphaPrefix
import AspisFormal.K1.V7Tag73IndexedControllerLabeledRecords

/-!
# One-shot inventory for the bidirectional fold/alpha controller

The fold answer and four alpha output blocks share one five-element slot
space.  This file records the controller's two internal one-shot fields as
one finite set and proves that every emitted label is inserted exactly once.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73BidirectionalFoldAlphaOneShot

open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73BidirectionalFoldAlphaController
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73FoldArmedAlphaZeroController
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The fold coordinate is `none`; alpha block `i` is `some i`. -/
def bidirectionalUsedSlots (memory : BidirectionalFoldAlphaMemory) :
    Finset FoldOneFoldDigestSlot :=
  (if memory.foldUsed then {none} else ∅) ∪
    memory.alpha.alpha.usedSlots.image some

@[simp] theorem fold_mem_bidirectional_used_slots
    (memory : BidirectionalFoldAlphaMemory) :
    none ∈ bidirectionalUsedSlots memory ↔ memory.foldUsed = true := by
  cases exact : memory.foldUsed <;> simp [bidirectionalUsedSlots, exact]

@[simp] theorem alpha_mem_bidirectional_used_slots
    (memory : BidirectionalFoldAlphaMemory) (slot : Fin 4) :
    some slot ∈ bidirectionalUsedSlots memory ↔
      slot ∈ memory.alpha.alpha.usedSlots := by
  cases exact : memory.foldUsed <;> simp [bidirectionalUsedSlots, exact]

theorem alpha_zero_preferred_slot_fresh
    {globalOracleCalls : Nat}
    (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (slot : Fin 4)
    (preferred : alphaZeroPreferredSlot transitionFuel state = some slot) :
    slot ∉ state.memory.usedSlots := by
  unfold alphaZeroPreferredSlot at preferred
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => simp [inputExact] at preferred
  | some input =>
      cases output : alphaZeroOutputSlot? state.memory.producers input with
      | none => simp [inputExact, output] at preferred
      | some outputSlot =>
          by_cases used : outputSlot ∈ state.memory.usedSlots
          · simp [inputExact, output, used] at preferred
          · have exactSlot : outputSlot = slot := by
              simpa [inputExact, output, used] using preferred
            simpa [← exactSlot] using used

/-- Any label selected before an answer is absent from the complete one-shot
inventory at that pause. -/
theorem bidirectional_preferred_slot_fresh
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory)
    (slot : FoldOneFoldDigestSlot)
    (preferred :
      bidirectionalFoldAlphaPreferred transitionFuel anchorIndex state =
        some slot) :
    slot ∉ bidirectionalUsedSlots state.memory := by
  unfold bidirectionalFoldAlphaPreferred at preferred
  dsimp only at preferred
  by_cases atAnchor : state.exposureIndex = anchorIndex
  · simp only [atAnchor, ↓reduceDIte] at preferred
    cases current : currentBidirectionalInput? transitionFuel state with
    | none => simp [current] at preferred
    | some input =>
        simp only [current, Option.bind_some] at preferred
        unfold foldCandidateAnchorKind? at preferred
        cases workParse : foldWorkInputToAlphaBoundary? input with
        | some boundary =>
            by_cases unused : state.memory.foldUsed = false
            · simp [workParse, unused] at preferred
              subst slot
              simp [bidirectionalUsedSlots, unused]
            · simp [workParse, unused] at preferred
        | none =>
            cases boundaryParse : alphaBoundaryInputToFoldWork? input <;>
              simp [workParse, boundaryParse] at preferred
  · simp only [atAnchor, ↓reduceDIte] at preferred
    by_cases consumesWork : state.memory.foldUsed = false ∧
        matchesExpectedFoldWork
          (currentBidirectionalInput? transitionFuel state)
          state.memory.expectedWork
    · rw [if_pos consumesWork] at preferred
      have slotExact : slot = none := (Option.some.inj preferred).symm
      subst slot
      simp [bidirectionalUsedSlots, consumesWork.1]
    · rw [if_neg consumesWork] at preferred
      cases alphaPreferred : alphaZeroPreferredSlot transitionFuel
          (foldArmedAlphaIndexedState (bidirectionalAlphaState state)) with
      | none => simp [alphaPreferred] at preferred
      | some alphaSlot =>
          simp only [alphaPreferred, Option.map_some] at preferred
          have exactSlot : some alphaSlot = slot := Option.some.inj preferred
          subst slot
          rw [alpha_mem_bidirectional_used_slots]
          exact alpha_zero_preferred_slot_fresh transitionFuel
            (foldArmedAlphaIndexedState (bidirectionalAlphaState state))
            alphaSlot alphaPreferred

/-- Consuming one answer inserts exactly its selected label into the combined
inventory and otherwise leaves that inventory unchanged. -/
theorem bidirectional_after_memory_used_slots
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory)
    (answer : Digest256) :
    bidirectionalUsedSlots
        (bidirectionalFoldAlphaAfterMemory transitionFuel anchorIndex state
          answer) =
      match bidirectionalFoldAlphaPreferred transitionFuel anchorIndex state with
      | some slot => insert slot (bidirectionalUsedSlots state.memory)
      | none => bidirectionalUsedSlots state.memory := by
  unfold bidirectionalFoldAlphaAfterMemory
  unfold bidirectionalFoldAlphaPreferred
  dsimp only
  by_cases atAnchor : state.exposureIndex = anchorIndex
  · simp only [atAnchor, if_pos]
    cases current : currentBidirectionalInput? transitionFuel state with
    | none => simp [current]
    | some input =>
        unfold foldCandidateAnchorKind?
        cases workParse : foldWorkInputToAlphaBoundary? input with
        | some boundary =>
            by_cases unused : state.memory.foldUsed = false <;>
              simp [current, workParse, unused, bidirectionalUsedSlots,
                arm_fold_alpha_memory_used_slots, bidirectionalAlphaState]
        | none =>
            cases boundaryParse : alphaBoundaryInputToFoldWork? input with
            | none => simp [current, workParse, boundaryParse]
            | some work =>
                simp [current, workParse, boundaryParse,
                  bidirectionalUsedSlots, installBoundaryAnchor]
  · simp only [atAnchor, ↓reduceDIte]
    let alphaState := foldArmedAlphaIndexedState
      (bidirectionalAlphaState state)
    have rawUsed := fold_armed_alpha_after_memory_used_slots transitionFuel
      (bidirectionalAlphaState state) answer
    by_cases consumesWork : state.memory.foldUsed = false ∧
        matchesExpectedFoldWork
          (currentBidirectionalInput? transitionFuel state)
          state.memory.expectedWork
    · have foldFalse : state.memory.foldUsed = false := consumesWork.1
      simp only [consumesWork, if_pos]
      simp [consumesWork, bidirectionalUsedSlots, foldFalse,
        bidirectionalAlphaState]
    · simp only [consumesWork, if_neg, if_false, decide_false,
        Bool.or_false, Option.map_none, Option.map_some]
      dsimp [alphaState, bidirectionalAlphaState,
        foldArmedAlphaIndexedState] at rawUsed
      cases alphaPreferred : alphaZeroPreferredSlot transitionFuel alphaState with
      | none =>
          simp [alphaState, bidirectionalAlphaState,
            foldArmedAlphaIndexedState] at alphaPreferred
          rw [alphaPreferred] at rawUsed
          have mapped := congrArg
            (fun used : Finset (Fin 4) =>
              (if state.memory.foldUsed then
                ({none} : Finset FoldOneFoldDigestSlot) else ∅) ∪
                used.image some) rawUsed
          simpa [bidirectionalUsedSlots, alphaPreferred, alphaState,
            bidirectionalAlphaState, foldArmedAlphaIndexedState] using mapped
      | some slot =>
          simp [alphaState, bidirectionalAlphaState,
            foldArmedAlphaIndexedState] at alphaPreferred
          rw [alphaPreferred] at rawUsed
          have mapped := congrArg
            (fun used : Finset (Fin 4) =>
              (if state.memory.foldUsed then
                ({none} : Finset FoldOneFoldDigestSlot) else ∅) ∪
                used.image some) rawUsed
          simpa [bidirectionalUsedSlots, alphaPreferred, alphaState,
            bidirectionalAlphaState, foldArmedAlphaIndexedState,
            Finset.image_insert, Finset.insert_union] using mapped

/-- The combined inventory is monotone across one answer. -/
theorem bidirectional_used_slots_mono
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory)
    (answer : Digest256) :
    bidirectionalUsedSlots state.memory ⊆
      bidirectionalUsedSlots
        (bidirectionalFoldAlphaAfterMemory transitionFuel anchorIndex state
          answer) := by
  rw [bidirectional_after_memory_used_slots]
  split
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.rfl

/-- Every named label emitted over an arbitrary answer stream is distinct,
and every emitted label was unused at the start of that stream. -/
theorem bidirectional_labeled_records_nodup_and_avoid_initial
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        BidirectionalFoldAlphaMemory),
      let labels := indexedControllerLabeledRecords transitionFuel
        (bidirectionalFoldAlphaController transitionFuel anchorIndex)
        state records
      (namedTraceSlots labels).Nodup ∧
        ∀ slot ∈ namedTraceSlots labels,
          slot ∉ bidirectionalUsedSlots state.memory := by
  intro records
  induction records with
  | nil =>
      intro state
      simp [indexedControllerLabeledRecords, namedTraceSlots]
  | cons record records ih =>
      intro state
      let controller := bidirectionalFoldAlphaController
        (globalOracleCalls := globalOracleCalls) transitionFuel anchorIndex
      let next := controller.afterAnswer transitionFuel state record.answer
      have tail := ih next
      have usedMono : bidirectionalUsedSlots state.memory ⊆
          bidirectionalUsedSlots next.memory := by
        simpa [next, controller, bidirectionalFoldAlphaController,
          IndexedUnifiedExposureController.afterAnswer] using
          bidirectional_used_slots_mono transitionFuel anchorIndex state
            record.answer
      cases preferred : controller.preferredSlot state with
      | none =>
          simpa [indexedControllerLabeledRecords, controller, next, preferred,
            namedTraceSlots] using
            And.intro tail.1 (fun slot member used =>
              tail.2 slot member (usedMono used))
      | some slot =>
          have preferred' : bidirectionalFoldAlphaPreferred transitionFuel
              anchorIndex state = some slot := by
            simpa [controller, bidirectionalFoldAlphaController] using preferred
          have slotFresh : slot ∉ bidirectionalUsedSlots state.memory :=
            bidirectional_preferred_slot_fresh transitionFuel anchorIndex state
              slot preferred'
          have slotUsed : slot ∈ bidirectionalUsedSlots next.memory := by
            change slot ∈ bidirectionalUsedSlots
              (bidirectionalFoldAlphaAfterMemory transitionFuel anchorIndex
                state record.answer)
            rw [bidirectional_after_memory_used_slots, preferred']
            exact Finset.mem_insert_self slot _
          have slotNotTail : slot ∉ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records) := by
            intro member
            exact tail.2 slot member slotUsed
          have tailAvoidsInitial : ∀ candidate ∈ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records), candidate ∉ bidirectionalUsedSlots state.memory := by
            intro candidate member used
            exact tail.2 candidate member (usedMono used)
          simpa [indexedControllerLabeledRecords, controller, next, preferred,
            namedTraceSlots] using
            And.intro (List.nodup_cons.mpr ⟨slotNotTail, tail.1⟩)
              ⟨slotFresh, tailAvoidsInitial⟩

theorem bidirectional_labeled_records_named_slots_nodup
    {globalOracleCalls : Nat}
    (transitionFuel anchorIndex : Nat)
    (records : List UnifiedExposureRecord)
    (state : IndexedUnifiedExposureState globalOracleCalls
      BidirectionalFoldAlphaMemory) :
    (namedTraceSlots
      (indexedControllerLabeledRecords transitionFuel
        (bidirectionalFoldAlphaController transitionFuel anchorIndex)
        state records)).Nodup :=
  (bidirectional_labeled_records_nodup_and_avoid_initial
    transitionFuel anchorIndex records state).1

end

#print axioms fold_mem_bidirectional_used_slots
#print axioms alpha_mem_bidirectional_used_slots
#print axioms bidirectional_preferred_slot_fresh
#print axioms bidirectional_after_memory_used_slots
#print axioms bidirectional_used_slots_mono
#print axioms bidirectional_labeled_records_nodup_and_avoid_initial
#print axioms bidirectional_labeled_records_named_slots_nodup

end AspisK1.V7Tag73BidirectionalFoldAlphaOneShot
