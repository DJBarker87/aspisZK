import AspisFormal.K1.V7Tag73IndexedControllerLabeledRecords
import AspisFormal.K1.V7Tag73RestoredQueryBatchForkController

/-!
# One-shot labels for the restoration-native query-batch controller

The waiting controller labels the first typed restored query-batch fork and
then follows the bounded duplex chain.  This file proves that every named
slot is used at most once on every answer stream.  The first fork output is
tracked explicitly because the controller's ordinary chain memory is not
initialized until the adjacent advance answer arrives.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73RestoredQueryBatchLabelsNodup

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalMachineLabeledTraceRouting
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedControllerLabeledRecords
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73RestoredQueryBatchForkController
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def firstOutputSlot : GammaPrefixDigestSlot := (⟨0, by decide⟩, false)
def firstAdvanceSlot : GammaPrefixDigestSlot := (⟨0, by decide⟩, true)

/-- Logical consumed-slot set.  During `firstAdvance`, block-zero output has
already been consumed even though the ordinary chain memory is still empty. -/
def waitingLogicalUsedSlots :
    WaitingRestoredQueryBatchMemory → Finset GammaPrefixDigestSlot
  | .waiting => ∅
  | .active memory =>
      match memory.phase with
      | .firstOutput => memory.chain.usedSlots
      | .firstAdvance _ => insert firstOutputSlot memory.chain.usedSlots
      | .continuation => memory.chain.usedSlots

/-- Reachability invariant for the small phase machine. -/
def waitingMemoryWellFormed :
    WaitingRestoredQueryBatchMemory → Prop
  | .waiting => True
  | .active memory =>
      match memory.phase with
      | .firstOutput => memory.chain.usedSlots = ∅
      | .firstAdvance _ => memory.chain.usedSlots = ∅
      | .continuation => firstPairUsedSlots ⊆ memory.chain.usedSlots

@[simp] theorem waiting_well_formed :
    waitingMemoryWellFormed .waiting := by
  trivial

theorem restored_candidate_preferred_fresh
    (memory : QueryBatchPrefixControllerMemory) (input : ShaInput)
    (slot : GammaPrefixDigestSlot)
    (preferred : restoredQueryBatchCandidateForInput memory input = some slot) :
    slot ∉ memory.usedSlots := by
  unfold restoredQueryBatchCandidateForInput at preferred
  cases candidateExact :
      ((queryBatchPrefixOutputSlot? memory.producers input).or
        (queryBatchPrefixAdvanceSlot? memory.producers input)) with
  | none => simp [candidateExact] at preferred
  | some candidate =>
      by_cases used : candidate ∈ memory.usedSlots
      · simp [candidateExact, used] at preferred
      · have exact : candidate = slot := by
          simpa [candidateExact, used] using preferred
        simpa [← exact] using used

theorem waiting_restored_query_batch_preferred_fresh
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (startsHere : UnifiedExposureCursor globalOracleCalls → Bool)
    (state : IndexedUnifiedExposureState globalOracleCalls
      WaitingRestoredQueryBatchMemory)
    (wellFormed : waitingMemoryWellFormed state.memory)
    (slot : GammaPrefixDigestSlot)
    (preferred :
      (waitingRestoredQueryBatchForkController transitionFuel startsHere).preferredSlot
        state = some slot) :
    slot ∉ waitingLogicalUsedSlots state.memory := by
  rcases state with ⟨exposureIndex, cursor, stateMemory⟩
  cases stateMemory with
  | waiting =>
      simp [waitingLogicalUsedSlots]
  | active memory =>
      cases phaseExact : memory.phase with
      | firstOutput =>
          have empty : memory.chain.usedSlots = ∅ := by
            simpa [waitingMemoryWellFormed, phaseExact] using wellFormed
          simp [waitingLogicalUsedSlots, phaseExact, empty]
      | firstAdvance output =>
          have empty : memory.chain.usedSlots = ∅ := by
            simpa [waitingMemoryWellFormed, phaseExact] using wellFormed
          have slotExact : slot = firstAdvanceSlot := by
            simpa [waitingRestoredQueryBatchForkController,
              restoredQueryBatchForkController,
              RestoredQueryBatchForkMemory.preferredSlot,
              activeRestoredQueryBatchState, phaseExact,
              firstAdvanceSlot] using preferred.symm
          subst slot
          simp [waitingLogicalUsedSlots, phaseExact, empty,
            firstOutputSlot, firstAdvanceSlot]
      | continuation =>
          simp only [waitingRestoredQueryBatchForkController,
            activeRestoredQueryBatchState, restoredQueryBatchForkController,
            RestoredQueryBatchForkMemory.preferredSlot, phaseExact] at preferred
          cases inputExact : unifiedInputBeforeAnswer? transitionFuel
              cursor with
          | none => simp [inputExact] at preferred
          | some input =>
              have fresh := restored_candidate_preferred_fresh memory.chain
                input slot (by simpa [inputExact] using preferred)
              simpa [waitingLogicalUsedSlots, phaseExact] using fresh

/-- The logical used set is monotone across every controller answer. -/
theorem waiting_restored_query_batch_used_slots_mono
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (startsHere : UnifiedExposureCursor globalOracleCalls → Bool)
    (state : IndexedUnifiedExposureState globalOracleCalls
      WaitingRestoredQueryBatchMemory)
    (wellFormed : waitingMemoryWellFormed state.memory)
    (answer : Digest256) :
    waitingLogicalUsedSlots state.memory ⊆
      waitingLogicalUsedSlots
        ((waitingRestoredQueryBatchForkController transitionFuel
          startsHere).afterAnswer transitionFuel state answer).memory := by
  intro slot member
  rcases state with ⟨exposureIndex, cursor, stateMemory⟩
  cases stateMemory with
  | waiting =>
      simp [waitingLogicalUsedSlots] at member
  | active memory =>
      cases phaseExact : memory.phase with
      | firstOutput =>
          simp only [waitingRestoredQueryBatchForkController,
            IndexedUnifiedExposureController.afterAnswer,
            activeRestoredQueryBatchState, restoredQueryBatchForkController,
            RestoredQueryBatchForkMemory.afterAnswer, phaseExact]
          simp [waitingLogicalUsedSlots, phaseExact,
            firstOutputSlot] at member ⊢
          exact Or.inr member
      | firstAdvance output =>
          have empty : memory.chain.usedSlots = ∅ := by
            simpa [waitingMemoryWellFormed, phaseExact] using wellFormed
          have member' : slot = firstOutputSlot := by
            simpa [waitingLogicalUsedSlots, phaseExact, empty] using member
          simp only [waitingRestoredQueryBatchForkController,
            IndexedUnifiedExposureController.afterAnswer,
            activeRestoredQueryBatchState, restoredQueryBatchForkController,
            RestoredQueryBatchForkMemory.afterAnswer, phaseExact]
          simp [waitingLogicalUsedSlots,
            prefixAfterFirstPair, firstPairUsedSlots, firstOutputSlot,
            firstAdvanceSlot, empty]
          exact Or.inl (by simpa [firstOutputSlot] using member')
      | continuation =>
          have member' : slot ∈ memory.chain.usedSlots := by
            simpa [waitingLogicalUsedSlots, phaseExact] using member
          simp only [waitingRestoredQueryBatchForkController,
            IndexedUnifiedExposureController.afterAnswer,
            activeRestoredQueryBatchState, restoredQueryBatchForkController,
            RestoredQueryBatchForkMemory.afterAnswer, phaseExact]
          cases inputExact : unifiedInputBeforeAnswer? transitionFuel
              cursor with
          | none => simpa [inputExact, waitingLogicalUsedSlots,
              phaseExact] using member'
          | some input =>
              simp only [inputExact]
              cases candidateExact : restoredQueryBatchCandidateForInput
                  memory.chain input with
              | none => simpa [candidateExact, waitingLogicalUsedSlots,
                  phaseExact] using member'
              | some selected =>
                  simp only [candidateExact, waitingLogicalUsedSlots,
                    phaseExact]
                  exact Finset.mem_insert_of_mem member'

/-- Whenever the controller names the current answer, that slot is logically
used in the successor state. -/
theorem waiting_restored_query_batch_preferred_used_after_answer
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (startsHere : UnifiedExposureCursor globalOracleCalls → Bool)
    (state : IndexedUnifiedExposureState globalOracleCalls
      WaitingRestoredQueryBatchMemory)
    (answer : Digest256) (slot : GammaPrefixDigestSlot)
    (preferred :
      (waitingRestoredQueryBatchForkController transitionFuel startsHere).preferredSlot
        state = some slot) :
    slot ∈ waitingLogicalUsedSlots
      ((waitingRestoredQueryBatchForkController transitionFuel
        startsHere).afterAnswer transitionFuel state answer).memory := by
  rcases state with ⟨exposureIndex, cursor, stateMemory⟩
  cases stateMemory with
  | waiting =>
      by_cases marked : startsHere cursor = true
      · have slotExact : slot = firstOutputSlot := by
          simpa [waitingRestoredQueryBatchForkController, marked,
            firstOutputSlot] using preferred.symm
        subst slot
        simp [IndexedUnifiedExposureController.afterAnswer,
          waitingRestoredQueryBatchForkController, marked,
          restoredQueryBatchForkController,
          RestoredQueryBatchForkMemory.afterAnswer,
          initialRestoredQueryBatchForkMemory, waitingLogicalUsedSlots,
          firstOutputSlot]
      · have markedFalse : startsHere cursor = false :=
          Bool.eq_false_of_not_eq_true marked
        simp [waitingRestoredQueryBatchForkController, markedFalse]
          at preferred
  | active memory =>
      cases phaseExact : memory.phase with
      | firstOutput =>
          have slotExact : slot = firstOutputSlot := by
            simpa [waitingRestoredQueryBatchForkController,
              restoredQueryBatchForkController,
              activeRestoredQueryBatchState,
              RestoredQueryBatchForkMemory.preferredSlot, phaseExact,
              firstOutputSlot] using preferred.symm
          subst slot
          simp [waitingRestoredQueryBatchForkController,
            IndexedUnifiedExposureController.afterAnswer,
            activeRestoredQueryBatchState, restoredQueryBatchForkController,
            RestoredQueryBatchForkMemory.afterAnswer, phaseExact,
            waitingLogicalUsedSlots, firstOutputSlot]
      | firstAdvance output =>
          have slotExact : slot = firstAdvanceSlot := by
            simpa [waitingRestoredQueryBatchForkController,
              restoredQueryBatchForkController,
              activeRestoredQueryBatchState,
              RestoredQueryBatchForkMemory.preferredSlot, phaseExact,
              firstAdvanceSlot] using preferred.symm
          subst slot
          simp [waitingRestoredQueryBatchForkController,
            IndexedUnifiedExposureController.afterAnswer,
            activeRestoredQueryBatchState, restoredQueryBatchForkController,
            RestoredQueryBatchForkMemory.afterAnswer, phaseExact,
            waitingLogicalUsedSlots, prefixAfterFirstPair,
            firstPairUsedSlots, firstOutputSlot, firstAdvanceSlot]
      | continuation =>
          simp only [waitingRestoredQueryBatchForkController,
            restoredQueryBatchForkController,
            activeRestoredQueryBatchState,
            RestoredQueryBatchForkMemory.preferredSlot, phaseExact]
            at preferred
          cases inputExact : unifiedInputBeforeAnswer? transitionFuel
              cursor with
          | none => simp [inputExact] at preferred
          | some input =>
              simp only [inputExact] at preferred
              cases candidateExact : restoredQueryBatchCandidateForInput
                  memory.chain input with
              | none => simp [candidateExact] at preferred
              | some selected =>
                  have selectedExact : selected = slot := by
                    simpa [candidateExact] using preferred
                  subst selected
                  simp [waitingRestoredQueryBatchForkController,
                    IndexedUnifiedExposureController.afterAnswer,
                    activeRestoredQueryBatchState,
                    restoredQueryBatchForkController,
                    RestoredQueryBatchForkMemory.afterAnswer, phaseExact,
                    inputExact, candidateExact, waitingLogicalUsedSlots]

/-- Every answer preserves reachability of the controller phase memory. -/
theorem waiting_restored_query_batch_well_formed_after_answer
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (startsHere : UnifiedExposureCursor globalOracleCalls → Bool)
    (state : IndexedUnifiedExposureState globalOracleCalls
      WaitingRestoredQueryBatchMemory)
    (wellFormed : waitingMemoryWellFormed state.memory)
    (answer : Digest256) :
    waitingMemoryWellFormed
      ((waitingRestoredQueryBatchForkController transitionFuel
        startsHere).afterAnswer transitionFuel state answer).memory := by
  rcases state with ⟨exposureIndex, cursor, stateMemory⟩
  cases stateMemory with
  | waiting =>
      by_cases marked : startsHere cursor = true
      · simp [waitingRestoredQueryBatchForkController, marked,
          IndexedUnifiedExposureController.afterAnswer,
          restoredQueryBatchForkController,
          RestoredQueryBatchForkMemory.afterAnswer,
          initialRestoredQueryBatchForkMemory, inactiveQueryBatchPrefixMemory,
          waitingMemoryWellFormed]
      · have markedFalse : startsHere cursor = false :=
          Bool.eq_false_of_not_eq_true marked
        simp [waitingRestoredQueryBatchForkController, markedFalse,
          IndexedUnifiedExposureController.afterAnswer,
          waitingMemoryWellFormed]
  | active memory =>
      cases phaseExact : memory.phase with
      | firstOutput =>
          have empty : memory.chain.usedSlots = ∅ := by
            simpa [waitingMemoryWellFormed, phaseExact] using wellFormed
          simpa [waitingRestoredQueryBatchForkController,
            IndexedUnifiedExposureController.afterAnswer,
            activeRestoredQueryBatchState, restoredQueryBatchForkController,
            RestoredQueryBatchForkMemory.afterAnswer, phaseExact,
            waitingMemoryWellFormed] using empty
      | firstAdvance output =>
          simp [waitingRestoredQueryBatchForkController,
            IndexedUnifiedExposureController.afterAnswer,
            activeRestoredQueryBatchState, restoredQueryBatchForkController,
            RestoredQueryBatchForkMemory.afterAnswer, phaseExact,
            waitingMemoryWellFormed, prefixAfterFirstPair,
            firstPairUsedSlots]
      | continuation =>
          have contained : firstPairUsedSlots ⊆ memory.chain.usedSlots := by
            simpa [waitingMemoryWellFormed, phaseExact] using wellFormed
          simp only [waitingRestoredQueryBatchForkController,
            IndexedUnifiedExposureController.afterAnswer,
            activeRestoredQueryBatchState, restoredQueryBatchForkController,
            RestoredQueryBatchForkMemory.afterAnswer, phaseExact]
          cases inputExact : unifiedInputBeforeAnswer? transitionFuel
              cursor with
          | none => simpa [inputExact, phaseExact,
              waitingMemoryWellFormed] using contained
          | some input =>
              simp only [inputExact]
              cases candidateExact : restoredQueryBatchCandidateForInput
                  memory.chain input with
              | none => simpa [candidateExact, phaseExact,
                  waitingMemoryWellFormed] using contained
              | some selected =>
                  simp only [candidateExact, waitingMemoryWellFormed,
                    phaseExact]
                  exact fun slot member ↦ Finset.mem_insert_of_mem
                    (contained member)

/-- Named labels are distinct and avoid every slot logically consumed before
the segment. -/
theorem waiting_restored_query_batch_labeled_records_nodup_and_avoid_initial
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (startsHere : UnifiedExposureCursor globalOracleCalls → Bool) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        WaitingRestoredQueryBatchMemory),
      waitingMemoryWellFormed state.memory →
      let controller := waitingRestoredQueryBatchForkController transitionFuel
        startsHere
      let labels := indexedControllerLabeledRecords transitionFuel controller
        state records
      (namedTraceSlots labels).Nodup ∧
        ∀ slot ∈ namedTraceSlots labels,
          slot ∉ waitingLogicalUsedSlots state.memory := by
  intro records
  induction records with
  | nil =>
      intro state wellFormed
      simp [indexedControllerLabeledRecords]
  | cons record records ih =>
      intro state wellFormed
      let controller := waitingRestoredQueryBatchForkController transitionFuel
        startsHere
      let next := controller.afterAnswer transitionFuel state record.answer
      have nextWellFormed : waitingMemoryWellFormed next.memory :=
        waiting_restored_query_batch_well_formed_after_answer transitionFuel
          startsHere state wellFormed record.answer
      have tail := ih next nextWellFormed
      have usedMono : waitingLogicalUsedSlots state.memory ⊆
          waitingLogicalUsedSlots next.memory :=
        waiting_restored_query_batch_used_slots_mono transitionFuel startsHere
          state wellFormed record.answer
      change
        (namedTraceSlots
          (indexedControllerLabeledRecords transitionFuel controller state
            (record :: records))).Nodup ∧
          ∀ slot ∈ namedTraceSlots
            (indexedControllerLabeledRecords transitionFuel controller state
              (record :: records)),
            slot ∉ waitingLogicalUsedSlots state.memory
      cases preferred : controller.preferredSlot state with
      | none =>
          simp only [indexedControllerLabeledRecords, preferred,
            namedTraceSlots]
          exact And.intro tail.1
            (fun slot member used ↦ tail.2 slot member (usedMono used))
      | some slot =>
          have slotFresh : slot ∉ waitingLogicalUsedSlots state.memory :=
            waiting_restored_query_batch_preferred_fresh transitionFuel
              startsHere state wellFormed slot preferred
          have nextUsed : slot ∈ waitingLogicalUsedSlots next.memory := by
            exact waiting_restored_query_batch_preferred_used_after_answer
              transitionFuel startsHere state record.answer slot preferred
          have slotNotTail : slot ∉ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records) := by
            intro member
            exact tail.2 slot member nextUsed
          have tailAvoidsInitial : ∀ candidate ∈ namedTraceSlots
              (indexedControllerLabeledRecords transitionFuel controller next
                records), candidate ∉ waitingLogicalUsedSlots state.memory := by
            intro candidate member used
            exact tail.2 candidate member (usedMono used)
          simp only [indexedControllerLabeledRecords, preferred,
            namedTraceSlots]
          constructor
          · exact List.nodup_cons.mpr ⟨slotNotTail, tail.1⟩
          · intro candidate member
            simp only [List.mem_cons] at member
            rcases member with equal | tailMember
            · subst candidate
              exact slotFresh
            · exact tailAvoidsInitial candidate tailMember

theorem waiting_restored_query_batch_labeled_records_named_slots_nodup
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (startsHere : UnifiedExposureCursor globalOracleCalls → Bool)
    (records : List UnifiedExposureRecord)
    (cursor : UnifiedExposureCursor globalOracleCalls) :
    (namedTraceSlots
      (indexedControllerLabeledRecords transitionFuel
        (waitingRestoredQueryBatchForkController transitionFuel startsHere)
        { exposureIndex := 0
          cursor := cursor
          memory := .waiting }
        records)).Nodup :=
  (waiting_restored_query_batch_labeled_records_nodup_and_avoid_initial
    transitionFuel startsHere records
      { exposureIndex := 0, cursor := cursor, memory := .waiting }
      waiting_well_formed).1

#print axioms waitingLogicalUsedSlots
#print axioms waitingMemoryWellFormed
#print axioms restored_candidate_preferred_fresh
#print axioms waiting_restored_query_batch_preferred_fresh
#print axioms waiting_restored_query_batch_used_slots_mono
#print axioms waiting_restored_query_batch_well_formed_after_answer
#print axioms waiting_restored_query_batch_labeled_records_named_slots_nodup

end
end AspisK1.V7Tag73RestoredQueryBatchLabelsNodup
