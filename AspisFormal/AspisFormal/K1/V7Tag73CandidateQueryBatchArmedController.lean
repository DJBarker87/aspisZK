import AspisFormal.K1.V7Tag73CandidateDirectedQueryBatchController
import AspisFormal.K1.V7Tag73IndexedAlignedRecordReplay
import AspisFormal.K1.V7Tag73IndexedControllerTraceAlignment

/-!
# Post-boundary candidate query-batch controller

Once the fixed candidate boundary has been observed, the q16 observer and the
arming test are irrelevant to query-batch routing.  This small projection
isolates the exact producer/used-slot transition followed by the remaining
duplex chain and avoids carrying the complete fold/alpha/q16 product through
the local invariant proof.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CandidateQueryBatchArmedController

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def armedQueryBatchAfterInput
    (memory : QueryBatchPrefixControllerMemory)
    (input : ShaInput) (answer : Digest256) :
    QueryBatchPrefixControllerMemory :=
  let extension : QueryBatchDagExtensionMemory :=
    { q16 := emptyObservedQ16Duplex, queryBatch := memory }
  let preferred := queryBatchDagPreferredSlotForInput extension input
  let nextUsed :=
    match preferred with
    | none => memory.usedSlots
    | some slot => insert slot memory.usedSlots
  { boundarySeen := true
    producers := extendQueryBatchPrefixProducers memory.producers input answer
    usedSlots := nextUsed }

def armedQueryBatchPreferredSlot
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      QueryBatchPrefixControllerMemory) : Option GammaPrefixDigestSlot :=
  match unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => none
  | some input =>
      queryBatchDagPreferredSlotForInput
        { q16 := emptyObservedQ16Duplex, queryBatch := state.memory } input

def armedQueryBatchAfterMemory
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      QueryBatchPrefixControllerMemory)
    (answer : Digest256) : QueryBatchPrefixControllerMemory :=
  match unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => state.memory
  | some input => armedQueryBatchAfterInput state.memory input answer

def armedQueryBatchController
    {globalOracleCalls : Nat} (transitionFuel : Nat) :
    IndexedUnifiedExposureController globalOracleCalls Digest256
      GammaPrefixDigestSlot QueryBatchPrefixControllerMemory where
  preferredSlot := armedQueryBatchPreferredSlot transitionFuel
  afterMemory := armedQueryBatchAfterMemory transitionFuel

def queryBatchIndexedState
    {globalOracleCalls : Nat} {Memory : Type}
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory Memory)) :
    IndexedUnifiedExposureState globalOracleCalls
      QueryBatchPrefixControllerMemory :=
  { exposureIndex := state.exposureIndex
    cursor := state.cursor
    memory := state.memory.2.queryBatch }

/-- With the boundary already armed, one candidate-directed answer projects
exactly to the small post-boundary controller. -/
theorem query_batch_state_after_candidate_answer
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat) (target :
      AspisK1.V7Tag73CausalQ16CoordinateRouter.Q16DigestSlot)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory →
      AspisK1.V7Tag73CausalDagFinalWorkQ16Controller.FinalWorkQ16DagMemory)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory Memory))
    (answer : Digest256)
    (armed : state.memory.2.queryBatch.boundarySeen = true) :
    queryBatchIndexedState
        ((extendControllerThroughCandidateQueryBatch transitionFuel target base
          dagOf).afterAnswer transitionFuel state answer) =
      (armedQueryBatchController transitionFuel).afterAnswer transitionFuel
        (queryBatchIndexedState state) answer := by
  rcases state with ⟨exposureIndex, cursor, memory⟩
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel cursor with
  | none =>
      simp [queryBatchIndexedState,
        IndexedUnifiedExposureController.afterAnswer,
        extendControllerThroughCandidateQueryBatch,
        armedQueryBatchController, armedQueryBatchAfterMemory, inputExact]
  | some input =>
      have armed' : memory.2.queryBatch.boundarySeen = true := by
        simpa using armed
      simp [queryBatchIndexedState,
        IndexedUnifiedExposureController.afterAnswer,
        extendControllerThroughCandidateQueryBatch,
        candidateDirectedQueryBatchAfterInput,
        armedQueryBatchController, armedQueryBatchAfterMemory,
        armedQueryBatchAfterInput, queryBatchDagPreferredSlotForInput,
        inputExact, armed']
      rfl

theorem armed_query_batch_boundary_seen_after_input
    (memory : QueryBatchPrefixControllerMemory)
    (input : ShaInput) (answer : Digest256) :
    (armedQueryBatchAfterInput memory input answer).boundarySeen = true := by
  simp [armedQueryBatchAfterInput]

theorem armed_query_batch_boundary_seen_after_answer
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      QueryBatchPrefixControllerMemory)
    (answer : Digest256)
    (armed : state.memory.boundarySeen = true) :
    ((armedQueryBatchController transitionFuel).afterAnswer transitionFuel
      state answer).memory.boundarySeen = true := by
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => simpa [armedQueryBatchController,
      IndexedUnifiedExposureController.afterAnswer, armedQueryBatchAfterMemory,
      inputExact] using armed
  | some input => simp [armedQueryBatchController,
      IndexedUnifiedExposureController.afterAnswer, armedQueryBatchAfterMemory,
      inputExact, armedQueryBatchAfterInput]

/-- Exact one-step used-set update induced by the armed controller's
pre-answer label. -/
theorem armed_query_batch_after_memory_used_slots
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      QueryBatchPrefixControllerMemory)
    (answer : Digest256) :
    (armedQueryBatchAfterMemory transitionFuel state answer).usedSlots =
      match armedQueryBatchPreferredSlot transitionFuel state with
      | some slot => insert slot state.memory.usedSlots
      | none => state.memory.usedSlots := by
  unfold armedQueryBatchAfterMemory armedQueryBatchPreferredSlot
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => rfl
  | some input =>
      simp only [inputExact]
      generalize preferredExact : queryBatchDagPreferredSlotForInput
        { q16 := emptyObservedQ16Duplex, queryBatch := state.memory } input =
          preferred
      cases preferred <;>
        simp [armedQueryBatchAfterInput, preferredExact]

/-- Every slot newly present after an armed replay prefix was selected at one
literal earlier pre-answer state in that prefix. -/
theorem armed_query_batch_used_slot_has_prior_record
    {globalOracleCalls : Nat} (transitionFuel : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        QueryBatchPrefixControllerMemory) (slot : GammaPrefixDigestSlot),
      slot ∉ state.memory.usedSlots →
      slot ∈
        (indexedStateAfterRecords transitionFuel
          (armedQueryBatchController transitionFuel) records state).memory.usedSlots →
      ∃ prior record later,
        records = prior ++ record :: later ∧
        (armedQueryBatchController transitionFuel).preferredSlot
          (indexedStateAfterRecords transitionFuel
            (armedQueryBatchController transitionFuel) prior state) = some slot := by
  intro records
  induction records with
  | nil =>
      intro state slot fresh used
      simp only [indexed_state_after_records_nil] at used
      exact (fresh used).elim
  | cons head tail ih =>
      intro state slot fresh used
      let controller := armedQueryBatchController
        (globalOracleCalls := globalOracleCalls) transitionFuel
      let next := controller.afterAnswer transitionFuel state head.answer
      have tailUsed : slot ∈
          (indexedStateAfterRecords transitionFuel controller tail
            next).memory.usedSlots := by
        simpa [controller, next, indexed_state_after_records_cons] using used
      cases preferred : controller.preferredSlot state with
      | none =>
          have preferred' : armedQueryBatchPreferredSlot transitionFuel state =
              none := by
            simpa [controller, armedQueryBatchController] using preferred
          have nextFresh : slot ∉ next.memory.usedSlots := by
            have nextUsed := armed_query_batch_after_memory_used_slots
              transitionFuel state head.answer
            rw [show next.memory.usedSlots = state.memory.usedSlots by
              simpa [next, controller, armedQueryBatchController,
                IndexedUnifiedExposureController.afterAnswer, preferred'] using
                nextUsed]
            exact fresh
          obtain ⟨prior, record, later, decomposition, selected⟩ :=
            ih next slot nextFresh tailUsed
          refine ⟨head :: prior, record, later, ?_, ?_⟩
          · simp [decomposition]
          · simpa [controller, next, indexed_state_after_records_cons] using
              selected
      | some current =>
          have preferred' : armedQueryBatchPreferredSlot transitionFuel state =
              some current := by
            simpa [controller, armedQueryBatchController] using preferred
          by_cases currentExact : current = slot
          · subst current
            exact ⟨[], head, tail, by simp, by
              simpa [controller, indexed_state_after_records_nil] using
                preferred⟩
          · have nextFresh : slot ∉ next.memory.usedSlots := by
              have nextUsed := armed_query_batch_after_memory_used_slots
                transitionFuel state head.answer
              rw [show next.memory.usedSlots =
                  insert current state.memory.usedSlots by
                simpa [next, controller, armedQueryBatchController,
                  IndexedUnifiedExposureController.afterAnswer, preferred']
                  using nextUsed]
              have slotNe : slot ≠ current := fun equal =>
                currentExact equal.symm
              simp [fresh, slotNe]
            obtain ⟨prior, record, later, decomposition, selected⟩ :=
              ih next slot nextFresh tailUsed
            refine ⟨head :: prior, record, later, ?_, ?_⟩
            · simp [decomposition]
            · simpa [controller, next, indexed_state_after_records_cons] using
                selected

/-- The projection commutes across every later record while the boundary is
armed. -/
theorem query_batch_state_after_candidate_records
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat)
    (target : AspisK1.V7Tag73CausalQ16CoordinateRouter.Q16DigestSlot)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory →
      AspisK1.V7Tag73CausalDagFinalWorkQ16Controller.FinalWorkQ16DagMemory) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (ExtendedControllerMemory Memory)),
      state.memory.2.queryBatch.boundarySeen = true →
      queryBatchIndexedState
          (indexedStateAfterRecords transitionFuel
            (extendControllerThroughCandidateQueryBatch transitionFuel target
              base dagOf) records state) =
        indexedStateAfterRecords transitionFuel
          (armedQueryBatchController transitionFuel) records
          (queryBatchIndexedState state) := by
  intro records
  induction records with
  | nil => intro state _armed; rfl
  | cons record records ih =>
      intro state armed
      rw [indexed_state_after_records_cons, indexed_state_after_records_cons]
      let nextFull :=
        (extendControllerThroughCandidateQueryBatch transitionFuel target base
          dagOf).afterAnswer transitionFuel state record.answer
      let nextSmall := (armedQueryBatchController transitionFuel).afterAnswer
        transitionFuel (queryBatchIndexedState state) record.answer
      have projected : queryBatchIndexedState nextFull = nextSmall := by
        simpa [nextFull, nextSmall] using
          query_batch_state_after_candidate_answer transitionFuel target base
            dagOf state record.answer armed
      have smallArmed : nextSmall.memory.boundarySeen = true := by
        simpa [nextSmall] using
          armed_query_batch_boundary_seen_after_answer transitionFuel
            (queryBatchIndexedState state) record.answer (by
              simpa [queryBatchIndexedState] using armed)
      have fullArmed : nextFull.memory.2.queryBatch.boundarySeen = true := by
        have memoryExact := congrArg
          (fun reached => reached.memory.boundarySeen) projected
        simpa [queryBatchIndexedState] using memoryExact.trans smallArmed
      rw [show (extendControllerThroughCandidateQueryBatch transitionFuel
        target base dagOf).afterAnswer transitionFuel state record.answer =
          nextFull by rfl]
      rw [ih nextFull fullArmed, projected]

/-- Alignment of any post-boundary candidate-controller suffix projects to
the small armed query-batch controller. -/
theorem candidate_aligned_records_project_to_armed_query_batch
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat)
    (target : AspisK1.V7Tag73CausalQ16CoordinateRouter.Q16DigestSlot)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory →
      AspisK1.V7Tag73CausalDagFinalWorkQ16Controller.FinalWorkQ16DagMemory)
    (records : List UnifiedExposureRecord)
    (state : IndexedUnifiedExposureState globalOracleCalls
      (ExtendedControllerMemory Memory))
    (armed : state.memory.2.queryBatch.boundarySeen = true)
    (aligned : IndexedRecordsAligned transitionFuel
      (extendControllerThroughCandidateQueryBatch transitionFuel target base
        dagOf) state records) :
    IndexedRecordsAligned transitionFuel
      (armedQueryBatchController transitionFuel)
      (queryBatchIndexedState state) records := by
  intro prior selected later decomposition
  have fullSelected := aligned prior selected later decomposition
  have projected := query_batch_state_after_candidate_records transitionFuel
    target base dagOf prior state armed
  have cursorExact := congrArg
    (fun reached => reached.cursor) projected
  rw [← cursorExact]
  exact fullSelected

#print axioms armedQueryBatchAfterInput
#print axioms armedQueryBatchController
#print axioms queryBatchIndexedState
#print axioms query_batch_state_after_candidate_answer
#print axioms armed_query_batch_after_memory_used_slots
#print axioms armed_query_batch_used_slot_has_prior_record
#print axioms query_batch_state_after_candidate_records
#print axioms candidate_aligned_records_project_to_armed_query_batch

end
end AspisK1.V7Tag73CandidateQueryBatchArmedController
