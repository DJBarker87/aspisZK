import AspisFormal.K1.V7Tag73CandidateDirectedQueryBatchController
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

#print axioms armedQueryBatchAfterInput
#print axioms armedQueryBatchController
#print axioms queryBatchIndexedState
#print axioms query_batch_state_after_candidate_answer
#print axioms query_batch_state_after_candidate_records

end
end AspisK1.V7Tag73CandidateQueryBatchArmedController
