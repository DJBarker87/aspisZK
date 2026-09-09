import AspisFormal.K1.V7Tag73CandidateDirectedQueryBatchController
import AspisFormal.K1.V7Tag73IndexedAlignedRecordReplay

/-!
# Provenance of a candidate-directed q16 advance observation

An advance entry cannot appear in the candidate observer spontaneously.  If a
slot is absent before a machine-fresh record replay and present afterwards,
one literal record in that replay was recognized from a producer already in
the base DAG.  This is purely deterministic controller bookkeeping.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CandidateDirectedObserverProvenance

open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Once a target advance is present, arbitrary later records preserve its
exact answer. -/
theorem candidate_observed_advance_is_monotone_over_records
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat) (target : Q16DigestSlot)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory → FinalWorkQ16DagMemory) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (ExtendedControllerMemory Memory)) (existing : Digest256),
      state.memory.2.q16.advances target = some existing →
      (indexedStateAfterRecords transitionFuel
        (extendControllerThroughCandidateQueryBatch transitionFuel target base
          dagOf) records state).memory.2.q16.advances target = some existing := by
  intro records
  induction records with
  | nil =>
      intro state existing present
      simpa using present
  | cons record records ih =>
      intro state existing present
      let controller := extendControllerThroughCandidateQueryBatch
        transitionFuel target base dagOf
      let next := controller.afterAnswer transitionFuel state record.answer
      have nextPresent : next.memory.2.q16.advances target = some existing := by
        simp only [next, controller,
          IndexedUnifiedExposureController.afterAnswer,
          extendControllerThroughCandidateQueryBatch]
        cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor
        · simpa [inputExact] using present
        · simp only [inputExact]
          exact observed_q16_advance_is_monotone state.memory.2.q16
            (dagOf (baseIndexedState state).memory) _ record.answer existing
            target present
      rw [indexed_state_after_records_cons]
      exact ih next existing nextPresent

/-- If the target is still absent after a record prefix, an initially unarmed
query-batch extension remains unarmed throughout that prefix. -/
theorem candidate_query_batch_stays_inactive_until_target_seen
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat) (target : Q16DigestSlot)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory → FinalWorkQ16DagMemory) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (ExtendedControllerMemory Memory)),
      state.memory.2.queryBatch.boundarySeen = false →
      state.memory.2.queryBatch.producers = [] →
      (indexedStateAfterRecords transitionFuel
        (extendControllerThroughCandidateQueryBatch transitionFuel target base
          dagOf) records state).memory.2.q16.advances target = none →
      (indexedStateAfterRecords transitionFuel
        (extendControllerThroughCandidateQueryBatch transitionFuel target base
          dagOf) records state).memory.2.queryBatch.boundarySeen = false ∧
      (indexedStateAfterRecords transitionFuel
        (extendControllerThroughCandidateQueryBatch transitionFuel target base
          dagOf) records state).memory.2.queryBatch.producers = [] := by
  intro records
  induction records with
  | nil =>
      intro state unseen empty _absent
      exact ⟨unseen, empty⟩
  | cons record records ih =>
      intro state unseen empty finalAbsent
      let controller := extendControllerThroughCandidateQueryBatch
        transitionFuel target base dagOf
      let next := controller.afterAnswer transitionFuel state record.answer
      have stateAbsent : state.memory.2.q16.advances target = none := by
        cases current : state.memory.2.q16.advances target with
        | none => rfl
        | some existing =>
            have persists := candidate_observed_advance_is_monotone_over_records
              transitionFuel target base dagOf
              ((record : UnifiedExposureRecord) :: records) state existing
              current
            rw [finalAbsent] at persists
            contradiction
      have nextInactive : next.memory.2.queryBatch = state.memory.2.queryBatch := by
        simp only [next, controller,
          IndexedUnifiedExposureController.afterAnswer,
          extendControllerThroughCandidateQueryBatch]
        cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor
        · simp [inputExact]
        · simp only [inputExact]
          exact missing_candidate_continuation_cannot_arm target
            (dagOf (baseIndexedState state).memory) state.memory.2 _
            record.answer unseen empty stateAbsent
      have nextUnseen : next.memory.2.queryBatch.boundarySeen = false := by
        rw [nextInactive]
        exact unseen
      have nextEmpty : next.memory.2.queryBatch.producers = [] := by
        rw [nextInactive]
        exact empty
      have tailAbsent :
          (indexedStateAfterRecords transitionFuel controller records next
            ).memory.2.q16.advances target = none := by
        simpa [controller, next, indexed_state_after_records_cons,
          UnifiedExposureRecord.answer] using finalAbsent
      simpa [controller, next, indexed_state_after_records_cons,
        UnifiedExposureRecord.answer] using
          ih next nextUnseen nextEmpty tailAbsent

/-- After the target continuation is known, a machine-fresh prefix containing
no copy of its boundary input preserves both the continuation and an unarmed
query-batch extension. -/
theorem candidate_query_batch_stays_inactive_before_distinct_boundary
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat) (target : Q16DigestSlot)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory → FinalWorkQ16DagMemory)
    (continuation : Digest256) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (ExtendedControllerMemory Memory)),
      IndexedRecordsAligned transitionFuel
        (extendControllerThroughCandidateQueryBatch transitionFuel target base
          dagOf) state records →
      OnlyMachineFreshRecords records →
      (∀ record ∈ records,
        causalInput? record ≠ some (bytes continuation ++
          [domAbsorb, queryBatchChallengeLabel])) →
      state.memory.2.q16.advances target = some continuation →
      state.memory.2.queryBatch.boundarySeen = false →
      state.memory.2.queryBatch.producers = [] →
      let reached := indexedStateAfterRecords transitionFuel
        (extendControllerThroughCandidateQueryBatch transitionFuel target base
          dagOf) records state
      reached.memory.2.q16.advances target = some continuation ∧
      reached.memory.2.queryBatch.boundarySeen = false ∧
      reached.memory.2.queryBatch.producers = [] := by
  intro records
  induction records with
  | nil =>
      intro state _aligned _only _distinct present unseen empty
      exact ⟨present, unseen, empty⟩
  | cons head tail ih =>
      intro state aligned onlyMachine distinct present unseen empty
      obtain ⟨actor, input, answer, headExact⟩ :=
        onlyMachine head (by simp)
      subst head
      let controller := extendControllerThroughCandidateQueryBatch
        transitionFuel target base dagOf
      let next := controller.afterAnswer transitionFuel state answer
      have headAligned := aligned []
        (.machineFresh actor input answer : UnifiedExposureRecord) tail (by rfl)
      have inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
          some input := by
        simpa only [indexed_state_after_records_nil] using
          aligned_machine_record_has_exact_input transitionFuel state.cursor
            actor input answer headAligned
      have inputDifferent : input ≠ bytes continuation ++
          [domAbsorb, queryBatchChallengeLabel] := by
        intro equal
        have rejected := distinct
          (.machineFresh actor input answer : UnifiedExposureRecord) (by simp)
        exact rejected (by simp [causalInput?, equal])
      have nextPresent : next.memory.2.q16.advances target =
          some continuation := by
        simp only [next, controller,
          IndexedUnifiedExposureController.afterAnswer,
          extendControllerThroughCandidateQueryBatch, inputExact]
        exact observed_q16_advance_is_monotone state.memory.2.q16
          (dagOf (baseIndexedState state).memory) input answer continuation
          target present
      have nextInactive : next.memory.2.queryBatch = state.memory.2.queryBatch := by
        simp only [next, controller,
          IndexedUnifiedExposureController.afterAnswer,
          extendControllerThroughCandidateQueryBatch, inputExact]
        exact different_candidate_boundary_cannot_arm target
          (dagOf (baseIndexedState state).memory) state.memory.2 input answer
          continuation unseen empty present inputDifferent
      have tailAligned : IndexedRecordsAligned transitionFuel controller next
          tail := by
        apply indexed_records_aligned_segment transitionFuel controller state
          ((.machineFresh actor input answer : UnifiedExposureRecord) :: tail)
          [(.machineFresh actor input answer : UnifiedExposureRecord)] tail []
          aligned
        simp
      have tailOnly : OnlyMachineFreshRecords tail := by
        intro record member
        exact onlyMachine record (by simp [member])
      have tailDistinct : ∀ record ∈ tail,
          causalInput? record ≠ some (bytes continuation ++
            [domAbsorb, queryBatchChallengeLabel]) := by
        intro record member
        exact distinct record (by simp [member])
      have nextUnseen : next.memory.2.queryBatch.boundarySeen = false := by
        rw [nextInactive]
        exact unseen
      have nextEmpty : next.memory.2.queryBatch.producers = [] := by
        rw [nextInactive]
        exact empty
      simpa [controller, next, indexed_state_after_records_cons,
        UnifiedExposureRecord.answer] using
          ih next tailAligned tailOnly tailDistinct nextPresent nextUnseen
            nextEmpty

/-- Every newly present target advance has a literal installing record and a
producer which the base DAG already knew immediately before that record. -/
theorem candidate_observed_advance_has_installing_record
    {globalOracleCalls : Nat} {Memory Slot : Type}
    (transitionFuel : Nat) (target : Q16DigestSlot)
    (base : IndexedUnifiedExposureController globalOracleCalls
      Digest256 Slot Memory)
    (dagOf : Memory → FinalWorkQ16DagMemory) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        (ExtendedControllerMemory Memory)),
      IndexedRecordsAligned transitionFuel
        (extendControllerThroughCandidateQueryBatch transitionFuel target base
          dagOf) state records →
      OnlyMachineFreshRecords records →
      state.memory.2.q16.advances target = none →
      (indexedStateAfterRecords transitionFuel
        (extendControllerThroughCandidateQueryBatch transitionFuel target base
          dagOf) records state).memory.2.q16.advances target ≠ none →
      ∃ prior later actor input answer producer,
        records = prior ++
          (.machineFresh actor input answer : UnifiedExposureRecord) :: later ∧
        producer ∈
          (dagOf
            (baseIndexedState
              (indexedStateAfterRecords transitionFuel
                (extendControllerThroughCandidateQueryBatch transitionFuel
                  target base dagOf) prior state)).memory).producers ∧
        producer.slot = target ∧
        input = bytes producer.digest ++ [domAdvance] := by
  intro records
  induction records with
  | nil =>
      intro state _aligned _only absent present
      simp only [indexed_state_after_records_nil] at present
      exact (present absent).elim
  | cons head tail ih =>
      intro state aligned onlyMachine absent present
      obtain ⟨actor, input, answer, headExact⟩ :=
        onlyMachine head (by simp)
      subst head
      let controller := extendControllerThroughCandidateQueryBatch
        transitionFuel target base dagOf
      let next := controller.afterAnswer transitionFuel state answer
      have headAligned := aligned []
        (.machineFresh actor input answer : UnifiedExposureRecord) tail (by rfl)
      have inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
          some input := by
        simpa only [indexed_state_after_records_nil] using
          aligned_machine_record_has_exact_input transitionFuel state.cursor
            actor input answer headAligned
      have tailAligned : IndexedRecordsAligned transitionFuel controller next
          tail := by
        apply indexed_records_aligned_segment transitionFuel controller state
          ((.machineFresh actor input answer : UnifiedExposureRecord) :: tail)
          [(.machineFresh actor input answer : UnifiedExposureRecord)] tail []
          aligned
        simp
      have tailOnly : OnlyMachineFreshRecords tail := by
        intro record member
        exact onlyMachine record (by simp [member])
      have presentNext :
          (indexedStateAfterRecords transitionFuel controller tail next
            ).memory.2.q16.advances target ≠ none := by
        simpa [controller, next, indexed_state_after_records_cons,
          UnifiedExposureRecord.answer] using present
      cases selected : q16AdvanceSlot?
          (dagOf (baseIndexedState state).memory).producers input with
      | none =>
          have nextAbsent : next.memory.2.q16.advances target = none := by
            simp [next, controller,
              IndexedUnifiedExposureController.afterAnswer,
              extendControllerThroughCandidateQueryBatch,
              candidateDirectedQueryBatchAfterInput,
              ObservedQ16Duplex.afterInput, inputExact, selected, absent]
          obtain ⟨prior, later, foundActor, foundInput, foundAnswer, producer,
              decomposition, producerMember, slotExact, inputFound⟩ :=
            ih next tailAligned tailOnly nextAbsent presentNext
          refine ⟨(.machineFresh actor input answer : UnifiedExposureRecord) ::
              prior, later, foundActor, foundInput, foundAnswer, producer, ?_,
            ?_, slotExact, inputFound⟩
          · simpa only [List.cons_append] using congrArg
              (fun xs => (.machineFresh actor input answer :
                UnifiedExposureRecord) :: xs) decomposition
          · simpa [controller, next, indexed_state_after_records_cons,
              UnifiedExposureRecord.answer] using producerMember
      | some selectedSlot =>
          by_cases targetExact : selectedSlot = target
          ·
            obtain ⟨producer, producerMember, producerSlot, producerInput⟩ :
                ∃ producer,
                  producer ∈
                    (dagOf (baseIndexedState state).memory).producers ∧
                  producer.slot = target ∧
                  input = bytes producer.digest ++ [domAdvance] := by
              unfold q16AdvanceSlot? at selected
              rw [Option.map_eq_some_iff] at selected
              obtain ⟨producer, found, slotExact⟩ := selected
              have producerMember := List.mem_of_find?_eq_some found
              have inputMatch := of_decide_eq_true
                (List.find?_eq_some_iff_append.mp found).1
              exact ⟨producer, producerMember,
                slotExact.trans targetExact, inputMatch⟩
            exact ⟨[], tail, actor, input, answer, producer, by simp,
              by simpa using producerMember, producerSlot, producerInput⟩
          · have nextAbsent : next.memory.2.q16.advances target = none := by
              have targetNe : target ≠ selectedSlot := Ne.symm targetExact
              simp only [next, controller,
                IndexedUnifiedExposureController.afterAnswer,
                extendControllerThroughCandidateQueryBatch]
              rw [inputExact]
              simp only [candidateDirectedQueryBatchAfterInput,
                ObservedQ16Duplex.afterInput, selected]
              change
                (if state.memory.2.q16.advances selectedSlot = none then
                    Function.update state.memory.2.q16.advances selectedSlot
                      (some answer)
                  else state.memory.2.q16.advances) target = none
              by_cases slotAbsent :
                  state.memory.2.q16.advances selectedSlot = none
              · simp [slotAbsent, Function.update, targetNe, absent]
              · simp [slotAbsent, absent]
            obtain ⟨prior, later, foundActor, foundInput, foundAnswer, producer,
                decomposition, producerMember, slotExact, inputFound⟩ :=
              ih next tailAligned tailOnly nextAbsent presentNext
            refine ⟨(.machineFresh actor input answer : UnifiedExposureRecord) ::
                prior, later, foundActor, foundInput, foundAnswer, producer, ?_,
              ?_, slotExact, inputFound⟩
            · simpa only [List.cons_append] using congrArg
                (fun xs => (.machineFresh actor input answer :
                  UnifiedExposureRecord) :: xs) decomposition
            · simpa [controller, next, indexed_state_after_records_cons,
                UnifiedExposureRecord.answer] using producerMember

#print axioms candidate_observed_advance_has_installing_record
#print axioms candidate_observed_advance_is_monotone_over_records
#print axioms candidate_query_batch_stays_inactive_until_target_seen
#print axioms candidate_query_batch_stays_inactive_before_distinct_boundary

end
end AspisK1.V7Tag73CandidateDirectedObserverProvenance
