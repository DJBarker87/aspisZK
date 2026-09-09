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

end
end AspisK1.V7Tag73CandidateDirectedObserverProvenance
