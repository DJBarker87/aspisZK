import AspisFormal.K1.V7Tag73CandidateQueryBatchProducerInvariant

/-!
# Freshness of armed candidate query-batch child slots

If an exact child input of a live query-batch producer is the current record,
its logical output/advance slot cannot already have been consumed.  Otherwise
used-slot provenance exposes an earlier preferred record; block uniqueness
identifies the same producer, and causal-input `Nodup` yields a contradiction.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CandidateQueryBatchSlotFreshness

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateQueryBatchArmedController
open AspisK1.V7Tag73CandidateQueryBatchProducerInvariant
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- A producer child at the current aligned record retains a fresh logical
slot.  The result covers both squeeze outputs and advances. -/
theorem armed_query_batch_live_child_slot_unused
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (records : List UnifiedExposureRecord)
    (initial : IndexedUnifiedExposureState globalOracleCalls
      QueryBatchPrefixControllerMemory)
    (currentPrefix later : List UnifiedExposureRecord)
    (currentActor : QueryActor) (currentInput : ShaInput)
    (currentAnswer : Digest256)
    (producer : QueryBatchPrefixProducer) (isAdvance : Bool)
    (decomposition : records = currentPrefix ++
      (.machineFresh currentActor currentInput currentAnswer :
        UnifiedExposureRecord) :: later)
    (aligned : IndexedRecordsAligned transitionFuel
      (armedQueryBatchController transitionFuel) initial records)
    (onlyMachine : OnlyMachineFreshRecords records)
    (inputNodup : (records.map causalInput?).Nodup)
    (initialFresh : (producer.block, isAdvance) ∉
      initial.memory.usedSlots)
    (invariant : ArmedQueryBatchProducerInvariant
      (indexedStateAfterRecords transitionFuel
        (armedQueryBatchController transitionFuel) currentPrefix
        initial).memory)
    (producerMember : producer ∈
      (indexedStateAfterRecords transitionFuel
        (armedQueryBatchController transitionFuel) currentPrefix
        initial).memory.producers)
    (currentInputExact : currentInput =
      bytes producer.digest ++ [if isAdvance then domAdvance else domSqueeze]) :
    (producer.block, isAdvance) ∉
      (indexedStateAfterRecords transitionFuel
        (armedQueryBatchController transitionFuel) currentPrefix
        initial).memory.usedSlots := by
  let controller := armedQueryBatchController
    (globalOracleCalls := globalOracleCalls) transitionFuel
  let reached := indexedStateAfterRecords transitionFuel controller
    currentPrefix initial
  intro slotUsed
  obtain ⟨usedPrior, usedRecord, usedLater, prefixExact, usedPreferred⟩ :=
    armed_query_batch_used_slot_has_prior_record transitionFuel currentPrefix
      initial (producer.block, isAdvance) initialFresh (by
        simpa [controller, reached] using slotUsed)
  have usedMemberPrefix : usedRecord ∈ currentPrefix := by
    rw [prefixExact]
    simp
  have usedMemberRecords : usedRecord ∈ records := by
    rw [decomposition]
    exact List.mem_append_left _ usedMemberPrefix
  obtain ⟨usedActor, usedInput, usedAnswer, usedRecordExact⟩ :=
    onlyMachine usedRecord usedMemberRecords
  subst usedRecord
  let usedState := indexedStateAfterRecords transitionFuel controller
    usedPrior initial
  have preferred : armedQueryBatchPreferredSlot transitionFuel usedState =
      some (producer.block, isAdvance) := by
    change armedQueryBatchPreferredSlot transitionFuel
      (indexedStateAfterRecords transitionFuel
        (armedQueryBatchController transitionFuel) usedPrior initial) =
          some (producer.block, isAdvance) at usedPreferred
    simpa [usedState, controller] using usedPreferred
  obtain ⟨selectedInput, earlierProducer, selectedInputExact, earlierMember,
      earlierRole⟩ :=
    armed_query_batch_preferred_slot_has_producer transitionFuel usedState
      (producer.block, isAdvance) preferred
  have recordsAtUsed : records = usedPrior ++
      (.machineFresh usedActor usedInput usedAnswer : UnifiedExposureRecord) ::
        (usedLater ++
          (.machineFresh currentActor currentInput currentAnswer :
            UnifiedExposureRecord) :: later) := by
    rw [decomposition, prefixExact]
    simp only [List.cons_append, List.append_assoc]
  have usedAligned : unifiedRecordAtAnswer transitionFuel usedState.cursor
      usedAnswer =
        (.machineFresh usedActor usedInput usedAnswer :
          UnifiedExposureRecord) := by
    simpa [usedState, controller, UnifiedExposureRecord.answer] using
      aligned usedPrior
        (.machineFresh usedActor usedInput usedAnswer : UnifiedExposureRecord)
        (usedLater ++
          (.machineFresh currentActor currentInput currentAnswer :
            UnifiedExposureRecord) :: later) recordsAtUsed
  have usedInputExact : unifiedInputBeforeAnswer? transitionFuel
      usedState.cursor = some usedInput :=
    aligned_machine_record_has_exact_input transitionFuel usedState.cursor
      usedActor usedInput usedAnswer usedAligned
  have selectedInputEq : selectedInput = usedInput :=
    Option.some.inj (selectedInputExact.symm.trans usedInputExact)
  have earlierReached : earlierProducer ∈ reached.memory.producers := by
    have growth := armed_query_batch_indexed_state_producers_prefix
      transitionFuel
      ((.machineFresh usedActor usedInput usedAnswer : UnifiedExposureRecord) ::
        usedLater) usedState
    have member := growth.subset earlierMember
    change earlierProducer ∈
      (indexedStateAfterRecords transitionFuel controller currentPrefix
        initial).memory.producers
    rw [prefixExact, indexed_state_after_records_append]
    simpa [usedState, controller,
      UnifiedExposureRecord.answer] using member
  have producerBlock : earlierProducer.block = producer.block := by
    rcases earlierRole with outputRole | advanceRole
    · exact (congrArg Prod.fst outputRole.2).symm
    · exact (congrArg Prod.fst advanceRole.2).symm
  have producerExact : earlierProducer = producer :=
    query_batch_producer_eq_of_block_eq earlierProducer producer
      reached.memory.producers invariant.blocksNodup earlierReached
        producerMember producerBlock
  have usedInputEq : usedInput = currentInput := by
    rcases earlierRole with outputRole | advanceRole
    · have flagExact : isAdvance = false := by
        have pairExact : (producer.block, isAdvance) =
            (earlierProducer.block, false) := outputRole.2
        exact congrArg Prod.snd pairExact
      rw [flagExact] at currentInputExact
      simp only [Bool.false_eq_true, ↓reduceIte] at currentInputExact
      calc
        usedInput = selectedInput := selectedInputEq.symm
        _ = bytes earlierProducer.digest ++ [domSqueeze] := outputRole.1
        _ = bytes producer.digest ++ [domSqueeze] := by rw [producerExact]
        _ = currentInput := currentInputExact.symm
    · have flagExact : isAdvance = true := by
        have pairExact : (producer.block, isAdvance) =
            (earlierProducer.block, true) := advanceRole.2
        exact congrArg Prod.snd pairExact
      rw [flagExact] at currentInputExact
      simp only [↓reduceIte] at currentInputExact
      calc
        usedInput = selectedInput := selectedInputEq.symm
        _ = bytes earlierProducer.digest ++ [domAdvance] := advanceRole.1
        _ = bytes producer.digest ++ [domAdvance] := by rw [producerExact]
        _ = currentInput := currentInputExact.symm
  rw [decomposition, List.map_append] at inputNodup
  have separated := (List.nodup_append.mp inputNodup).2.2
  have prefixMember : some currentInput ∈ currentPrefix.map causalInput? := by
    rw [prefixExact, List.map_append]
    simp [causalInput?, usedInputEq]
  have suffixMember : some currentInput ∈
      ((.machineFresh currentActor currentInput currentAnswer :
        UnifiedExposureRecord) :: later).map causalInput? := by
    simp [causalInput?]
  exact separated _ prefixMember _ suffixMember rfl

#print axioms armed_query_batch_live_child_slot_unused

end
end AspisK1.V7Tag73CandidateQueryBatchSlotFreshness
