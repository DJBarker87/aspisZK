import AspisFormal.K1.V7Tag73CandidateQueryBatchArmedController
import AspisFormal.K1.V7Tag73IndexedAlignedRecordReplay
import AspisFormal.K1.V7Tag73SqueezeInputStateInjectivity

/-!
# Structural invariant of the armed query-batch producer chain

After the candidate boundary installs block zero, every later producer is
created by the advance input of the unique preceding block.  Fresh root inputs
and answers preserve uniqueness of blocks, source inputs, and producer
digests.  These facts make both siblings of every live producer recognizable
before their answers are exposed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73CandidateQueryBatchProducerInvariant

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CandidateQueryBatchArmedController
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def QueryBatchProducerSourceValid
    (producers : List QueryBatchPrefixProducer)
    (producer : QueryBatchPrefixProducer) : Prop :=
  producer.block.val = 0 ∨
    ∃ parent ∈ producers,
      parent.block.val + 1 = producer.block.val ∧
      producer.sourceInput = bytes parent.digest ++ [domAdvance]

def QueryBatchProducerInventoryValid
    (producers : List QueryBatchPrefixProducer) : Prop :=
  ∀ producer ∈ producers, QueryBatchProducerSourceValid producers producer

theorem query_batch_output_slot_of_digest_nodup
    (producer : QueryBatchPrefixProducer) :
    ∀ producers : List QueryBatchPrefixProducer,
      (producers.map QueryBatchPrefixProducer.digest).Nodup →
      producer ∈ producers →
      queryBatchPrefixOutputSlot? producers
          (bytes producer.digest ++ [domSqueeze]) =
        some (producer.block, false) := by
  intro producers
  induction producers with
  | nil => simp
  | cons head tail ih =>
      intro nodup member
      have split : head.digest ∉ tail.map QueryBatchPrefixProducer.digest ∧
          (tail.map QueryBatchPrefixProducer.digest).Nodup := by
        simpa only [List.map_cons] using List.nodup_cons.mp nodup
      rcases List.mem_cons.mp member with equal | tailMember
      · subst head
        simp [queryBatchPrefixOutputSlot?]
      · have digestNe : producer.digest ≠ head.digest := by
          intro equal
          apply split.1
          exact List.mem_map.mpr ⟨producer, tailMember, equal⟩
        have bytesNe : bytes producer.digest ≠ bytes head.digest := by
          intro equal
          exact digestNe (digest_bytes_injective equal)
        have reduce : queryBatchPrefixOutputSlot? (head :: tail)
              (bytes producer.digest ++ [domSqueeze]) =
            queryBatchPrefixOutputSlot? tail
              (bytes producer.digest ++ [domSqueeze]) := by
          simp [queryBatchPrefixOutputSlot?, bytesNe]
        rw [reduce]
        exact ih split.2 tailMember

theorem query_batch_advance_slot_of_digest_nodup
    (producer : QueryBatchPrefixProducer) :
    ∀ producers : List QueryBatchPrefixProducer,
      (producers.map QueryBatchPrefixProducer.digest).Nodup →
      producer ∈ producers →
      queryBatchPrefixAdvanceSlot? producers
          (bytes producer.digest ++ [domAdvance]) =
        some (producer.block, true) := by
  intro producers
  induction producers with
  | nil => simp
  | cons head tail ih =>
      intro nodup member
      have split : head.digest ∉ tail.map QueryBatchPrefixProducer.digest ∧
          (tail.map QueryBatchPrefixProducer.digest).Nodup := by
        simpa only [List.map_cons] using List.nodup_cons.mp nodup
      rcases List.mem_cons.mp member with equal | tailMember
      · subst head
        simp [queryBatchPrefixAdvanceSlot?]
      · have digestNe : producer.digest ≠ head.digest := by
          intro equal
          apply split.1
          exact List.mem_map.mpr ⟨producer, tailMember, equal⟩
        have bytesNe : bytes producer.digest ≠ bytes head.digest := by
          intro equal
          exact digestNe (digest_bytes_injective equal)
        have reduce : queryBatchPrefixAdvanceSlot? (head :: tail)
              (bytes producer.digest ++ [domAdvance]) =
            queryBatchPrefixAdvanceSlot? tail
              (bytes producer.digest ++ [domAdvance]) := by
          simp [queryBatchPrefixAdvanceSlot?, bytesNe]
        rw [reduce]
        exact ih split.2 tailMember

theorem query_batch_advance_find_cases
    (producers : List QueryBatchPrefixProducer)
    (input : ShaInput) (parent : QueryBatchPrefixProducer)
    (found : producers.find? (fun producer =>
      decide (input = bytes producer.digest ++ [domAdvance])) = some parent) :
    parent ∈ producers ∧
      input = bytes parent.digest ++ [domAdvance] := by
  have predicate := List.find?_some found
  exact ⟨List.mem_of_find?_eq_some found, of_decide_eq_true predicate⟩

theorem query_batch_producer_source_valid_mono
    {before after : List QueryBatchPrefixProducer}
    (subset : ∀ producer, producer ∈ before → producer ∈ after)
    {producer : QueryBatchPrefixProducer}
    (valid : QueryBatchProducerSourceValid before producer) :
    QueryBatchProducerSourceValid after producer := by
  rcases valid with zero | ⟨parent, parentMember, blockExact, sourceExact⟩
  · exact Or.inl zero
  · exact Or.inr ⟨parent, subset parent parentMember, blockExact,
      sourceExact⟩

theorem extend_query_batch_producers_preserves_inventory
    (producers : List QueryBatchPrefixProducer)
    (input : ShaInput) (answer : Digest256)
    (valid : QueryBatchProducerInventoryValid producers) :
    QueryBatchProducerInventoryValid
      (extendQueryBatchPrefixProducers producers input answer) := by
  unfold extendQueryBatchPrefixProducers
  generalize foundExact : producers.find? (fun producer =>
      decide (input = bytes producer.digest ++ [domAdvance])) = found
  cases found with
  | none => exact valid
  | some parent =>
      by_cases bounded : parent.block.val + 1 < 12
      · simp only [bounded, dite_true]
        intro producer member
        rw [List.mem_append] at member
        rcases member with old | added
        · exact query_batch_producer_source_valid_mono
            (fun candidate candidateMember => List.mem_append_left _
              candidateMember) (valid producer old)
        · simp only [List.mem_singleton] at added
          subst producer
          obtain ⟨parentMember, inputExact⟩ :=
            query_batch_advance_find_cases producers input parent foundExact
          exact Or.inr ⟨parent, List.mem_append_left _ parentMember, rfl,
            inputExact⟩
      · simp [bounded]
        exact valid

theorem query_batch_producer_eq_of_block_eq
    (first second : QueryBatchPrefixProducer) :
    ∀ producers : List QueryBatchPrefixProducer,
      (producers.map QueryBatchPrefixProducer.block).Nodup →
      first ∈ producers → second ∈ producers →
      first.block = second.block → first = second := by
  intro producers
  induction producers with
  | nil => simp
  | cons head tail ih =>
      intro nodup firstMember secondMember blockExact
      have split : head.block ∉ tail.map QueryBatchPrefixProducer.block ∧
          (tail.map QueryBatchPrefixProducer.block).Nodup := by
        simpa only [List.map_cons] using List.nodup_cons.mp nodup
      rcases List.mem_cons.mp firstMember with firstHead | firstTail
      · subst first
        rcases List.mem_cons.mp secondMember with secondHead | secondTail
        · exact secondHead.symm
        · exfalso
          apply split.1
          exact List.mem_map.mpr ⟨second, secondTail, blockExact.symm⟩
      · rcases List.mem_cons.mp secondMember with secondHead | secondTail
        · subst second
          exfalso
          apply split.1
          exact List.mem_map.mpr ⟨first, firstTail, blockExact⟩
        · exact ih split.2 firstTail secondTail blockExact

theorem query_batch_successor_block_fresh
    (producers : List QueryBatchPrefixProducer)
    (input : ShaInput) (parent : QueryBatchPrefixProducer)
    (bounded : parent.block.val + 1 < 12)
    (valid : QueryBatchProducerInventoryValid producers)
    (blocksNodup : (producers.map QueryBatchPrefixProducer.block).Nodup)
    (sourceFresh : input ∉
      producers.map QueryBatchPrefixProducer.sourceInput)
    (found : producers.find? (fun producer =>
      decide (input = bytes producer.digest ++ [domAdvance])) = some parent) :
    (⟨parent.block.val + 1, bounded⟩ : Fin 12) ∉
      producers.map QueryBatchPrefixProducer.block := by
  intro blockMember
  obtain ⟨existing, existingMember, existingBlock⟩ :=
    List.mem_map.mp blockMember
  obtain ⟨parentMember, inputExact⟩ :=
    query_batch_advance_find_cases producers input parent found
  rcases valid existing existingMember with existingZero |
      ⟨otherParent, otherParentMember, otherBlock, sourceExact⟩
  · have positive : 0 < parent.block.val + 1 := by omega
    have existingValue : existing.block.val = parent.block.val + 1 := by
      simpa using congrArg Fin.val existingBlock
    have zero : parent.block.val + 1 = 0 := by omega
    omega
  · have parentsValue : otherParent.block.val = parent.block.val := by
      have existingValue : existing.block.val = parent.block.val + 1 := by
        simpa using congrArg Fin.val existingBlock
      have successor : otherParent.block.val + 1 = parent.block.val + 1 := by
        omega
      omega
    have parentsBlock : otherParent.block = parent.block := Fin.ext parentsValue
    have parentsExact : otherParent = parent :=
      query_batch_producer_eq_of_block_eq otherParent parent producers
        blocksNodup otherParentMember parentMember parentsBlock
    subst otherParent
    apply sourceFresh
    exact List.mem_map.mpr ⟨existing, existingMember, by
      rw [sourceExact, ← inputExact]⟩

theorem extend_query_batch_producers_blocks_nodup
    (producers : List QueryBatchPrefixProducer)
    (input : ShaInput) (answer : Digest256)
    (valid : QueryBatchProducerInventoryValid producers)
    (blocksNodup : (producers.map QueryBatchPrefixProducer.block).Nodup)
    (sourceFresh : input ∉
      producers.map QueryBatchPrefixProducer.sourceInput) :
    ((extendQueryBatchPrefixProducers producers input answer).map
      QueryBatchPrefixProducer.block).Nodup := by
  unfold extendQueryBatchPrefixProducers
  generalize foundExact : producers.find? (fun producer =>
      decide (input = bytes producer.digest ++ [domAdvance])) = found
  cases found with
  | none => exact blocksNodup
  | some parent =>
      by_cases bounded : parent.block.val + 1 < 12
      · simp only [bounded, dite_true, List.map_append, List.map_singleton]
        apply List.nodup_append.mpr
        refine ⟨blocksNodup, by simp, ?_⟩
        intro prior priorMember singleton singletonMember
        simp only [List.mem_singleton] at singletonMember
        subst singleton
        exact fun equal => query_batch_successor_block_fresh producers input
          parent bounded valid blocksNodup sourceFresh foundExact
            (equal ▸ priorMember)
      · simpa [bounded] using blocksNodup

theorem extend_query_batch_producers_source_inputs_nodup
    (producers : List QueryBatchPrefixProducer)
    (input : ShaInput) (answer : Digest256)
    (sourceNodup :
      (producers.map QueryBatchPrefixProducer.sourceInput).Nodup)
    (sourceFresh : input ∉
      producers.map QueryBatchPrefixProducer.sourceInput) :
    ((extendQueryBatchPrefixProducers producers input answer).map
      QueryBatchPrefixProducer.sourceInput).Nodup := by
  unfold extendQueryBatchPrefixProducers
  generalize foundExact : producers.find? (fun producer =>
      decide (input = bytes producer.digest ++ [domAdvance])) = found
  cases found with
  | none => exact sourceNodup
  | some parent =>
    by_cases bounded : parent.block.val + 1 < 12
    · simp only [bounded, dite_true, List.map_append, List.map_singleton]
      apply List.nodup_append.mpr
      refine ⟨sourceNodup, by simp, ?_⟩
      intro prior priorMember singleton singletonMember
      simp only [List.mem_singleton] at singletonMember
      subst singleton
      exact fun equal => sourceFresh (equal ▸ priorMember)
    · simpa [bounded] using sourceNodup

theorem extend_query_batch_producers_digests_nodup
    (producers : List QueryBatchPrefixProducer)
    (input : ShaInput) (answer : Digest256)
    (digestNodup : (producers.map QueryBatchPrefixProducer.digest).Nodup)
    (digestFresh : answer ∉ producers.map QueryBatchPrefixProducer.digest) :
    ((extendQueryBatchPrefixProducers producers input answer).map
      QueryBatchPrefixProducer.digest).Nodup := by
  unfold extendQueryBatchPrefixProducers
  generalize foundExact : producers.find? (fun producer =>
      decide (input = bytes producer.digest ++ [domAdvance])) = found
  cases found with
  | none => exact digestNodup
  | some parent =>
    by_cases bounded : parent.block.val + 1 < 12
    · simp only [bounded, dite_true, List.map_append, List.map_singleton]
      apply List.nodup_append.mpr
      refine ⟨digestNodup, by simp, ?_⟩
      intro prior priorMember singleton singletonMember
      simp only [List.mem_singleton] at singletonMember
      subst singleton
      exact fun equal => digestFresh (equal ▸ priorMember)
    · simpa [bounded] using digestNodup

/-- Every producer after one extension step is old, or is the exact producer
created from the current input and answer. -/
theorem extend_query_batch_producer_member_origin
    (producers : List QueryBatchPrefixProducer)
    (input : ShaInput) (answer : Digest256)
    (producer : QueryBatchPrefixProducer)
    (member : producer ∈
      extendQueryBatchPrefixProducers producers input answer) :
    producer ∈ producers ∨
      (producer.sourceInput = input ∧ producer.digest = answer) := by
  unfold extendQueryBatchPrefixProducers at member
  generalize foundExact : producers.find? (fun candidate =>
      decide (input = bytes candidate.digest ++ [domAdvance])) = found at member
  cases found with
  | none => exact Or.inl member
  | some parent =>
    by_cases bounded : parent.block.val + 1 < 12
    · simp only [bounded, dite_true] at member
      rw [List.mem_append] at member
      rcases member with old | added
      · exact Or.inl old
      · simp only [List.mem_singleton] at added
        subst producer
        exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl (by simpa [bounded] using member)

structure ArmedQueryBatchProducerInvariant
    (memory : QueryBatchPrefixControllerMemory) : Prop where
  boundarySeen : memory.boundarySeen = true
  inventoryValid : QueryBatchProducerInventoryValid memory.producers
  blocksNodup :
    (memory.producers.map QueryBatchPrefixProducer.block).Nodup
  sourceInputsNodup :
    (memory.producers.map QueryBatchPrefixProducer.sourceInput).Nodup
  digestsNodup :
    (memory.producers.map QueryBatchPrefixProducer.digest).Nodup

theorem singleton_armed_query_batch_invariant
    (producer : QueryBatchPrefixProducer)
    (memory : QueryBatchPrefixControllerMemory)
    (seen : memory.boundarySeen = true)
    (singleton : memory.producers = [producer])
    (blockZero : producer.block.val = 0) :
    ArmedQueryBatchProducerInvariant memory := by
  constructor
  · exact seen
  · intro candidate member
    rw [singleton] at member
    simp only [List.mem_singleton] at member
    subst candidate
    exact Or.inl blockZero
  · rw [singleton]
    simp
  · rw [singleton]
    simp
  · rw [singleton]
    simp

theorem armed_query_batch_after_input_preserves_invariant
    (memory : QueryBatchPrefixControllerMemory)
    (input : ShaInput) (answer : Digest256)
    (invariant : ArmedQueryBatchProducerInvariant memory)
    (sourceFresh : input ∉
      memory.producers.map QueryBatchPrefixProducer.sourceInput)
    (digestFresh : answer ∉
      memory.producers.map QueryBatchPrefixProducer.digest) :
    ArmedQueryBatchProducerInvariant
      (armedQueryBatchAfterInput memory input answer) := by
  constructor
  · exact armed_query_batch_boundary_seen_after_input memory input answer
  · exact extend_query_batch_producers_preserves_inventory
      memory.producers input answer invariant.inventoryValid
  · exact extend_query_batch_producers_blocks_nodup memory.producers input
      answer invariant.inventoryValid invariant.blocksNodup sourceFresh
  · exact extend_query_batch_producers_source_inputs_nodup memory.producers
      input answer invariant.sourceInputsNodup sourceFresh
  · exact extend_query_batch_producers_digests_nodup memory.producers input
      answer invariant.digestsNodup digestFresh

/-- An aligned machine-fresh record segment preserves the armed producer
invariant.  The two disjointness hypotheses say that every producer already
present was created before this segment; exact-root input and answer `Nodup`
facts discharge them in the source-facing specialization. -/
theorem aligned_records_preserve_armed_query_batch_invariant
    {globalOracleCalls : Nat} (transitionFuel : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        QueryBatchPrefixControllerMemory),
      IndexedRecordsAligned transitionFuel
        (armedQueryBatchController transitionFuel) state records →
      OnlyMachineFreshRecords records →
      (records.map causalInput?).Nodup →
      (records.map UnifiedExposureRecord.answer).Nodup →
      ArmedQueryBatchProducerInvariant state.memory →
      (∀ producer ∈ state.memory.producers,
        some producer.sourceInput ∉ records.map causalInput?) →
      (∀ producer ∈ state.memory.producers,
        producer.digest ∉ records.map UnifiedExposureRecord.answer) →
      ArmedQueryBatchProducerInvariant
        (indexedStateAfterRecords transitionFuel
          (armedQueryBatchController transitionFuel) records state).memory := by
  intro records
  induction records with
  | nil =>
      intro state _aligned _only _inputNodup _answerNodup invariant
        _sourceDisjoint _digestDisjoint
      simpa using invariant
  | cons head tail ih =>
      intro state aligned onlyMachine inputNodup answerNodup invariant
        sourceDisjoint digestDisjoint
      obtain ⟨actor, input, answer, headExact⟩ :=
        onlyMachine head (by simp)
      subst head
      let record : UnifiedExposureRecord := .machineFresh actor input answer
      let controller := armedQueryBatchController
        (globalOracleCalls := globalOracleCalls) transitionFuel
      let next := controller.afterAnswer transitionFuel state answer
      have headAligned := aligned [] record tail (by simp [record])
      have inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor =
          some input :=
        aligned_machine_record_has_exact_input transitionFuel state.cursor actor
          input answer (by simpa [record, controller,
            UnifiedExposureRecord.answer] using headAligned)
      have sourceFresh : input ∉
          state.memory.producers.map QueryBatchPrefixProducer.sourceInput := by
        intro member
        obtain ⟨producer, producerMember, sourceExact⟩ :=
          List.mem_map.mp member
        have forbidden := sourceDisjoint producer producerMember
        apply forbidden
        simp [causalInput?, sourceExact]
      have digestFresh : answer ∉
          state.memory.producers.map QueryBatchPrefixProducer.digest := by
        intro member
        obtain ⟨producer, producerMember, digestExact⟩ :=
          List.mem_map.mp member
        have forbidden := digestDisjoint producer producerMember
        apply forbidden
        rw [digestExact]
        change answer ∈ answer :: tail.map UnifiedExposureRecord.answer
        exact List.mem_cons_self
      have nextMemory : next.memory =
          armedQueryBatchAfterInput state.memory input answer := by
        simp [next, controller, armedQueryBatchController,
          IndexedUnifiedExposureController.afterAnswer,
          armedQueryBatchAfterMemory, inputExact]
      have nextInvariant : ArmedQueryBatchProducerInvariant next.memory := by
        rw [nextMemory]
        exact armed_query_batch_after_input_preserves_invariant state.memory
          input answer invariant sourceFresh digestFresh
      have tailAligned : IndexedRecordsAligned transitionFuel controller next
          tail := by
        have restricted := indexed_records_aligned_segment transitionFuel
          controller state (record :: tail) [record] tail [] aligned (by simp)
        simpa [next, controller, record,
          UnifiedExposureRecord.answer] using restricted
      have tailOnly : OnlyMachineFreshRecords tail := by
        intro candidate member
        exact onlyMachine candidate (by simp [member])
      have inputNodup' : (some input :: tail.map causalInput?).Nodup := by
        simpa [record, causalInput?] using inputNodup
      have answerNodup' :
          (answer :: tail.map UnifiedExposureRecord.answer).Nodup := by
        simpa [record, UnifiedExposureRecord.answer] using answerNodup
      have inputNodupSplit := List.nodup_cons.mp inputNodup'
      have answerNodupSplit := List.nodup_cons.mp answerNodup'
      have nextSourceDisjoint : ∀ producer ∈ next.memory.producers,
          some producer.sourceInput ∉ tail.map causalInput? := by
        intro producer producerMember tailMember
        have producerMember' : producer ∈
            extendQueryBatchPrefixProducers state.memory.producers input answer :=
          by simpa [nextMemory, armedQueryBatchAfterInput] using producerMember
        rcases extend_query_batch_producer_member_origin state.memory.producers
            input answer producer producerMember' with old | created
        · apply sourceDisjoint producer old
          simp only [List.map_cons, List.mem_cons]
          exact Or.inr tailMember
        · apply inputNodupSplit.1
          simpa [created.1] using tailMember
      have nextDigestDisjoint : ∀ producer ∈ next.memory.producers,
          producer.digest ∉ tail.map UnifiedExposureRecord.answer := by
        intro producer producerMember tailMember
        have producerMember' : producer ∈
            extendQueryBatchPrefixProducers state.memory.producers input answer :=
          by simpa [nextMemory, armedQueryBatchAfterInput] using producerMember
        rcases extend_query_batch_producer_member_origin state.memory.producers
            input answer producer producerMember' with old | created
        · apply digestDisjoint producer old
          simp only [List.map_cons, List.mem_cons]
          exact Or.inr tailMember
        · apply answerNodupSplit.1
          simpa [created.2] using tailMember
      have result := ih next tailAligned tailOnly inputNodupSplit.2
        answerNodupSplit.2 nextInvariant nextSourceDisjoint nextDigestDisjoint
      simpa [next, controller, record,
        UnifiedExposureRecord.answer] using result

#print axioms query_batch_output_slot_of_digest_nodup
#print axioms query_batch_advance_slot_of_digest_nodup
#print axioms extend_query_batch_producers_preserves_inventory
#print axioms query_batch_producer_eq_of_block_eq
#print axioms extend_query_batch_producers_blocks_nodup
#print axioms extend_query_batch_producer_member_origin
#print axioms ArmedQueryBatchProducerInvariant
#print axioms singleton_armed_query_batch_invariant
#print axioms armed_query_batch_after_input_preserves_invariant
#print axioms aligned_records_preserve_armed_query_batch_invariant

end
end AspisK1.V7Tag73CandidateQueryBatchProducerInvariant
