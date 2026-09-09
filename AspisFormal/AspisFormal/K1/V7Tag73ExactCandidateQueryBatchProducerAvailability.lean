import AspisFormal.K1.V7Tag73CandidateQueryBatchSlotFreshness
import AspisFormal.K1.V7Tag73ExactCandidateQueryBatchChainAnchor
import AspisFormal.K1.V7Tag73ExactRootRecordOrderLift

/-!
# Source chronology for candidate query-batch producers

The armed block-zero producer is available immediately after the selected
boundary.  Every later producer is installed by its literal advance record.
This file turns either origin into availability immediately before any child
whose source-order certificate occurs in the accepted root.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCandidateQueryBatchProducerAvailability

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateQueryBatchArmedController
open AspisK1.V7Tag73CandidateQueryBatchProducerInvariant
open AspisK1.V7Tag73CandidateQueryBatchSlotFreshness
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactRootRecordOrderLift
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- A producer is either the block-zero value installed at the boundary, or
was installed by one literal source record in the post-boundary suffix. -/
inductive ArmedQueryBatchProducerReady
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (suffix : List UnifiedExposureRecord)
    (initial : IndexedUnifiedExposureState globalOracleCalls
      QueryBatchPrefixControllerMemory)
    (boundaryInput : ShaInput) (boundaryDigest : Digest256) :
    QueryBatchPrefixProducer → Prop where
  | boundary (producer : QueryBatchPrefixProducer)
      (sourceExact : producer.sourceInput = boundaryInput)
      (digestExact : producer.digest = boundaryDigest)
      (member : producer ∈ initial.memory.producers) :
      ArmedQueryBatchProducerReady transitionFuel suffix initial
        boundaryInput boundaryDigest producer
  | recorded (producer : QueryBatchPrefixProducer)
      (prior later : List UnifiedExposureRecord) (actor : QueryActor)
      (decomposition : suffix = prior ++
        (.machineFresh actor producer.sourceInput producer.digest :
          UnifiedExposureRecord) :: later)
      (member : producer ∈
        (indexedStateAfterRecords transitionFuel
          (armedQueryBatchController transitionFuel)
          (prior ++
            [(.machineFresh actor producer.sourceInput producer.digest :
              UnifiedExposureRecord)]) initial).memory.producers) :
      ArmedQueryBatchProducerReady transitionFuel suffix initial
        boundaryInput boundaryDigest producer

/-- The armed producer invariant restricts to every strict prefix of an
aligned root suffix. -/
theorem armed_query_batch_invariant_at_record_prefix
    {globalOracleCalls : Nat} (transitionFuel : Nat)
    (records : List UnifiedExposureRecord)
    (initial : IndexedUnifiedExposureState globalOracleCalls
      QueryBatchPrefixControllerMemory)
    (prior later : List UnifiedExposureRecord)
    (selected : UnifiedExposureRecord)
    (decomposition : records = prior ++ selected :: later)
    (aligned : IndexedRecordsAligned transitionFuel
      (armedQueryBatchController transitionFuel) initial records)
    (onlyMachine : OnlyMachineFreshRecords records)
    (inputNodup : (records.map causalInput?).Nodup)
    (answerNodup :
      (records.map UnifiedExposureRecord.answer).Nodup)
    (initialInvariant : ArmedQueryBatchProducerInvariant initial.memory)
    (sourceDisjoint : ∀ producer ∈ initial.memory.producers,
      some producer.sourceInput ∉ records.map causalInput?)
    (digestDisjoint : ∀ producer ∈ initial.memory.producers,
      producer.digest ∉ records.map UnifiedExposureRecord.answer) :
    ArmedQueryBatchProducerInvariant
      (indexedStateAfterRecords transitionFuel
        (armedQueryBatchController transitionFuel) prior initial).memory := by
  have priorAligned : IndexedRecordsAligned transitionFuel
      (armedQueryBatchController transitionFuel) initial prior := by
    apply indexed_records_aligned_segment transitionFuel
      (armedQueryBatchController transitionFuel) initial records [] prior
        (selected :: later) aligned
    simpa using decomposition
  have priorOnly : OnlyMachineFreshRecords prior := by
    apply only_machine_fresh_records_segment records [] prior
      (selected :: later) onlyMachine
    simpa using decomposition
  have priorInputNodup : (prior.map causalInput?).Nodup := by
    rw [decomposition, List.map_append] at inputNodup
    exact (List.nodup_append.mp inputNodup).1
  have priorAnswerNodup :
      (prior.map UnifiedExposureRecord.answer).Nodup := by
    rw [decomposition, List.map_append] at answerNodup
    exact (List.nodup_append.mp answerNodup).1
  apply aligned_records_preserve_armed_query_batch_invariant transitionFuel
    prior initial priorAligned priorOnly priorInputNodup priorAnswerNodup
      initialInvariant
  · intro producer member forbidden
    exact sourceDisjoint producer member (by
      rw [decomposition, List.map_append]
      exact List.mem_append_left _ forbidden)
  · intro producer member forbidden
    exact digestDisjoint producer member (by
      rw [decomposition, List.map_append]
      exact List.mem_append_left _ forbidden)
/-- Strict source-before-child order in the full root yields a literal child
decomposition in the post-boundary suffix and producer availability at that
child's pre-answer state. -/
theorem armed_query_batch_ready_producer_available_before_child
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (boundaryPrior suffix : List UnifiedExposureRecord)
    (boundaryActor : QueryActor) (boundaryInput : ShaInput)
    (boundaryDigest : Digest256)
    (rootExact : exactFixedRootRecords input.package.root = boundaryPrior ++
      (.machineFresh boundaryActor boundaryInput boundaryDigest :
        UnifiedExposureRecord) :: suffix)
    (initial : IndexedUnifiedExposureState
      (globalFull256OracleCallCap parameters)
      QueryBatchPrefixControllerMemory)
    (producer : QueryBatchPrefixProducer)
    (ready : ArmedQueryBatchProducerReady transitionFuel suffix initial
      boundaryInput boundaryDigest producer)
    (childInput : ShaInput) (childAnswer : Digest256)
    (ordered : ∃ before middle after,
      exactRootFreshQueries input =
        before ++ (producer.sourceInput, producer.digest) :: middle ++
          (childInput, childAnswer) :: after) :
    ∃ childPrefix childLater childActor,
      suffix = childPrefix ++
        (.machineFresh childActor childInput childAnswer :
          UnifiedExposureRecord) :: childLater ∧
      producer ∈
        (indexedStateAfterRecords transitionFuel
          (armedQueryBatchController transitionFuel) childPrefix
          initial).memory.producers := by
  obtain ⟨before, middle, after, pairExact⟩ := ordered
  obtain ⟨pairPrior, between, pairLater, producerActor, childActor,
      pairRootExact⟩ :=
    exact_root_pair_order_lifts_to_records input producer.sourceInput
      childInput producer.digest childAnswer before middle after pairExact
  let boundaryRecord : UnifiedExposureRecord :=
    .machineFresh boundaryActor boundaryInput boundaryDigest
  let producerRecord : UnifiedExposureRecord :=
    .machineFresh producerActor producer.sourceInput producer.digest
  let childRecord : UnifiedExposureRecord :=
    .machineFresh childActor childInput childAnswer
  cases ready with
  | boundary sourceExact digestExact initialMember =>
      have prefixExact : boundaryPrior = pairPrior := by
        apply mapped_nodup_selected_prefix_eq causalInput?
          (exactFixedRootRecords input.package.root) boundaryPrior suffix
            pairPrior (between ++ childRecord :: pairLater)
          boundaryRecord producerRecord
          (exact_root_record_causal_inputs_nodup input) rootExact
          (by simpa [producerRecord, childRecord, List.append_assoc] using
            pairRootExact)
        simp [boundaryRecord, producerRecord, causalInput?, sourceExact.symm]
      subst pairPrior
      have tails : boundaryRecord :: suffix =
          producerRecord :: between ++ childRecord :: pairLater := by
        exact List.append_cancel_left (rootExact.symm.trans (by
          simpa [producerRecord, childRecord, List.append_assoc] using
            pairRootExact))
      have suffixExact : suffix = between ++ childRecord :: pairLater :=
        (List.cons.inj tails).2
      have growth := armed_query_batch_indexed_state_producers_prefix
        transitionFuel between initial
      exact ⟨between, pairLater, childActor, by
        simpa [childRecord] using suffixExact, growth.subset initialMember⟩
  | recorded sourcePrior sourceLater sourceActor sourceExact sourceMember =>
      let sourceRecord : UnifiedExposureRecord :=
        .machineFresh sourceActor producer.sourceInput producer.digest
      let sourceRootPrefix :=
        boundaryPrior ++ boundaryRecord :: sourcePrior
      have sourceRootExact : exactFixedRootRecords input.package.root =
          sourceRootPrefix ++ sourceRecord :: sourceLater := by
        rw [rootExact, sourceExact]
        simp [sourceRootPrefix, sourceRecord, boundaryRecord,
          List.append_assoc]
      have prefixExact : sourceRootPrefix = pairPrior := by
        apply mapped_nodup_selected_prefix_eq causalInput?
          (exactFixedRootRecords input.package.root) sourceRootPrefix
            sourceLater pairPrior (between ++ childRecord :: pairLater)
          sourceRecord producerRecord
          (exact_root_record_causal_inputs_nodup input) sourceRootExact
          (by simpa [producerRecord, childRecord, List.append_assoc] using
            pairRootExact)
        simp [sourceRecord, producerRecord, causalInput?]
      subst pairPrior
      have tails : sourceRecord :: sourceLater =
          producerRecord :: between ++ childRecord :: pairLater := by
        exact List.append_cancel_left (sourceRootExact.symm.trans (by
          simpa [producerRecord, childRecord, List.append_assoc] using
            pairRootExact))
      have sourceLaterExact : sourceLater =
          between ++ childRecord :: pairLater := (List.cons.inj tails).2
      let childPrefix := sourcePrior ++ sourceRecord :: between
      have suffixChild : suffix = childPrefix ++ childRecord :: pairLater := by
        rw [sourceExact, sourceLaterExact]
        simp [childPrefix, sourceRecord, List.append_assoc]
      let afterSource := indexedStateAfterRecords transitionFuel
        (armedQueryBatchController transitionFuel)
        (sourcePrior ++ [sourceRecord]) initial
      have growth := armed_query_batch_indexed_state_producers_prefix
        transitionFuel between afterSource
      have available : producer ∈
          (indexedStateAfterRecords transitionFuel
            (armedQueryBatchController transitionFuel) childPrefix
            initial).memory.producers := by
        rw [show childPrefix =
          (sourcePrior ++ [sourceRecord]) ++ between by
            simp [childPrefix]]
        rw [indexed_state_after_records_append]
        exact growth.subset (by simpa [afterSource, sourceRecord] using
          sourceMember)
      exact ⟨childPrefix, pairLater, childActor, by
        simpa [childRecord] using suffixChild, available⟩

#print axioms ArmedQueryBatchProducerReady
#print axioms armed_query_batch_invariant_at_record_prefix
#print axioms armed_query_batch_ready_producer_available_before_child

end
end AspisK1.V7Tag73ExactCandidateQueryBatchProducerAvailability
