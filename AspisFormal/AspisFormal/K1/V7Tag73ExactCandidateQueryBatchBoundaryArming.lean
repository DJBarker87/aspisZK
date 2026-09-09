import AspisFormal.K1.V7Tag73ExactCandidateAdvanceFreshness
import AspisFormal.K1.V7Tag73ExactRootLookupCausalOrder
import AspisFormal.K1.V7Tag73ExactRootRecordOrderLift
import AspisFormal.K1.V7Tag73NoPairOccurrenceTrichotomy
import AspisFormal.K1.V7Tag73CausalFoldAlphaQ16QueryBatchController

/-!
# Exact arming of the candidate-directed query-batch controller

The selected terminal advance is installed at its literal root record.  Its
answer persists across the unique intervening fresh inputs, and the following
query-batch-domain record arms block zero of the query-batch DAG.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCandidateQueryBatchBoundaryArming

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateDirectedObserverProvenance
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalDagProducerInvariant
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCandidateAdvanceFreshness
open AspisK1.V7Tag73ExactCandidateQueryBatchControllerProjection
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaQ16OperationalRealization
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactRootRecordOrderLift
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The real query-batch-domain answer arms the candidate-directed extension
with the exact selected terminal continuation. -/
theorem exact_selected_candidate_query_batch_boundary_arms
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (foldTrial : ExactCompilerExposureTrial parameters)
    (boundaryIndex : Nat) :
    ∃ (finalTrial : ExactCompilerExposureTrial parameters)
        (target : Q16DigestSlot) (blockAdvance queryBatchDigest : Digest256)
        (beforeDomain : EvalState)
        (boundaryPrior boundaryLater : List UnifiedExposureRecord)
        (boundaryActor : QueryActor),
      exactFixedRootRecords input.package.root =
        boundaryPrior ++
          (.machineFresh boundaryActor
            (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
            queryBatchDigest : UnifiedExposureRecord) :: boundaryLater ∧
      finalTrial =
        (exactAcceptedDagInstallation transitionRoom input).finalTrial ∧
      blockAdvance = beforeDomain.digest ∧
      beforeDomain.digest =
        (exactOperationalQ16Evaluator input).afterQ16.digest ∧
      let base := candidateCompleteBaseController transitionFuel foldTrial.val
        finalTrial.val boundaryIndex
      let controller := extendControllerThroughCandidateQueryBatch
        transitionFuel target base completeFoldAlphaQ16DagMemory
      let initial := exactCandidateDirectedQueryBatchInitialState input
      let beforeBoundary := indexedStateAfterRecords transitionFuel controller
        boundaryPrior initial
      let afterBoundary := controller.afterAnswer transitionFuel beforeBoundary
        queryBatchDigest
      beforeBoundary.memory.2.q16.advances target = some blockAdvance ∧
      beforeBoundary.memory.2.queryBatch.boundarySeen = false ∧
      beforeBoundary.memory.2.queryBatch.producers = [] ∧
      afterBoundary.memory.2.queryBatch =
        { boundarySeen := true
          producers :=
            [{ digest := queryBatchDigest, block := 0,
               sourceInput := bytes blockAdvance ++
                 [domAbsorb, queryBatchChallengeLabel] }]
          usedSlots := ∅ } := by
  obtain ⟨finalTrial, target, blockProducerInput, blockDigest, blockAdvance,
      beforeDomain, beforeQueryBatch, preAdvance, advanceLater, advanceActor,
      advanceRootExact, selectedMember, finalTrialExact, targetAbsent, advanceLookup,
      terminalExact, boundaryStart, boundaryLookup⟩ :=
    exact_selected_candidate_advance_is_fresh transitionRoom input foldTrial
      boundaryIndex
  let boundaryInput : ShaInput :=
    bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel]
  have boundaryLookup' : tableLookup (exactOperationalTable input)
      boundaryInput = some beforeQueryBatch.digest := by
    simpa [boundaryInput, terminalExact] using boundaryLookup
  have dependency : HasLiteralStatePrefix blockAdvance boundaryInput := by
    simp [HasLiteralStatePrefix, boundaryInput, bytes]
  obtain ⟨orderedBefore, orderedMiddle, orderedAfter, orderedPairs⟩ :=
    exact_compiler_literal_dependency_has_strict_root_order transitionRoom input
      (gammaAdvanceInput blockDigest) boundaryInput blockAdvance
      beforeQueryBatch.digest advanceLookup boundaryLookup' dependency
  obtain ⟨orderedPrior, between, boundaryLater, orderedAdvanceActor,
      boundaryActor, orderedRootExact⟩ :=
    exact_root_pair_order_lifts_to_records input
      (gammaAdvanceInput blockDigest) boundaryInput blockAdvance
      beforeQueryBatch.digest orderedBefore orderedMiddle orderedAfter
      orderedPairs
  let freshnessAdvance : UnifiedExposureRecord :=
    .machineFresh advanceActor (gammaAdvanceInput blockDigest) blockAdvance
  let orderedAdvance : UnifiedExposureRecord :=
    .machineFresh orderedAdvanceActor (gammaAdvanceInput blockDigest)
      blockAdvance
  let boundaryRecord : UnifiedExposureRecord :=
    .machineFresh boundaryActor boundaryInput beforeQueryBatch.digest
  have priorExact : preAdvance = orderedPrior := by
    apply mapped_nodup_selected_prefix_eq causalInput?
      (exactFixedRootRecords input.package.root) preAdvance advanceLater
      orderedPrior (between ++ boundaryRecord :: boundaryLater)
      freshnessAdvance orderedAdvance
      (exact_root_record_causal_inputs_nodup input)
    · simpa [freshnessAdvance] using advanceRootExact
    · simpa [orderedAdvance, boundaryRecord, List.append_assoc] using
        orderedRootExact
    · simp [freshnessAdvance, orderedAdvance, causalInput?]
  subst orderedPrior
  let base : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256
      FoldAlphaFinalWorkQ16DigestSlot CompleteFoldAlphaQ16Memory :=
    candidateCompleteBaseController transitionFuel foldTrial.val finalTrial.val
      boundaryIndex
  let controller := extendControllerThroughCandidateQueryBatch transitionFuel
    target base completeFoldAlphaQ16DagMemory
  let initial := exactCandidateDirectedQueryBatchInitialState input
  let beforeAdvance := indexedStateAfterRecords transitionFuel controller
    preAdvance initial
  have fullAligned :=
    exact_root_records_aligned_for_candidate_directed_controller input foldTrial
      finalTrial boundaryIndex target
  have advanceInputExact : unifiedInputBeforeAnswer? transitionFuel
      beforeAdvance.cursor = some (gammaAdvanceInput blockDigest) := by
    have aligned := fullAligned preAdvance freshnessAdvance advanceLater
      (by simpa [freshnessAdvance] using advanceRootExact)
    exact aligned_machine_record_has_exact_input transitionFuel
      beforeAdvance.cursor advanceActor (gammaAdvanceInput blockDigest)
      blockAdvance (by simpa [beforeAdvance, freshnessAdvance,
        UnifiedExposureRecord.answer] using aligned)
  have selectedDigestNodup :
      ((completeFoldAlphaQ16DagMemory
        (baseIndexedState beforeAdvance).memory).producers.map
          Q16DagProducer.digest).Nodup := by
    rw [candidate_extended_dag_after_records_eq_standalone input foldTrial
      finalTrial boundaryIndex target preAdvance]
    exact exact_dag_candidate_prefix_producer_digests_nodup input finalTrial
      preAdvance (freshnessAdvance :: advanceLater)
      (by simpa [freshnessAdvance] using advanceRootExact)
  have selectedSlot : q16AdvanceSlot?
      (completeFoldAlphaQ16DagMemory
        (baseIndexedState beforeAdvance).memory).producers
      (gammaAdvanceInput blockDigest) = some target := by
    apply AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController.q16_advance_slot_of_digest_nodup
      (Q16DagProducer.mk blockDigest target blockProducerInput)
      (completeFoldAlphaQ16DagMemory
        (baseIndexedState beforeAdvance).memory).producers selectedDigestNodup
    simpa [beforeAdvance, controller, base, initial] using selectedMember
  have preAdvanceInactive :=
    candidate_query_batch_stays_inactive_until_target_seen transitionFuel target
      base completeFoldAlphaQ16DagMemory preAdvance initial (by rfl) (by rfl)
      (by simpa [beforeAdvance, controller, base, initial] using targetAbsent)
  have beforeAdvanceUnseen :
      beforeAdvance.memory.2.queryBatch.boundarySeen = false :=
    preAdvanceInactive.1
  have beforeAdvanceEmpty :
      beforeAdvance.memory.2.queryBatch.producers = [] :=
    preAdvanceInactive.2
  have beforeAdvanceMemory : beforeAdvance.memory.2.queryBatch =
      inactiveQueryBatchPrefixMemory := by
    have preserved :=
      candidate_query_batch_memory_preserved_until_target_seen transitionFuel
        target base completeFoldAlphaQ16DagMemory preAdvance initial (by rfl)
          (by rfl) (by
            simpa [beforeAdvance, controller, base, initial] using targetAbsent)
    simpa [beforeAdvance, controller, initial,
      exactCandidateDirectedQueryBatchInitialState,
      inactiveQueryBatchDagExtensionMemory] using preserved
  let afterAdvance := controller.afterAnswer transitionFuel beforeAdvance
    blockAdvance
  have afterAdvanceTarget : afterAdvance.memory.2.q16.advances target =
      some blockAdvance := by
    simp only [afterAdvance, controller,
      IndexedUnifiedExposureController.afterAnswer,
      extendControllerThroughCandidateQueryBatch, advanceInputExact]
    exact observed_q16_advance_installed beforeAdvance.memory.2.q16
      (completeFoldAlphaQ16DagMemory
        (baseIndexedState beforeAdvance).memory)
      (gammaAdvanceInput blockDigest) blockAdvance target
      (by simpa [beforeAdvance, controller, base, initial] using targetAbsent)
      selectedSlot
  have afterAdvanceQueryBatch :
      afterAdvance.memory.2.queryBatch = beforeAdvance.memory.2.queryBatch := by
    simp only [afterAdvance, controller,
      IndexedUnifiedExposureController.afterAnswer,
      extendControllerThroughCandidateQueryBatch, advanceInputExact]
    exact missing_candidate_continuation_cannot_arm target
      (completeFoldAlphaQ16DagMemory
        (baseIndexedState beforeAdvance).memory) beforeAdvance.memory.2
      (gammaAdvanceInput blockDigest) blockAdvance beforeAdvanceUnseen
      beforeAdvanceEmpty
      (by simpa [beforeAdvance, controller, base, initial] using targetAbsent)
  have afterAdvanceUnseen :
      afterAdvance.memory.2.queryBatch.boundarySeen = false := by
    rw [afterAdvanceQueryBatch]
    exact beforeAdvanceUnseen
  have afterAdvanceEmpty : afterAdvance.memory.2.queryBatch.producers = [] := by
    rw [afterAdvanceQueryBatch]
    exact beforeAdvanceEmpty
  have betweenAligned : IndexedRecordsAligned transitionFuel controller
      afterAdvance between := by
    have raw := indexed_records_aligned_segment transitionFuel controller initial
      (exactFixedRootRecords input.package.root)
      (preAdvance ++ [orderedAdvance]) between
      (boundaryRecord :: boundaryLater)
      (by simpa [controller, base, initial] using fullAligned)
      (by simpa [orderedAdvance, boundaryRecord, List.append_assoc] using
        orderedRootExact)
    simpa [afterAdvance, beforeAdvance, indexed_state_after_records_append,
      orderedAdvance, UnifiedExposureRecord.answer] using raw
  have betweenOnly : OnlyMachineFreshRecords between := by
    apply only_machine_fresh_records_segment
      (exactFixedRootRecords input.package.root)
      (preAdvance ++ [orderedAdvance]) between
      (boundaryRecord :: boundaryLater)
      (exact_root_records_only_machine_fresh input)
    simpa [orderedAdvance, boundaryRecord, List.append_assoc] using
      orderedRootExact
  have betweenDistinct : ∀ record ∈ between,
      causalInput? record ≠ some boundaryInput := by
    have rootNodup := exact_root_record_causal_inputs_nodup input
    let boundaryPrior := preAdvance ++ orderedAdvance :: between
    have boundaryRootExact : exactFixedRootRecords input.package.root =
        boundaryPrior ++ boundaryRecord :: boundaryLater := by
      simpa [boundaryPrior, orderedAdvance, boundaryRecord, List.append_assoc]
        using orderedRootExact
    rw [boundaryRootExact, List.map_append] at rootNodup
    have separated := (List.nodup_append.mp rootNodup).2.2
    intro record recordMember equal
    have prefixMember : some boundaryInput ∈ boundaryPrior.map causalInput? := by
      rw [show boundaryPrior = preAdvance ++ orderedAdvance :: between by rfl,
        List.map_append]
      apply List.mem_append_right
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨record, recordMember, equal⟩
    have suffixMember : some boundaryInput ∈
        (boundaryRecord :: boundaryLater).map causalInput? := by
      simp [boundaryRecord, causalInput?]
    exact separated _ prefixMember _ suffixMember rfl
  have betweenState :=
    candidate_query_batch_stays_inactive_before_distinct_boundary
      transitionFuel target base completeFoldAlphaQ16DagMemory blockAdvance
      between afterAdvance betweenAligned betweenOnly (by
        simpa [boundaryInput] using betweenDistinct) afterAdvanceTarget
      afterAdvanceUnseen afterAdvanceEmpty
  have betweenMemory :=
    candidate_query_batch_memory_preserved_before_distinct_boundary
      transitionFuel target base completeFoldAlphaQ16DagMemory blockAdvance
      between afterAdvance betweenAligned betweenOnly (by
        simpa [boundaryInput] using betweenDistinct) afterAdvanceTarget
      afterAdvanceUnseen afterAdvanceEmpty
  let boundaryPrior := preAdvance ++ orderedAdvance :: between
  let beforeBoundary := indexedStateAfterRecords transitionFuel controller
    boundaryPrior initial
  have beforeBoundaryExact : beforeBoundary =
      indexedStateAfterRecords transitionFuel controller between afterAdvance := by
    simp [beforeBoundary, boundaryPrior, afterAdvance, beforeAdvance,
      indexed_state_after_records_append, freshnessAdvance, orderedAdvance,
      UnifiedExposureRecord.answer]
  have beforeBoundaryTarget : beforeBoundary.memory.2.q16.advances target =
      some blockAdvance := by
    rw [beforeBoundaryExact]
    exact betweenState.1
  have beforeBoundaryUnseen :
      beforeBoundary.memory.2.queryBatch.boundarySeen = false := by
    rw [beforeBoundaryExact]
    exact betweenState.2.1
  have beforeBoundaryEmpty :
      beforeBoundary.memory.2.queryBatch.producers = [] := by
    rw [beforeBoundaryExact]
    exact betweenState.2.2
  have beforeBoundaryMemory : beforeBoundary.memory.2.queryBatch =
      inactiveQueryBatchPrefixMemory := by
    rw [beforeBoundaryExact, betweenMemory, afterAdvanceQueryBatch,
      beforeAdvanceMemory]
  have beforeBoundaryUsedEmpty :
      beforeBoundary.memory.2.queryBatch.usedSlots = ∅ := by
    rw [beforeBoundaryMemory]
    rfl
  have boundaryInputExact : unifiedInputBeforeAnswer? transitionFuel
      beforeBoundary.cursor = some boundaryInput := by
    have aligned := fullAligned boundaryPrior boundaryRecord boundaryLater
      (by simpa [boundaryPrior, boundaryRecord, orderedAdvance,
        List.append_assoc] using orderedRootExact)
    exact aligned_machine_record_has_exact_input transitionFuel
      beforeBoundary.cursor boundaryActor boundaryInput beforeQueryBatch.digest
      (by simpa [beforeBoundary, boundaryRecord,
        UnifiedExposureRecord.answer] using aligned)
  let afterBoundary := controller.afterAnswer transitionFuel beforeBoundary
    beforeQueryBatch.digest
  have armed : afterBoundary.memory.2.queryBatch =
      { boundarySeen := true
        producers :=
          [{ digest := beforeQueryBatch.digest, block := 0,
             sourceInput := boundaryInput }]
        usedSlots := beforeBoundary.memory.2.queryBatch.usedSlots } := by
    simp only [afterBoundary, controller,
      IndexedUnifiedExposureController.afterAnswer,
      extendControllerThroughCandidateQueryBatch, boundaryInputExact]
    exact exact_candidate_boundary_arms_query_batch target
      (completeFoldAlphaQ16DagMemory
        (baseIndexedState beforeBoundary).memory) beforeBoundary.memory.2
      boundaryInput beforeQueryBatch.digest blockAdvance beforeBoundaryUnseen
      beforeBoundaryEmpty beforeBoundaryTarget rfl
  have armedEmpty : afterBoundary.memory.2.queryBatch =
      { boundarySeen := true
        producers :=
          [{ digest := beforeQueryBatch.digest, block := 0,
             sourceInput := boundaryInput }]
        usedSlots := ∅ } := by
    rw [armed, beforeBoundaryUsedEmpty]
  refine ⟨finalTrial, target, blockAdvance, beforeQueryBatch.digest,
    beforeDomain, boundaryPrior, boundaryLater, boundaryActor, ?_,
    finalTrialExact, terminalExact, boundaryStart, ?_⟩
  · simpa [boundaryPrior, boundaryRecord, boundaryInput, orderedAdvance,
      List.append_assoc] using orderedRootExact
  · exact ⟨beforeBoundaryTarget, beforeBoundaryUnseen, beforeBoundaryEmpty,
      by simpa [base, controller, initial, beforeBoundary, afterBoundary,
        boundaryInput] using armedEmpty⟩

#print axioms exact_selected_candidate_query_batch_boundary_arms

end
end AspisK1.V7Tag73ExactCandidateQueryBatchBoundaryArming
