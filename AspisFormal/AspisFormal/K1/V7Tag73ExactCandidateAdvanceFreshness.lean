import AspisFormal.K1.V7Tag73CandidateDirectedObserverProvenance
import AspisFormal.K1.V7Tag73CausalDagProducerInvariant
import AspisFormal.K1.V7Tag73ExactCandidateQueryBatchControllerProjection
import AspisFormal.K1.V7Tag73ExactFinalWorkPairControllerCompletion
import AspisFormal.K1.V7Tag73ExactFixedOperationalStateMap
import AspisFormal.K1.V7Tag73ExactProbabilityCoverageAudit

/-!
# Freshness of the selected candidate's terminal advance observation

The candidate observer is initially empty.  Before the selected terminal
advance record, that target slot is still empty: an earlier installation would
require another live DAG producer at the same slot, hence the same producer,
and would duplicate the exact terminal advance input in the fresh root trace.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCandidateAdvanceFreshness

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateDirectedObserverProvenance
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalDagProducerInvariant
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCandidateQueryBatchControllerProjection
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalStateMap
open AspisK1.V7Tag73ExactFoldAlphaQ16OperationalRealization
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactProbabilityCoverageAudit
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The exact accepted root trace is aligned with every fixed candidate slot
controller because all indexed controllers share the same cursor transition. -/
theorem exact_root_records_aligned_for_candidate_directed_controller
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
    (foldTrial finalTrial : ExactCompilerExposureTrial parameters)
    (boundaryIndex : Nat) (target : Q16DigestSlot) :
    IndexedRecordsAligned transitionFuel
      (extendControllerThroughCandidateQueryBatch transitionFuel target
        (candidateCompleteBaseController transitionFuel foldTrial.val
          finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory)
      (exactCandidateDirectedQueryBatchInitialState input)
      (exactFixedRootRecords input.package.root) := by
  let controller : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256
      (FoldAlphaFinalWorkQ16DigestSlot ⊕ GammaPrefixDigestSlot)
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory) :=
    extendControllerThroughCandidateQueryBatch transitionFuel target
      (candidateCompleteBaseController transitionFuel foldTrial.val
        finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory
  let rootTape := operationalTapeCoordinates
    (globalFull256OracleCallCap parameters) 1
    (unifiedFull256ExposureCap parameters)
    (exactCompilerOperationalIndexedTape parameters sample.2)
  have traceExact :
      runUnifiedExposureTrace transitionFuel
          (unifiedFull256ExposureCap parameters)
          (exactPlainRomCursor configuration sample.1).erase rootTape =
        (runExactPlainRom transitionFuel configuration sample).trace := by
    simpa [rootTape, exactCompilerUnifiedExposureTrace] using
      exact_compiler_unified_exposure_trace_is_actual_plain_rom_trace
        transitionFuel configuration sample
  have fullAligned := indexed_records_aligned_of_trace transitionFuel
    controller (exactCandidateDirectedQueryBatchInitialState input) rootTape
      (runExactPlainRom transitionFuel configuration sample).trace traceExact
  have fullSplit :
      (runExactPlainRom transitionFuel configuration sample).trace =
        [] ++ exactFixedRootRecords input.package.root ++
          (exactFixedComputedClientTailRun transitionFuel configuration sample
            input.package.root).trace := by
    rw [exact_fixed_operational_state_map_trace_is_full_trace transitionFuel
      configuration projection fixedInstance sample input.package]
    rfl
  have rootAligned := indexed_records_aligned_segment transitionFuel controller
    (exactCandidateDirectedQueryBatchInitialState input)
    (runExactPlainRom transitionFuel configuration sample).trace []
    (exactFixedRootRecords input.package.root)
    (exactFixedComputedClientTailRun transitionFuel configuration sample
      input.package.root).trace fullAligned fullSplit
  simpa only [indexed_state_after_records_nil, controller] using rootAligned

/-- Immediately before the selected terminal advance answer, its candidate
observer entry is still empty. -/
theorem exact_selected_candidate_advance_is_fresh
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
        (target : Q16DigestSlot) (blockProducerInput : ShaInput)
        (blockDigest blockAdvance : Digest256)
        (beforeDomain beforeQueryBatch : EvalState)
        (preAdvance later : List UnifiedExposureRecord)
        (advanceActor : QueryActor),
      exactFixedRootRecords input.package.root =
        preAdvance ++
          (.machineFresh advanceActor (gammaAdvanceInput blockDigest)
            blockAdvance : UnifiedExposureRecord) :: later ∧
      Q16DagProducer.mk blockDigest target blockProducerInput ∈
        (completeFoldAlphaQ16DagMemory
          (baseIndexedState
            (indexedStateAfterRecords transitionFuel
              (extendControllerThroughCandidateQueryBatch transitionFuel target
                (candidateCompleteBaseController transitionFuel foldTrial.val
                  finalTrial.val boundaryIndex)
                completeFoldAlphaQ16DagMemory)
              preAdvance
              (exactCandidateDirectedQueryBatchInitialState input))).memory
          ).producers ∧
      finalTrial =
        (exactAcceptedDagInstallation transitionRoom input).finalTrial ∧
      (indexedStateAfterRecords transitionFuel
        (extendControllerThroughCandidateQueryBatch transitionFuel target
          (candidateCompleteBaseController transitionFuel foldTrial.val
            finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory)
        preAdvance (exactCandidateDirectedQueryBatchInitialState input)
        ).memory.2.q16.advances target = none ∧
      tableLookup (exactOperationalTable input)
          (gammaAdvanceInput blockDigest) = some blockAdvance ∧
      blockAdvance = beforeDomain.digest ∧
      beforeDomain.digest =
        (exactOperationalQ16Evaluator input).afterQ16.digest ∧
      tableLookup (exactOperationalTable input)
          (bytes beforeDomain.digest ++
            [domAbsorb, queryBatchChallengeLabel]) =
        some beforeQueryBatch.digest := by
  obtain ⟨finalTrial, target, blockProducerInput, blockDigest, blockAdvance,
      beforeDomain, beforeQueryBatch, prior, middle, later, producerActor,
      advanceActor, recordsExact, selectedMember, _targetCounter, _targetBlock,
      finalTrialExact, advanceLookup, terminalExact, boundaryStart,
      boundaryLookup⟩ :=
    exact_selected_candidate_parent_available_in_complete_base transitionRoom
      input foldTrial boundaryIndex
  let producerRecord : UnifiedExposureRecord :=
    .machineFresh producerActor blockProducerInput blockDigest
  let advanceRecord : UnifiedExposureRecord :=
    .machineFresh advanceActor (gammaAdvanceInput blockDigest) blockAdvance
  let preAdvance := prior ++ producerRecord :: middle
  let base : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256
      FoldAlphaFinalWorkQ16DigestSlot CompleteFoldAlphaQ16Memory :=
    candidateCompleteBaseController transitionFuel foldTrial.val finalTrial.val
      boundaryIndex
  let controller := extendControllerThroughCandidateQueryBatch transitionFuel
    target base completeFoldAlphaQ16DagMemory
  let initial := exactCandidateDirectedQueryBatchInitialState input
  let reached := indexedStateAfterRecords transitionFuel controller preAdvance
    initial
  have rootExact : exactFixedRootRecords input.package.root =
      preAdvance ++ advanceRecord :: later := by
    simpa only [preAdvance, producerRecord, advanceRecord, List.cons_append,
      List.append_assoc] using recordsExact
  have targetAbsent : reached.memory.2.q16.advances target = none := by
    cases observed : reached.memory.2.q16.advances target with
    | none => rfl
    | some observedAnswer =>
        have fullAligned :=
          exact_root_records_aligned_for_candidate_directed_controller input
            foldTrial finalTrial boundaryIndex target
        have prefixAligned : IndexedRecordsAligned transitionFuel controller
            initial preAdvance := by
          apply indexed_records_aligned_segment transitionFuel controller initial
            (exactFixedRootRecords input.package.root) [] preAdvance
            (advanceRecord :: later)
          · simpa [controller, base, initial] using fullAligned
          · simpa using rootExact
        have prefixOnly : OnlyMachineFreshRecords preAdvance := by
          apply only_machine_fresh_records_segment
            (exactFixedRootRecords input.package.root) [] preAdvance
            (advanceRecord :: later) (exact_root_records_only_machine_fresh input)
          simpa using rootExact
        have initialAbsent : initial.memory.2.q16.advances target = none := by
          rfl
        have becamePresent : reached.memory.2.q16.advances target ≠ none := by
          rw [observed]
          simp
        obtain ⟨earlierPrior, earlierLater, earlierActor, earlierInput,
            earlierAnswer, earlierProducer, earlierExact, earlierMember,
            earlierSlot, earlierInputExact⟩ :=
          candidate_observed_advance_has_installing_record transitionFuel target
            base completeFoldAlphaQ16DagMemory preAdvance initial prefixAligned
            prefixOnly initialAbsent (by simpa [reached] using becamePresent)
        have earlierStandalone : earlierProducer ∈
            (indexedStateAfterRecords transitionFuel
              (exactDagTrialController transitionFuel finalTrial) earlierPrior
              (exactDagCandidateInitialState input)).memory.producers := by
          rw [← candidate_extended_dag_after_records_eq_standalone input
            foldTrial finalTrial boundaryIndex target earlierPrior]
          simpa [controller, base, initial] using earlierMember
        let earlierState := indexedStateAfterRecords transitionFuel
          (exactDagTrialController transitionFuel finalTrial) earlierPrior
          (exactDagCandidateInitialState input)
        have growth := dag_indexed_state_producers_prefix transitionFuel
          finalTrial.val
          ((.machineFresh earlierActor earlierInput earlierAnswer :
            UnifiedExposureRecord) :: earlierLater) earlierState
        have earlierAtEnd : earlierProducer ∈
            (indexedStateAfterRecords transitionFuel
              (exactDagTrialController transitionFuel finalTrial) preAdvance
              (exactDagCandidateInitialState input)).memory.producers := by
          have member := growth.subset (by
            simpa [earlierState] using earlierStandalone)
          rw [earlierExact, indexed_state_after_records_append]
          simpa [earlierState, exactDagTrialController,
            UnifiedExposureRecord.answer] using member
        have selectedStandalone : Q16DagProducer.mk blockDigest target
            blockProducerInput ∈
            (indexedStateAfterRecords transitionFuel
              (exactDagTrialController transitionFuel finalTrial) preAdvance
              (exactDagCandidateInitialState input)).memory.producers := by
          rw [← complete_base_dag_after_records_eq_standalone input foldTrial
            finalTrial boundaryIndex preAdvance]
          simpa [preAdvance, producerRecord] using selectedMember
        have invariant := exact_dag_candidate_prefix_producer_invariant input
          finalTrial preAdvance (advanceRecord :: later) rootExact
        have producerExact : earlierProducer =
            Q16DagProducer.mk blockDigest target blockProducerInput := by
          apply q16_dag_producer_eq_of_slot_eq earlierProducer
            (Q16DagProducer.mk blockDigest target blockProducerInput)
            (indexedStateAfterRecords transitionFuel
              (exactDagTrialController transitionFuel finalTrial) preAdvance
              (exactDagCandidateInitialState input)).memory.producers
            invariant.slotsNodup earlierAtEnd selectedStandalone
          simpa using earlierSlot
        have priorInputMember : some (gammaAdvanceInput blockDigest) ∈
            preAdvance.map causalInput? := by
          rw [earlierExact]
          simp [causalInput?, earlierInputExact, producerExact,
            gammaAdvanceInput]
        have rootNodup := exact_root_record_causal_inputs_nodup input
        rw [rootExact, List.map_append] at rootNodup
        have separated := (List.nodup_append.mp rootNodup).2.2
        have suffixInputMember : some (gammaAdvanceInput blockDigest) ∈
            (advanceRecord :: later).map causalInput? := by
          simp [advanceRecord, causalInput?]
        exact (separated _ priorInputMember _ suffixInputMember rfl).elim
  refine ⟨finalTrial, target, blockProducerInput, blockDigest, blockAdvance,
    beforeDomain, beforeQueryBatch, preAdvance, later, advanceActor, rootExact,
    ?_, finalTrialExact, targetAbsent, advanceLookup, terminalExact, boundaryStart,
    boundaryLookup⟩
  rw [candidate_extended_dag_after_records_eq_standalone input foldTrial
    finalTrial boundaryIndex target preAdvance]
  rw [← complete_base_dag_after_records_eq_standalone input foldTrial
    finalTrial boundaryIndex preAdvance]
  simpa [preAdvance, producerRecord] using selectedMember

#print axioms exact_root_records_aligned_for_candidate_directed_controller
#print axioms exact_selected_candidate_advance_is_fresh

end
end AspisK1.V7Tag73ExactCandidateAdvanceFreshness
