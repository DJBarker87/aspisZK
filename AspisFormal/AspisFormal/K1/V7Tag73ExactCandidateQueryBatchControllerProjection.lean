import AspisFormal.K1.V7Tag73CandidateDirectedQueryBatchController
import AspisFormal.K1.V7Tag73ExactCandidateQueryBatchAnchorInstalled
import AspisFormal.K1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
import AspisFormal.K1.V7Tag73FoldAlphaFinalWorkQ16ControllerProjection

/-!
# Selected candidate anchor in the complete base controller

The accepted-source q16 proof is stated for the standalone final-work/q16 DAG.
This file projects the identical root-record replay through the alpha product
and outer fold controller.  It therefore makes the installed last-block
producer available to the candidate-directed query-batch extension without
joining separately simulated executions.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCandidateQueryBatchControllerProjection

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerProjection
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactCandidateQueryBatchAnchorInstalled
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagQ16ChainRouting
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerProjection
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The complete 518-slot base controller used below. -/
def candidateCompleteBaseController
    {globalOracleCalls : Nat}
    (transitionFuel : Nat) (foldTrial finalTrial : Nat)
    (boundaryIndex : Nat) :
    IndexedUnifiedExposureController globalOracleCalls Digest256
      FoldAlphaFinalWorkQ16DigestSlot CompleteFoldAlphaQ16Memory :=
  foldAlphaFinalWorkQ16Controller foldTrial
    (alphaFinalWorkQ16DagController transitionFuel finalTrial
      (alphaZeroCausalController transitionFuel boundaryIndex))

/-- Initial state of one candidate-directed 542-slot experiment. -/
def exactCandidateDirectedQueryBatchInitialState
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (_input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    IndexedUnifiedExposureState (globalFull256OracleCallCap parameters)
      (ExtendedControllerMemory CompleteFoldAlphaQ16Memory) :=
  { exposureIndex := 0
    cursor := (exactPlainRomCursor configuration sample.1).erase
    memory :=
      ((false, (inactiveAlphaZeroMemory, inactiveDagMemory)),
        inactiveQueryBatchDagExtensionMemory) }

/-- Projecting the complete base memory after any literal record prefix gives
exactly the standalone final-work/q16 DAG replay used by the source proof. -/
theorem complete_base_dag_after_records_eq_standalone
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
    (boundaryIndex : Nat) (records : List UnifiedExposureRecord) :
    completeFoldAlphaQ16DagMemory
        (indexedStateAfterRecords transitionFuel
          (candidateCompleteBaseController transitionFuel foldTrial.val
            finalTrial.val boundaryIndex) records
          (exactFoldAlphaFinalWorkQ16InitialState input)).memory =
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel finalTrial) records
        (exactDagCandidateInitialState input)).memory := by
  unfold candidateCompleteBaseController
  change
    (finalWorkQ16IndexedState
      (underlyingIndexedState
        (indexedStateAfterRecords transitionFuel
          (foldAlphaFinalWorkQ16Controller foldTrial.val
            (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
              (alphaZeroCausalController transitionFuel boundaryIndex)))
          records (exactFoldAlphaFinalWorkQ16InitialState input)))).memory = _
  rw [underlying_indexed_state_after_fold_records]
  rw [final_work_q16_indexed_state_after_composed_records]
  rfl

/-- The candidate extension is observationally inert on the complete base DAG,
so its projected producer inventory is the same standalone exact replay. -/
theorem candidate_extended_dag_after_records_eq_standalone
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
    (boundaryIndex : Nat) (target : Q16DigestSlot)
    (records : List UnifiedExposureRecord) :
    completeFoldAlphaQ16DagMemory
        (baseIndexedState
          (indexedStateAfterRecords transitionFuel
            (extendControllerThroughCandidateQueryBatch transitionFuel target
              (candidateCompleteBaseController transitionFuel foldTrial.val
                finalTrial.val boundaryIndex)
              completeFoldAlphaQ16DagMemory)
            records (exactCandidateDirectedQueryBatchInitialState input)
          )).memory =
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel finalTrial) records
        (exactDagCandidateInitialState input)).memory := by
  rw [base_indexed_state_after_candidate_extended_records]
  change completeFoldAlphaQ16DagMemory
      (indexedStateAfterRecords transitionFuel
        (candidateCompleteBaseController transitionFuel foldTrial.val
          finalTrial.val boundaryIndex) records
        (exactFoldAlphaFinalWorkQ16InitialState input)).memory = _
  exact complete_base_dag_after_records_eq_standalone input foldTrial finalTrial
    boundaryIndex records

/-- The selected last q16 parent is present at the exact pre-advance prefix of
the complete fold/alpha/final-work/q16 controller. -/
theorem exact_selected_candidate_parent_available_in_complete_base
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
        (prior middle later : List UnifiedExposureRecord)
        (producerActor advanceActor : QueryActor),
      exactFixedRootRecords input.package.root =
        prior ++
          (.machineFresh producerActor blockProducerInput blockDigest :
            UnifiedExposureRecord) :: middle ++
          (.machineFresh advanceActor (gammaAdvanceInput blockDigest)
            blockAdvance : UnifiedExposureRecord) :: later ∧
      Q16DagProducer.mk blockDigest target blockProducerInput ∈
        (completeFoldAlphaQ16DagMemory
          (indexedStateAfterRecords transitionFuel
            (candidateCompleteBaseController transitionFuel foldTrial.val
              finalTrial.val boundaryIndex)
            (prior ++
              (.machineFresh producerActor blockProducerInput blockDigest :
                UnifiedExposureRecord) :: middle)
            (exactFoldAlphaFinalWorkQ16InitialState input)).memory).producers ∧
      target.1 = (exactOperationalTape input).search.selectedCounter ∧
      target.2.val + 1 =
        (exactOperationalTape input).search.selectedSchedule.blocksUsed ∧
      tableLookup (exactOperationalTable input)
          (gammaAdvanceInput blockDigest) = some blockAdvance ∧
      blockAdvance = beforeDomain.digest ∧
      tableLookup (exactOperationalTable input)
          (bytes beforeDomain.digest ++
            [domAbsorb, queryBatchChallengeLabel]) =
        some beforeQueryBatch.digest := by
  obtain ⟨finalTrial, target, blockProducerInput, blockDigest, blockAdvance,
      beforeDomain, beforeQueryBatch, targetCounter, targetBlock, installed,
      _producerLookup, advanceLookup, ordered, terminalExact,
      boundaryLookup⟩ :=
    exact_selected_candidate_query_batch_anchor_is_installed transitionRoom input
  obtain ⟨prior, middle, later, producerActor, advanceActor, recordsExact,
      available⟩ :=
    exact_dag_installed_producer_available_before_ordered_child input finalTrial
      (Q16DagProducer.mk blockDigest target blockProducerInput)
      (gammaAdvanceInput blockDigest) blockAdvance installed ordered
  refine ⟨finalTrial, target, blockProducerInput, blockDigest, blockAdvance,
    beforeDomain, beforeQueryBatch, prior, middle, later, producerActor,
    advanceActor, recordsExact, ?_, targetCounter, targetBlock, advanceLookup,
    terminalExact, boundaryLookup⟩
  rw [complete_base_dag_after_records_eq_standalone input foldTrial finalTrial
    boundaryIndex]
  exact available

#print axioms candidateCompleteBaseController
#print axioms exactCandidateDirectedQueryBatchInitialState
#print axioms complete_base_dag_after_records_eq_standalone
#print axioms candidate_extended_dag_after_records_eq_standalone
#print axioms exact_selected_candidate_parent_available_in_complete_base

end
end AspisK1.V7Tag73ExactCandidateQueryBatchControllerProjection
