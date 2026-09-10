import AspisFormal.K1.V7Tag73ExactCandidateQueryBatchProducerAvailability

/-!
# Exact armed context for one selected Tag-73 query batch

One accepted-source witness supplies the fixed candidate, literal boundary,
post-boundary singleton producer, aligned remaining root trace, and complete
deployed duplex chain.  All freshness facts are derived from the exact root's
input/answer `Nodup` certificates.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCandidateQueryBatchArmedContext

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CandidateQueryBatchArmedController
open AspisK1.V7Tag73CandidateQueryBatchProducerInvariant
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalFoldAlphaFinalWorkQ16Coordinates
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73ExactCandidateAdvanceFreshness
open AspisK1.V7Tag73ExactCandidateQueryBatchChainAnchor
open AspisK1.V7Tag73ExactCandidateQueryBatchControllerProjection
open AspisK1.V7Tag73ExactCandidateQueryBatchProducerAvailability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaQ16OperationalRealization
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def ExactCandidateQueryBatchArmedContext
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
    (transitionRoom : 2 ≤ transitionFuel)
    (foldTrial : ExactCompilerExposureTrial parameters)
    (boundaryIndex : Nat) : Prop :=
  ∃ (finalTrial : ExactCompilerExposureTrial parameters)
      (target : Q16DigestSlot) (blockAdvance queryBatchDigest : Digest256)
      (outputs advances : List Digest256)
      (boundaryPrior suffix : List UnifiedExposureRecord)
      (boundaryActor : QueryActor)
      (initial : IndexedUnifiedExposureState
        (globalFull256OracleCallCap parameters)
        QueryBatchPrefixControllerMemory),
    exactFixedRootRecords input.package.root = boundaryPrior ++
      (.machineFresh boundaryActor
        (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
        queryBatchDigest : UnifiedExposureRecord) :: suffix ∧
    finalTrial =
      (exactAcceptedDagInstallation transitionRoom input).finalTrial ∧
    target.1 = (exactOperationalTape input).search.selectedCounter ∧
    target.2.val + 1 =
      (exactOperationalTape input).search.selectedSchedule.blocksUsed ∧
    ExactRootOrderedQ16Chain input
      (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
      queryBatchDigest outputs advances ∧
    outputs.length =
      ((exactOperationalTape input).messages.challengeUse .queryBatch).blocksUsed ∧
    advances.length = outputs.length ∧
    blockAdvance =
      (exactOperationalQ16Evaluator input).afterQ16.digest ∧
    initial = queryBatchIndexedState
      ((extendControllerThroughCandidateQueryBatch transitionFuel target
        (candidateCompleteBaseController transitionFuel foldTrial.val
          finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory
        ).afterAnswer transitionFuel
          (indexedStateAfterRecords transitionFuel
            (extendControllerThroughCandidateQueryBatch transitionFuel target
              (candidateCompleteBaseController transitionFuel foldTrial.val
                finalTrial.val boundaryIndex) completeFoldAlphaQ16DagMemory)
            boundaryPrior (exactCandidateDirectedQueryBatchInitialState input))
          queryBatchDigest) ∧
    initial.memory =
      { boundarySeen := true
        producers :=
          [{ digest := queryBatchDigest, block := 0,
             sourceInput := bytes blockAdvance ++
               [domAbsorb, queryBatchChallengeLabel] }]
        usedSlots := ∅ } ∧
    IndexedRecordsAligned transitionFuel
      (armedQueryBatchController transitionFuel) initial suffix ∧
    OnlyMachineFreshRecords suffix ∧
    (suffix.map causalInput?).Nodup ∧
    (suffix.map UnifiedExposureRecord.answer).Nodup ∧
    (∀ producer ∈ initial.memory.producers,
      some producer.sourceInput ∉ suffix.map causalInput?) ∧
    (∀ producer ∈ initial.memory.producers,
      producer.digest ∉ suffix.map UnifiedExposureRecord.answer) ∧
    ArmedQueryBatchProducerInvariant initial.memory ∧
    ArmedQueryBatchProducerReady transitionFuel suffix initial
      (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
      queryBatchDigest
      { digest := queryBatchDigest, block := 0,
        sourceInput := bytes blockAdvance ++
          [domAbsorb, queryBatchChallengeLabel] }

/-- Construct the exact post-boundary context from the selected accepted
candidate and deployed query-batch chain. -/
theorem exact_selected_candidate_has_armed_query_batch_context
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
    ExactCandidateQueryBatchArmedContext input transitionRoom foldTrial
      boundaryIndex := by
  obtain ⟨finalTrial, target, blockAdvance, queryBatchDigest, outputs,
      advances, boundaryPrior, suffix, boundaryActor, rootExact,
      finalTrialExact, targetCounter, targetBlock, chain, outputsLength,
      advancesLength, q16TerminalExact, targetExact, unseen,
      empty, armed⟩ :=
    exact_selected_candidate_arms_complete_query_batch_chain transitionRoom
      input foldTrial boundaryIndex
  let base : IndexedUnifiedExposureController
      (globalFull256OracleCallCap parameters) Digest256
      FoldAlphaFinalWorkQ16DigestSlot CompleteFoldAlphaQ16Memory :=
    candidateCompleteBaseController transitionFuel foldTrial.val
      finalTrial.val boundaryIndex
  let controller := extendControllerThroughCandidateQueryBatch transitionFuel
    target base completeFoldAlphaQ16DagMemory
  let fullInitial := exactCandidateDirectedQueryBatchInitialState input
  let beforeBoundary := indexedStateAfterRecords transitionFuel controller
    boundaryPrior fullInitial
  let afterBoundary := controller.afterAnswer transitionFuel beforeBoundary
    queryBatchDigest
  let initial := queryBatchIndexedState afterBoundary
  let boundaryInput :=
    bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel]
  let boundaryRecord : UnifiedExposureRecord :=
    .machineFresh boundaryActor boundaryInput queryBatchDigest
  let producer : QueryBatchPrefixProducer :=
    { digest := queryBatchDigest, block := 0, sourceInput := boundaryInput }
  have initialMemory : initial.memory =
      { boundarySeen := true, producers := [producer], usedSlots := ∅ } := by
    simpa [initial, queryBatchIndexedState, producer, boundaryInput, base,
      controller, fullInitial, beforeBoundary, afterBoundary] using armed
  have fullAligned :=
    exact_root_records_aligned_for_candidate_directed_controller input
      foldTrial finalTrial boundaryIndex target
  have suffixFullAligned : IndexedRecordsAligned transitionFuel controller
      afterBoundary suffix := by
    have restricted := indexed_records_aligned_segment transitionFuel
      controller fullInitial (exactFixedRootRecords input.package.root)
      (boundaryPrior ++ [boundaryRecord]) suffix [] (by
        simpa [controller, base, fullInitial] using fullAligned) (by
          simpa [boundaryRecord, boundaryInput, List.append_assoc] using
            rootExact)
    simpa [afterBoundary, beforeBoundary, boundaryRecord,
      indexed_state_after_records_append, controller, fullInitial,
      UnifiedExposureRecord.answer] using restricted
  have initialArmed : initial.memory.boundarySeen = true := by
    rw [initialMemory]
  have aligned : IndexedRecordsAligned transitionFuel
      (armedQueryBatchController transitionFuel) initial suffix := by
    exact candidate_aligned_records_project_to_armed_query_batch
      transitionFuel target base completeFoldAlphaQ16DagMemory suffix
        afterBoundary (by
          simpa [initial, queryBatchIndexedState] using initialArmed)
        (by simpa [controller, base] using suffixFullAligned)
  have onlyMachine : OnlyMachineFreshRecords suffix := by
    apply only_machine_fresh_records_segment
      (exactFixedRootRecords input.package.root)
      (boundaryPrior ++ [boundaryRecord]) suffix []
      (exact_root_records_only_machine_fresh input)
    simpa [boundaryRecord, boundaryInput, List.append_assoc] using rootExact
  have rootInputNodup := exact_root_record_causal_inputs_nodup input
  have rootAnswerNodup := exact_root_record_answers_nodup input
  have inputNodup : (suffix.map causalInput?).Nodup := by
    rw [rootExact, List.map_append] at rootInputNodup
    exact (List.nodup_cons.mp (List.nodup_append.mp rootInputNodup).2.1).2
  have answerNodup :
      (suffix.map UnifiedExposureRecord.answer).Nodup := by
    rw [rootExact, List.map_append] at rootAnswerNodup
    exact (List.nodup_cons.mp (List.nodup_append.mp rootAnswerNodup).2.1).2
  have sourceDisjoint : ∀ candidate ∈ initial.memory.producers,
      some candidate.sourceInput ∉ suffix.map causalInput? := by
    intro candidate member
    rw [initialMemory] at member
    simp only [List.mem_singleton] at member
    subst candidate
    rw [rootExact, List.map_append] at rootInputNodup
    have fresh := (List.nodup_cons.mp
      (List.nodup_append.mp rootInputNodup).2.1).1
    simpa [producer, boundaryRecord, boundaryInput, causalInput?] using fresh
  have digestDisjoint : ∀ candidate ∈ initial.memory.producers,
      candidate.digest ∉ suffix.map UnifiedExposureRecord.answer := by
    intro candidate member
    rw [initialMemory] at member
    simp only [List.mem_singleton] at member
    subst candidate
    rw [rootExact, List.map_append] at rootAnswerNodup
    have fresh := (List.nodup_cons.mp
      (List.nodup_append.mp rootAnswerNodup).2.1).1
    change queryBatchDigest ∉
      suffix.map UnifiedExposureRecord.answer at fresh
    simpa [producer] using fresh
  have invariant : ArmedQueryBatchProducerInvariant initial.memory := by
    apply singleton_armed_query_batch_invariant producer initial.memory
    · rw [initialMemory]
    · rw [initialMemory]
    · rfl
  have initialReady : ArmedQueryBatchProducerReady transitionFuel suffix
      initial boundaryInput queryBatchDigest producer := by
    apply ArmedQueryBatchProducerReady.boundary producer
    · rfl
    · rfl
    · rw [initialMemory]
      simp
  exact ⟨finalTrial, target, blockAdvance, queryBatchDigest, outputs,
    advances, boundaryPrior, suffix, boundaryActor, initial, by
      simpa [boundaryRecord, boundaryInput] using rootExact, finalTrialExact,
    targetCounter, targetBlock, chain,
    outputsLength, advancesLength, q16TerminalExact, rfl, by
      simpa [producer, boundaryInput] using initialMemory, aligned, onlyMachine,
    inputNodup, answerNodup, sourceDisjoint, digestDisjoint, invariant, by
      simpa [producer, boundaryInput] using initialReady⟩

#print axioms ExactCandidateQueryBatchArmedContext
#print axioms exact_selected_candidate_has_armed_query_batch_context

end
end AspisK1.V7Tag73ExactCandidateQueryBatchArmedContext
