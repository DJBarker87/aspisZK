import AspisFormal.K1.V7Tag73ExactCandidateQueryBatchArmedContext

/-!
# Recursive routing of the selected candidate query batch

The exact twelve-block duplex certificate is replayed through the armed
post-boundary controller.  Each output and advance receives its pre-answer
logical slot, and each advance installs the producer used by the next block.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactCandidateQueryBatchChainRouting

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73CandidateDirectedQueryBatchController
open AspisK1.V7Tag73CandidateQueryBatchArmedController
open AspisK1.V7Tag73CandidateQueryBatchProducerInvariant
open AspisK1.V7Tag73CandidateQueryBatchSlotFreshness
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73CausalFoldAlphaQ16QueryBatchController
open AspisK1.V7Tag73ExactCandidateQueryBatchArmedContext
open AspisK1.V7Tag73ExactCandidateQueryBatchControllerProjection
open AspisK1.V7Tag73ExactCandidateQueryBatchProducerAvailability
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaQ16OperationalRealization
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- State digest feeding block `index` of a duplex chain. -/
def gammaChainState : Digest256 → List Digest256 → Nat → Digest256
  | initial, _, 0 => initial
  | initial, next :: rest, index + 1 => gammaChainState next rest index
  | initial, [], _ + 1 => initial

/-- Full source-facing witness for one output/advance child of a ready
producer. -/
theorem armed_query_batch_ready_child_has_preferred
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
    (aligned : IndexedRecordsAligned transitionFuel
      (armedQueryBatchController transitionFuel) initial suffix)
    (onlyMachine : OnlyMachineFreshRecords suffix)
    (inputNodup : (suffix.map causalInput?).Nodup)
    (answerNodup :
      (suffix.map UnifiedExposureRecord.answer).Nodup)
    (initialInvariant : ArmedQueryBatchProducerInvariant initial.memory)
    (sourceDisjoint : ∀ candidate ∈ initial.memory.producers,
      some candidate.sourceInput ∉ suffix.map causalInput?)
    (digestDisjoint : ∀ candidate ∈ initial.memory.producers,
      candidate.digest ∉ suffix.map UnifiedExposureRecord.answer)
    (initialUsedEmpty : initial.memory.usedSlots = ∅)
    (producer : QueryBatchPrefixProducer)
    (ready : ArmedQueryBatchProducerReady transitionFuel suffix initial
      boundaryInput boundaryDigest producer)
    (isAdvance : Bool) (childAnswer : Digest256)
    (ordered : ∃ before middle after,
      exactRootFreshQueries input =
        before ++ (producer.sourceInput, producer.digest) :: middle ++
          (bytes producer.digest ++
            [if isAdvance then domAdvance else domSqueeze], childAnswer) ::
              after) :
    ∃ childPrefix childLater childActor,
      suffix = childPrefix ++
        (.machineFresh childActor
          (bytes producer.digest ++
            [if isAdvance then domAdvance else domSqueeze]) childAnswer :
          UnifiedExposureRecord) :: childLater ∧
      producer ∈
        (indexedStateAfterRecords transitionFuel
          (armedQueryBatchController transitionFuel) childPrefix
          initial).memory.producers ∧
      ArmedQueryBatchProducerInvariant
        (indexedStateAfterRecords transitionFuel
          (armedQueryBatchController transitionFuel) childPrefix
          initial).memory ∧
      unifiedInputBeforeAnswer? transitionFuel
        (indexedStateAfterRecords transitionFuel
          (armedQueryBatchController transitionFuel) childPrefix
          initial).cursor =
        some (bytes producer.digest ++
          [if isAdvance then domAdvance else domSqueeze]) ∧
      (producer.block, isAdvance) ∉
        (indexedStateAfterRecords transitionFuel
          (armedQueryBatchController transitionFuel) childPrefix
          initial).memory.usedSlots ∧
      armedQueryBatchPreferredSlot transitionFuel
        (indexedStateAfterRecords transitionFuel
          (armedQueryBatchController transitionFuel) childPrefix
          initial) = some (producer.block, isAdvance) := by
  let childInput := bytes producer.digest ++
    [if isAdvance then domAdvance else domSqueeze]
  obtain ⟨childPrefix, childLater, childActor, childExact, producerMember⟩ :=
    armed_query_batch_ready_producer_available_before_child input boundaryPrior
      suffix boundaryActor boundaryInput boundaryDigest rootExact initial
        producer ready childInput childAnswer (by simpa [childInput] using ordered)
  let childRecord : UnifiedExposureRecord :=
    .machineFresh childActor childInput childAnswer
  have invariant := armed_query_batch_invariant_at_record_prefix
    transitionFuel suffix initial childPrefix childLater childRecord (by
      simpa [childRecord, childInput] using childExact) aligned onlyMachine
        inputNodup answerNodup initialInvariant sourceDisjoint digestDisjoint
  have childAligned := aligned childPrefix childRecord childLater (by
    simpa [childRecord, childInput] using childExact)
  have cursorInput : unifiedInputBeforeAnswer? transitionFuel
      (indexedStateAfterRecords transitionFuel
        (armedQueryBatchController transitionFuel) childPrefix initial).cursor =
      some childInput :=
    aligned_machine_record_has_exact_input transitionFuel _ childActor
      childInput childAnswer (by
        simpa [childRecord, UnifiedExposureRecord.answer] using childAligned)
  have initialFresh : (producer.block, isAdvance) ∉
      initial.memory.usedSlots := by
    rw [initialUsedEmpty]
    simp
  have unused := armed_query_batch_live_child_slot_unused transitionFuel suffix
    initial childPrefix childLater childActor childInput childAnswer producer
      isAdvance (by simpa [childInput, childRecord] using childExact) aligned
      onlyMachine inputNodup initialFresh invariant producerMember (by
        simp [childInput])
  have preferred : armedQueryBatchPreferredSlot transitionFuel
      (indexedStateAfterRecords transitionFuel
        (armedQueryBatchController transitionFuel) childPrefix initial) =
      some (producer.block, isAdvance) := by
    cases isAdvance with
    | false =>
        apply armed_query_batch_output_preferred_of_producer transitionFuel _
          producer invariant producerMember (by simpa using unused)
        simpa [childInput] using cursorInput
    | true =>
        apply armed_query_batch_advance_preferred_of_producer transitionFuel _
          producer invariant producerMember (by simpa using unused)
        simpa [childInput] using cursorInput
  exact ⟨childPrefix, childLater, childActor, by
    simpa [childInput] using childExact, producerMember, invariant, by
      simpa [childInput] using cursorInput, unused, preferred⟩

/-- Recursive exact-root fold.  Every consumed output and advance in the
query-batch chain receives the corresponding `(block, side)` label. -/
theorem exact_ordered_armed_query_batch_chain_has_preferred_slots
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
    (aligned : IndexedRecordsAligned transitionFuel
      (armedQueryBatchController transitionFuel) initial suffix)
    (onlyMachine : OnlyMachineFreshRecords suffix)
    (inputNodup : (suffix.map causalInput?).Nodup)
    (answerNodup :
      (suffix.map UnifiedExposureRecord.answer).Nodup)
    (initialInvariant : ArmedQueryBatchProducerInvariant initial.memory)
    (sourceDisjoint : ∀ candidate ∈ initial.memory.producers,
      some candidate.sourceInput ∉ suffix.map causalInput?)
    (digestDisjoint : ∀ candidate ∈ initial.memory.producers,
      candidate.digest ∉ suffix.map UnifiedExposureRecord.answer)
    (initialUsedEmpty : initial.memory.usedSlots = ∅) :
    ∀ {producerInput : ShaInput} {digest : Digest256}
      {outputs advances : List Digest256}
      (block : Fin 12)
      (chain : ExactRootOrderedQ16Chain input producerInput digest outputs
        advances)
      (lengthCap : block.val + outputs.length ≤ 12)
      (ready : ArmedQueryBatchProducerReady transitionFuel suffix initial
        boundaryInput boundaryDigest
        (QueryBatchPrefixProducer.mk digest block producerInput)),
      (∀ index (inOutputs : index < outputs.length),
        ∃ outputPrefix later outputActor,
          suffix = outputPrefix ++
            (.machineFresh outputActor
              (bytes (gammaChainState digest advances index) ++ [domSqueeze])
              outputs[index] : UnifiedExposureRecord) :: later ∧
          armedQueryBatchPreferredSlot transitionFuel
            (indexedStateAfterRecords transitionFuel
              (armedQueryBatchController transitionFuel) outputPrefix
              initial) =
            some (⟨block.val + index,
              (Nat.add_lt_add_left inOutputs block.val).trans_le lengthCap⟩,
              false)) ∧
      (∀ index (inAdvances : index < advances.length),
        ∃ advancePrefix later advanceActor,
          suffix = advancePrefix ++
            (.machineFresh advanceActor
              (bytes (gammaChainState digest advances index) ++ [domAdvance])
              advances[index] : UnifiedExposureRecord) :: later ∧
          armedQueryBatchPreferredSlot transitionFuel
            (indexedStateAfterRecords transitionFuel
              (armedQueryBatchController transitionFuel) advancePrefix
              initial) =
            some (⟨block.val + index,
              by
                have lengths := exact_root_ordered_q16_chain_lengths chain
                rw [lengths] at inAdvances
                exact (Nat.add_lt_add_left inAdvances block.val).trans_le
                  lengthCap⟩, true)) := by
  intro producerInput digest outputs advances block chain lengthCap ready
  induction chain generalizing block with
  | done producerInput digest producerFound =>
      constructor <;> intro index impossible <;> simp at impossible
  | @next producerInput digest output advanced outputs advances producerFound
      outputFound advanceFound producerBeforeOutput producerBeforeAdvance tail ih =>
      let producer := QueryBatchPrefixProducer.mk digest block producerInput
      have outputWitness := armed_query_batch_ready_child_has_preferred input
        boundaryPrior suffix boundaryActor boundaryInput boundaryDigest rootExact
        initial aligned onlyMachine inputNodup answerNodup initialInvariant
        sourceDisjoint digestDisjoint initialUsedEmpty producer (by
          simpa [producer] using ready) false output (by
            simpa [producer, gammaOutputInput] using producerBeforeOutput)
      have advanceWitness := armed_query_batch_ready_child_has_preferred input
        boundaryPrior suffix boundaryActor boundaryInput boundaryDigest rootExact
        initial aligned onlyMachine inputNodup answerNodup initialInvariant
        sourceDisjoint digestDisjoint initialUsedEmpty producer (by
          simpa [producer] using ready) true advanced (by
            simpa [producer, gammaAdvanceInput] using producerBeforeAdvance)
      obtain ⟨advancePrefix, advanceLater, advanceActor, advanceExact,
          producerMember, advanceInvariant, advanceInputExact, advanceUnused,
          advancePreferred⟩ := advanceWitness
      by_cases outputsEmpty : outputs = []
      · subst outputs
        have advancesEmpty : advances = [] := by
          apply List.length_eq_zero_iff.mp
          simpa using exact_root_ordered_q16_chain_lengths tail
        subst advances
        constructor
        · intro index inOutputs
          have indexZero : index = 0 := by simpa using inOutputs
          subst index
          obtain ⟨outputPrefix, later, outputActor, outputExact,
              outputMember, outputInvariant, outputInputExact, outputUnused,
              outputPreferred⟩ := outputWitness
          exact ⟨outputPrefix, later, outputActor, by
            simpa [producer, gammaChainState, gammaOutputInput] using
              outputExact, by
            simpa [producer] using outputPreferred⟩
        · intro index inAdvances
          have indexZero : index = 0 := by simpa using inAdvances
          subst index
          exact ⟨advancePrefix, advanceLater, advanceActor, by
            simpa [producer, gammaChainState, gammaAdvanceInput] using
              advanceExact, by
            simpa [producer] using advancePreferred⟩
      · have tailPositive : 0 < outputs.length :=
          Nat.pos_of_ne_zero (fun lengthZero =>
            outputsEmpty (List.length_eq_zero_iff.mp lengthZero))
        have nextBound : block.val + 1 < 12 := by
          simp only [List.length_cons] at lengthCap
          omega
        let nextBlock : Fin 12 := ⟨block.val + 1, nextBound⟩
        let nextProducer := QueryBatchPrefixProducer.mk advanced nextBlock
          (gammaAdvanceInput digest)
        let advanceRecord : UnifiedExposureRecord :=
          .machineFresh advanceActor (gammaAdvanceInput digest) advanced
        have nextMember : nextProducer ∈
            (indexedStateAfterRecords transitionFuel
              (armedQueryBatchController transitionFuel)
              (advancePrefix ++ [advanceRecord]) initial).memory.producers := by
          have installed := armed_query_batch_advance_installs_successor
            (indexedStateAfterRecords transitionFuel
              (armedQueryBatchController transitionFuel) advancePrefix
              initial).memory producer advanced nextBound advanceInvariant
                producerMember
          rw [indexed_state_after_records_append,
            indexed_state_after_records_cons, indexed_state_after_records_nil]
          change nextProducer ∈
            (armedQueryBatchAfterMemory transitionFuel
              (indexedStateAfterRecords transitionFuel
                (armedQueryBatchController transitionFuel) advancePrefix
                  initial) advanced).producers
          have advanceInputExact' : unifiedInputBeforeAnswer? transitionFuel
              (indexedStateAfterRecords transitionFuel
                (armedQueryBatchController transitionFuel) advancePrefix
                  initial).cursor = some (gammaAdvanceInput digest) := by
            simpa [producer, gammaAdvanceInput] using advanceInputExact
          rw [show armedQueryBatchAfterMemory transitionFuel
              (indexedStateAfterRecords transitionFuel
                (armedQueryBatchController transitionFuel) advancePrefix
                  initial) advanced =
              armedQueryBatchAfterInput
                (indexedStateAfterRecords transitionFuel
                  (armedQueryBatchController transitionFuel) advancePrefix
                    initial).memory
                (gammaAdvanceInput digest) advanced by
            simp [armedQueryBatchAfterMemory, advanceInputExact']]
          simpa [producer, nextProducer, nextBlock, gammaAdvanceInput] using
            installed
        have nextReady : ArmedQueryBatchProducerReady transitionFuel suffix
            initial boundaryInput boundaryDigest nextProducer := by
          apply ArmedQueryBatchProducerReady.recorded nextProducer
            advancePrefix advanceLater advanceActor
          · change suffix = advancePrefix ++
              (.machineFresh advanceActor (gammaAdvanceInput digest) advanced :
                UnifiedExposureRecord) :: advanceLater
            simpa [producer, gammaAdvanceInput] using advanceExact
          · simpa [advanceRecord] using nextMember
        have tailCap : nextBlock.val + outputs.length ≤ 12 := by
          simp [nextBlock]
          simp only [List.length_cons] at lengthCap
          omega
        have tailResult := ih nextBlock tailCap (by
          simpa [nextProducer, nextBlock, gammaAdvanceInput] using nextReady)
        constructor
        · intro index inOutputs
          cases index with
          | zero =>
              obtain ⟨outputPrefix, later, outputActor, outputExact,
                  outputMember, outputInvariant, outputInputExact, outputUnused,
                  outputPreferred⟩ := outputWitness
              exact ⟨outputPrefix, later, outputActor, by
                simpa [producer, gammaChainState, gammaOutputInput] using
                  outputExact, by
                simpa [producer] using outputPreferred⟩
          | succ index =>
              have tailIndex : index < outputs.length := by
                simpa using inOutputs
              obtain ⟨outputPrefix, later, outputActor, outputExact,
                preferred⟩ := tailResult.1 index tailIndex
              refine ⟨outputPrefix, later, outputActor, by
                simpa [gammaChainState, nextProducer, nextBlock] using
                  outputExact, ?_⟩
              rw [preferred]
              congr 2
              apply Fin.ext
              simp [nextBlock]
              omega
        · intro index inAdvances
          cases index with
          | zero =>
              exact ⟨advancePrefix, advanceLater, advanceActor, by
                simpa [producer, gammaChainState, gammaAdvanceInput] using
                  advanceExact, by
                simpa [producer] using advancePreferred⟩
          | succ index =>
              have tailIndex : index < advances.length := by
                simpa using inAdvances
              obtain ⟨advancePrefix, later, advanceActor, advanceExact,
                preferred⟩ := tailResult.2 index tailIndex
              refine ⟨advancePrefix, later, advanceActor, by
                simpa [gammaChainState, nextProducer, nextBlock] using
                  advanceExact, ?_⟩
              rw [preferred]
              congr 2
              apply Fin.ext
              simp [nextBlock]
              omega

/-- The selected accepted candidate's complete deployed query-batch chain is
routed by the armed post-boundary controller.  The theorem exposes only the
actual sampler blocks consumed by the accepted execution; unused capacity up
to the twelve-block deployment cap is not assigned a causal role. -/
theorem exact_selected_candidate_armed_query_batch_has_preferred_slots
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
        ((exactOperationalTape input).messages.challengeUse
          .queryBatch).blocksUsed ∧
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
              boundaryPrior
                (exactCandidateDirectedQueryBatchInitialState input))
            queryBatchDigest) ∧
      initial.memory =
        { boundarySeen := true
          producers :=
            [{ digest := queryBatchDigest, block := 0,
               sourceInput := bytes blockAdvance ++
                 [domAbsorb, queryBatchChallengeLabel] }]
          usedSlots := ∅ } ∧
      (∀ index (inOutputs : index < outputs.length),
        ∃ (outputPrefix later : List UnifiedExposureRecord)
            (outputActor : QueryActor) (slot : Fin 12),
          suffix = outputPrefix ++
            (.machineFresh outputActor
              (bytes (gammaChainState queryBatchDigest advances index) ++
                [domSqueeze]) outputs[index] : UnifiedExposureRecord) ::
              later ∧
          armedQueryBatchPreferredSlot transitionFuel
            (indexedStateAfterRecords transitionFuel
              (armedQueryBatchController transitionFuel) outputPrefix
              initial) = some (slot, false) ∧
          slot.val = index) ∧
      (∀ index (inAdvances : index < advances.length),
        ∃ (advancePrefix later : List UnifiedExposureRecord)
            (advanceActor : QueryActor) (slot : Fin 12),
          suffix = advancePrefix ++
            (.machineFresh advanceActor
              (bytes (gammaChainState queryBatchDigest advances index) ++
                [domAdvance]) advances[index] : UnifiedExposureRecord) ::
              later ∧
          armedQueryBatchPreferredSlot transitionFuel
            (indexedStateAfterRecords transitionFuel
              (armedQueryBatchController transitionFuel) advancePrefix
              initial) = some (slot, true) ∧
          slot.val = index) := by
  obtain ⟨finalTrial, target, blockAdvance, queryBatchDigest, outputs,
      advances, boundaryPrior, suffix, boundaryActor, initial, rootExact,
      finalTrialExact, targetCounter, targetBlock, chain, outputsLength,
      advancesLength, q16TerminalExact, initialExact,
      initialMemory, aligned, onlyMachine, inputNodup, answerNodup,
      sourceDisjoint, digestDisjoint, invariant, initialReady⟩ :=
    exact_selected_candidate_has_armed_query_batch_context transitionRoom input
      foldTrial boundaryIndex
  have lengthCap : (0 : Fin 12).val + outputs.length ≤ 12 := by
    simp only [Fin.val_zero, Nat.zero_add]
    rw [outputsLength]
    simpa [samplerMode, samplerBlockCap] using
      ((exactOperationalTape input).messages.challengeUse
        .queryBatch).withinDeployedCap
  obtain ⟨outputPreferred, advancePreferred⟩ :=
    exact_ordered_armed_query_batch_chain_has_preferred_slots input
      boundaryPrior suffix boundaryActor
      (bytes blockAdvance ++ [domAbsorb, queryBatchChallengeLabel])
      queryBatchDigest rootExact initial aligned onlyMachine inputNodup
      answerNodup invariant sourceDisjoint digestDisjoint (by
        rw [initialMemory]) (0 : Fin 12) chain lengthCap initialReady
  have plainLengthCap : outputs.length ≤ 12 := by
    simpa using lengthCap
  have outputResult : ∀ index (inOutputs : index < outputs.length),
      ∃ (outputPrefix later : List UnifiedExposureRecord)
          (outputActor : QueryActor) (slot : Fin 12),
        suffix = outputPrefix ++
          (.machineFresh outputActor
            (bytes (gammaChainState queryBatchDigest advances index) ++
              [domSqueeze]) outputs[index] : UnifiedExposureRecord) :: later ∧
        armedQueryBatchPreferredSlot transitionFuel
          (indexedStateAfterRecords transitionFuel
            (armedQueryBatchController transitionFuel) outputPrefix initial) =
          some (slot, false) ∧
        slot.val = index := by
    intro index inOutputs
    obtain ⟨outputPrefix, later, outputActor, outputExact, preferred⟩ :=
      outputPreferred index inOutputs
    let slot : Fin 12 := ⟨index, inOutputs.trans_le plainLengthCap⟩
    exact ⟨outputPrefix, later, outputActor, slot, outputExact, by
      simpa [slot] using preferred, rfl⟩
  have advanceResult : ∀ index (inAdvances : index < advances.length),
      ∃ (advancePrefix later : List UnifiedExposureRecord)
          (advanceActor : QueryActor) (slot : Fin 12),
        suffix = advancePrefix ++
          (.machineFresh advanceActor
            (bytes (gammaChainState queryBatchDigest advances index) ++
              [domAdvance]) advances[index] : UnifiedExposureRecord) :: later ∧
        armedQueryBatchPreferredSlot transitionFuel
          (indexedStateAfterRecords transitionFuel
            (armedQueryBatchController transitionFuel) advancePrefix initial) =
          some (slot, true) ∧
        slot.val = index := by
    intro index inAdvances
    obtain ⟨advancePrefix, later, advanceActor, advanceExact, preferred⟩ :=
      advancePreferred index inAdvances
    have indexOutputs : index < outputs.length := by
      simpa [advancesLength] using inAdvances
    let slot : Fin 12 := ⟨index, indexOutputs.trans_le plainLengthCap⟩
    exact ⟨advancePrefix, later, advanceActor, slot, advanceExact, by
      simpa [slot] using preferred, rfl⟩
  exact ⟨finalTrial, target, blockAdvance, queryBatchDigest, outputs, advances,
    boundaryPrior, suffix, boundaryActor, initial, rootExact, finalTrialExact,
    targetCounter, targetBlock, chain,
    outputsLength, advancesLength, q16TerminalExact, initialExact,
    initialMemory, outputResult, advanceResult⟩

#print axioms armed_query_batch_ready_child_has_preferred
#print axioms exact_ordered_armed_query_batch_chain_has_preferred_slots
#print axioms exact_selected_candidate_armed_query_batch_has_preferred_slots

end
end AspisK1.V7Tag73ExactCandidateQueryBatchChainRouting
