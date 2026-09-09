import AspisFormal.K1.V7Tag73ExactQueryBatchPrefixBoundaryOrigin

/-!
# Exact selected-q16 terminal to query-batch boundary

This file connects the terminal advance of the literal selected q16 branch to
the state absorbed by the deployed query-batch domain.  It is deterministic
source evidence; no random-oracle independence or logical-role classifier is
assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactSelectedQ16QueryBatchBoundary

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73CausalQ16CoordinateRouter
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerQ16InitialDigestMap
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactQueryBatchPrefixBoundaryOrigin
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The literal selected `runCandidate` supplies an ordered duplex chain
whose terminal digest is exactly the evaluator's post-q16 digest. -/
theorem exact_selected_q16_chain_reaches_after_q16
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
      fixedInstance sample) :
    ∃ producerInput initialDigest outputs advances,
      tableLookup (exactOperationalTable input) producerInput =
          some initialDigest ∧
      producerInput =
        bytes (exactOperationalRawTrace input).q16BaseDigest ++
          [domAbsorb, queryCandidateLabel,
            UInt8.ofNat
              (exactOperationalTape input).search.selectedCounter.val] ∧
      ExactRootOrderedQ16Chain input producerInput initialDigest outputs
        advances ∧
      outputs.length =
        (exactOperationalTape input).search.selectedSchedule.blocksUsed ∧
      advances.length = outputs.length ∧
      (exactOperationalQ16Evaluator input).afterQ16.digest =
        gammaTerminalDigest initialDigest advances := by
  let evaluator := exactOperationalQ16Evaluator input
  have q16Run := evaluator.q16Run
  rw [runQ16] at q16Run
  obtain ⟨beforeSelected, _earlierRun, selectedRun⟩ :=
    Option.bind_eq_some_iff.mp q16Run
  let spec := (q16TapeOfSearch
    (exactOperationalTape input).search).selected
  obtain ⟨afterCounter, outputs, afterBlocks, absorbRun, squeezeRun,
      afterExact, outputsLength, recordMember⟩ :=
    run_candidate_exposes_exact_record (exactOperationalTable input)
      beforeSelected evaluator.afterQ16 spec (by
        simpa [spec] using selectedRun)
  obtain ⟨advances, advancesLength, tableChain, terminalExact, _callsExact⟩ :=
    squeeze_many_coordinates_with_terminal (exactOperationalTable input)
      (.queryCandidate spec.counter) spec.outcome.blocksUsed afterCounter
      afterBlocks outputs squeezeRun
  let record : CandidateRecord :=
    { counter := spec.counter
      outcome := spec.outcome
      baseDigest := beforeSelected.digest
      endDigest := afterBlocks.digest
      blocks := outputs }
  have recordInAfterQ16 : record ∈ evaluator.afterQ16.candidates := by
    simpa [record] using recordMember
  have baseExact : beforeSelected.digest =
      (exactOperationalRawTrace input).q16BaseDigest := by
    simpa [record, evaluator] using
      exact_operational_q16_after_state_uses_shared_base input record
        recordInAfterQ16
  let producerInput : ShaInput :=
    bytes (exactOperationalRawTrace input).q16BaseDigest ++
      [domAbsorb, queryCandidateLabel,
        UInt8.ofNat (exactOperationalTape input).search.selectedCounter.val]
  have producerLookup : tableLookup (exactOperationalTable input)
      producerInput = some afterCounter.digest := by
    have lookup := absorb_step_exposes_literal_lookup
      (exactOperationalTable input) beforeSelected afterCounter
        (.queryCandidate spec.counter) absorbRun
    simpa [producerInput, spec, q16TapeOfSearch, baseExact,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data,
      List.append_assoc] using lookup
  have ordered : ExactRootOrderedQ16Chain input producerInput
      afterCounter.digest outputs advances :=
    gamma_table_coordinate_chain_has_exact_root_order transitionRoom input
      producerInput afterCounter.digest producerLookup tableChain
  have afterDigest : evaluator.afterQ16.digest = afterBlocks.digest := by
    rw [afterExact]
  refine ⟨producerInput, afterCounter.digest, outputs, advances,
    producerLookup, rfl, ordered, ?_, advancesLength,
    afterDigest.trans terminalExact⟩
  simpa [spec, q16TapeOfSearch, CandidateOutcome.blocksUsed] using
    outputsLength

/-- The frontier-count check between q16 and the query-batch domain is
state-preserving, so the domain absorption starts at the exact post-q16
digest. -/
theorem exact_query_batch_domain_starts_at_after_q16
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ (beforeDomain beforeQueryBatch : EvalState),
      beforeDomain.digest =
          (exactOperationalQ16Evaluator input).afterQ16.digest ∧
      tableLookup (exactOperationalTable input)
          (bytes beforeDomain.digest ++
            [domAbsorb, queryBatchChallengeLabel]) =
        some beforeQueryBatch.digest := by
  let evaluator := exactOperationalQ16Evaluator input
  have splitRun := evaluator.afterQ16Run
  rw [after_accepted_query_scan_query_batch_split] at splitRun
  obtain ⟨beforeQueryBatch, prefixRun, _restRun⟩ :=
    (run_machine_events_work_erased_append_iff
      (exactOperationalTable input) beforeQueryBatchChallengeEvents
      (challengeEvent (exactOperationalTape input).messages .queryBatch ::
        afterQueryBatchChallengeEvents
          (exactOperationalTape input).messages)
      evaluator.afterQ16 evaluator.finalState).mp splitRun
  obtain ⟨beforeDomain, frontierRun, domainRun⟩ :=
    (run_machine_events_work_erased_append_iff
      (exactOperationalTable input) [.check .frontierCount]
      [.absorb .queryBatchDomain] evaluator.afterQ16 beforeQueryBatch).mp
        (by simpa [beforeQueryBatchChallengeEvents] using prefixRun)
  have beforeExact : evaluator.afterQ16 = beforeDomain := by
    simpa [runMachineEventsWorkErased, runMachineEventWorkErased] using
      frontierRun
  simp only [runMachineEventsWorkErased] at domainRun
  obtain ⟨afterDomain, absorbRun, domainDone⟩ :=
    Option.bind_eq_some_iff.mp domainRun
  have afterDomainExact : afterDomain = beforeQueryBatch := by
    simpa [runMachineEventsWorkErased] using Option.some.inj domainDone
  subst afterDomain
  have lookup := absorb_step_exposes_literal_lookup
    (exactOperationalTable input) beforeDomain beforeQueryBatch
      .queryBatchDomain absorbRun
  refine ⟨beforeDomain, beforeQueryBatch, ?_, ?_⟩
  · exact congrArg EvalState.digest beforeExact.symm
  · simpa [AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using lookup

/-- Combined source endpoint: the selected q16 advance chain terminates at
the exact digest used to construct the query-batch-domain input. -/
theorem exact_selected_q16_terminal_is_query_batch_boundary
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
      fixedInstance sample) :
    ∃ (producerInput : ShaInput) (initialDigest : Digest256)
        (outputs advances : List Digest256)
        (beforeDomain beforeQueryBatch : EvalState),
      tableLookup (exactOperationalTable input) producerInput =
          some initialDigest ∧
      producerInput =
        bytes (exactOperationalRawTrace input).q16BaseDigest ++
          [domAbsorb, queryCandidateLabel,
            UInt8.ofNat
              (exactOperationalTape input).search.selectedCounter.val] ∧
      ExactRootOrderedQ16Chain input producerInput initialDigest outputs
        advances ∧
      outputs.length =
        (exactOperationalTape input).search.selectedSchedule.blocksUsed ∧
      advances.length = outputs.length ∧
      gammaTerminalDigest initialDigest advances = beforeDomain.digest ∧
      tableLookup (exactOperationalTable input)
          (bytes beforeDomain.digest ++
            [domAbsorb, queryBatchChallengeLabel]) =
        some beforeQueryBatch.digest := by
  obtain ⟨producerInput, initialDigest, outputs, advances, producerLookup,
      producerExact, ordered, outputsLength, advancesLength, terminalExact⟩ :=
    exact_selected_q16_chain_reaches_after_q16 transitionRoom input
  obtain ⟨beforeDomain, beforeQueryBatch, boundaryStart, boundaryLookup⟩ :=
    exact_query_batch_domain_starts_at_after_q16 input
  exact ⟨producerInput, initialDigest, outputs, advances, beforeDomain,
    beforeQueryBatch, producerLookup, producerExact, ordered, outputsLength,
    advancesLength, terminalExact.symm.trans boundaryStart.symm,
    boundaryLookup⟩

/-- The terminal source fact names one concrete member of the 512-slot cover.
Its block is the last consumed block of the selected schedule, and its advance
answer is exactly the state used by the query-batch-domain input. -/
theorem exact_selected_q16_terminal_has_candidate_slot
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
      fixedInstance sample) :
    ∃ (target : Q16DigestSlot) (producerInput blockProducerInput : ShaInput)
        (initialDigest blockDigest blockAdvance : Digest256)
        (prefixOutputs prefixAdvances : List Digest256)
        (beforeDomain beforeQueryBatch : EvalState),
      target.1 = (exactOperationalTape input).search.selectedCounter ∧
      target.2.val + 1 =
        (exactOperationalTape input).search.selectedSchedule.blocksUsed ∧
      prefixOutputs.length = target.2.val ∧
      tableLookup (exactOperationalTable input) producerInput =
        some initialDigest ∧
      producerInput =
        bytes (exactOperationalRawTrace input).q16BaseDigest ++
          [domAbsorb, queryCandidateLabel,
            UInt8.ofNat target.1.val] ∧
      ExactRootOrderedQ16Chain input producerInput initialDigest prefixOutputs
        prefixAdvances ∧
      gammaTerminalDigest initialDigest prefixAdvances = blockDigest ∧
      tableLookup (exactOperationalTable input) blockProducerInput =
        some blockDigest ∧
      tableLookup (exactOperationalTable input)
          (gammaAdvanceInput blockDigest) = some blockAdvance ∧
      (∃ before middle after,
        exactRootFreshQueries input =
          before ++ (blockProducerInput, blockDigest) :: middle ++
            (gammaAdvanceInput blockDigest, blockAdvance) :: after) ∧
      blockAdvance = beforeDomain.digest ∧
      tableLookup (exactOperationalTable input)
          (bytes beforeDomain.digest ++
            [domAbsorb, queryBatchChallengeLabel]) =
        some beforeQueryBatch.digest := by
  obtain ⟨producerInput, initialDigest, outputs, advances, beforeDomain,
      beforeQueryBatch, producerLookup, producerExact, chain, outputsLength,
      advancesLength, terminalExact, boundaryLookup⟩ :=
    exact_selected_q16_terminal_is_query_batch_boundary transitionRoom input
  have nonempty : 0 < outputs.length := by
    rw [outputsLength]
    have positive :=
      (exactOperationalTape input).search.selectedSchedule.atLeastTwoBlocks
    omega
  obtain ⟨prefixOutputs, prefixAdvances, blockProducerInput, blockDigest,
      _blockOutput, blockAdvance, _outputsExact, advancesExact, prefixChain,
      blockProducerLookup, _blockOutputLookup, blockAdvanceLookup, blockOrder,
      predecessorExact, lastExact⟩ :=
    exact_root_ordered_q16_chain_unsnoc_with_order chain nonempty
  have prefixLength : prefixAdvances.length + 1 =
      (exactOperationalTape input).search.selectedSchedule.blocksUsed := by
    have advanceCount : advances.length =
        (exactOperationalTape input).search.selectedSchedule.blocksUsed :=
      advancesLength.trans outputsLength
    rw [advancesExact] at advanceCount
    simpa using advanceCount
  have targetBound : prefixAdvances.length < 8 := by
    have cap :=
      (exactOperationalTape input).search.selectedSchedule.withinSixtyFourDraws
    omega
  let target : Q16DigestSlot :=
    ((exactOperationalTape input).search.selectedCounter,
      ⟨prefixAdvances.length, targetBound⟩)
  have prefixPairLength : prefixOutputs.length = prefixAdvances.length := by
    have lengths := exact_root_ordered_q16_chain_lengths prefixChain
    exact lengths.symm
  refine ⟨target, producerInput, blockProducerInput, initialDigest, blockDigest,
    blockAdvance, prefixOutputs, prefixAdvances, beforeDomain,
    beforeQueryBatch, rfl, ?_, ?_, producerLookup, ?_, prefixChain,
    predecessorExact, blockProducerLookup, blockAdvanceLookup, blockOrder, ?_,
    boundaryLookup⟩
  · simpa [target] using prefixLength
  · simpa [target] using prefixPairLength
  · simpa [target] using producerExact
  · exact lastExact.symm.trans terminalExact

#print axioms exact_selected_q16_chain_reaches_after_q16
#print axioms exact_query_batch_domain_starts_at_after_q16
#print axioms exact_selected_q16_terminal_is_query_batch_boundary
#print axioms exact_selected_q16_terminal_has_candidate_slot

end
end AspisK1.V7Tag73ExactSelectedQ16QueryBatchBoundary
