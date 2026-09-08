import AspisFormal.K1.V7Tag73ExactCompilerGammaPrefixCoordinates
import AspisFormal.K1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
import AspisFormal.K1.V7Tag73ExactQ16CausalCoordinateOrder
import AspisFormal.K1.V7Tag73QueryBatchPrefixCausalController

/-!
# Exact source origin of the query-batch boundary

The accepted post-q16 execution absorbs the empty query-batch domain before
sampling the nonzero batching challenge.  This file exposes that literal
absorption, its returned digest, and the complete consumed duplex chain from
one evaluator witness.  These are the source facts needed to prove that the
pre-answer query-batch controller labels the real production coordinates.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactQueryBatchPrefixBoundaryOrigin

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73CheckedRefinementFullFutureFreePath
open AspisK1.V7Tag73AcceptedSemanticExecution
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ExactCompilerGammaPrefixCoordinates
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open AspisK1.V7Tag73ExactCompilerFinalWorkTraceOccurrence
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73QueryBatchPrefixCausalController
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

def beforeQueryBatchChallengeEvents : List MachineEvent :=
  [.check .frontierCount, .absorb .queryBatchDomain]

def afterQueryBatchChallengeEvents (messages : Messages) : List MachineEvent :=
  [.check .twoTreeAuthentication,
   .absorb (.queryBatchClaim messages.queryBatchClaim)] ++
    relationTailEvents messages ++ [.check .relationTerminal]

theorem after_accepted_query_scan_query_batch_split (messages : Messages) :
    afterAcceptedQueryScan messages =
      beforeQueryBatchChallengeEvents ++
        challengeEvent messages .queryBatch ::
          afterQueryBatchChallengeEvents messages := by
  simp [afterAcceptedQueryScan, beforeQueryBatchChallengeEvents,
    afterQueryBatchChallengeEvents]

/-- The exact accepted execution reaches the query-batch sampler at the digest
returned by the immediately preceding empty-domain absorption. -/
theorem exact_operational_query_batch_domain_produces_initial_digest
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
      tableLookup (exactOperationalTable input)
          (bytes beforeDomain.digest ++
            [domAbsorb, queryBatchChallengeLabel]) =
        some beforeQueryBatch.digest ∧
      isQueryBatchPrefixBoundaryInput
          (bytes beforeDomain.digest ++
            [domAbsorb, queryBatchChallengeLabel]) = true := by
  obtain ⟨evaluator⟩ :=
    exact_operational_input_constructs_complete_evaluator input
  have splitRun := evaluator.afterQ16Run
  rw [after_accepted_query_scan_query_batch_split] at splitRun
  obtain ⟨beforeQueryBatch, prefixRun, _restRun⟩ :=
    (run_machine_events_work_erased_append_iff
      (exactOperationalTable input) beforeQueryBatchChallengeEvents
      (challengeEvent (exactOperationalTape input).messages .queryBatch ::
        afterQueryBatchChallengeEvents
          (exactOperationalTape input).messages)
      evaluator.afterQ16 evaluator.finalState).mp splitRun
  obtain ⟨beforeDomain, _frontierRun, domainRun⟩ :=
    (run_machine_events_work_erased_append_iff
      (exactOperationalTable input) [.check .frontierCount]
      [.absorb .queryBatchDomain] evaluator.afterQ16 beforeQueryBatch).mp
        (by simpa [beforeQueryBatchChallengeEvents] using prefixRun)
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
  · simpa [AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using lookup
  · exact literal_query_batch_domain_is_prefix_boundary beforeDomain.digest

/-- One evaluator witness supplies both the domain producer and the complete
consumed query-batch duplex chain.  The chain is root ordered and therefore
remains valid when a coordinate was first queried by the adversary. -/
theorem exact_operational_query_batch_domain_and_chain
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
        (outputs advances : List Digest256),
      tableLookup (exactOperationalTable input) producerInput =
          some initialDigest ∧
      (∃ beforeDomain : EvalState,
        producerInput = bytes beforeDomain.digest ++
          [domAbsorb, queryBatchChallengeLabel]) ∧
      ExactRootOrderedQ16Chain input producerInput initialDigest outputs
        advances ∧
      outputs.length =
        ((exactOperationalTape input).messages.challengeUse
          .queryBatch).blocksUsed ∧
      advances.length = outputs.length := by
  obtain ⟨evaluator⟩ :=
    exact_operational_input_constructs_complete_evaluator input
  have splitRun := evaluator.afterQ16Run
  rw [after_accepted_query_scan_query_batch_split] at splitRun
  obtain ⟨beforeQueryBatch, prefixRun, restRun⟩ :=
    (run_machine_events_work_erased_append_iff
      (exactOperationalTable input) beforeQueryBatchChallengeEvents
      (challengeEvent (exactOperationalTape input).messages .queryBatch ::
        afterQueryBatchChallengeEvents
          (exactOperationalTape input).messages)
      evaluator.afterQ16 evaluator.finalState).mp splitRun
  obtain ⟨beforeDomain, _frontierRun, domainRun⟩ :=
    (run_machine_events_work_erased_append_iff
      (exactOperationalTable input) [.check .frontierCount]
      [.absorb .queryBatchDomain] evaluator.afterQ16 beforeQueryBatch).mp
        (by simpa [beforeQueryBatchChallengeEvents] using prefixRun)
  simp only [runMachineEventsWorkErased] at domainRun
  obtain ⟨afterDomain, absorbRun, domainDone⟩ :=
    Option.bind_eq_some_iff.mp domainRun
  have afterDomainExact : afterDomain = beforeQueryBatch := by
    simpa [runMachineEventsWorkErased] using Option.some.inj domainDone
  subst afterDomain
  let producerInput : ShaInput :=
    bytes beforeDomain.digest ++ [domAbsorb, queryBatchChallengeLabel]
  have producerLookup : tableLookup (exactOperationalTable input)
      producerInput = some beforeQueryBatch.digest := by
    have lookup := absorb_step_exposes_literal_lookup
      (exactOperationalTable input) beforeDomain beforeQueryBatch
        .queryBatchDomain absorbRun
    simpa [producerInput,
      AspisK1.V7Tag73TranscriptSchedule.Payload.label,
      AspisK1.V7Tag73TranscriptSchedule.Payload.data] using lookup
  simp only [runMachineEventsWorkErased] at restRun
  obtain ⟨afterQueryBatch, queryBatchRun, _tailRun⟩ :=
    Option.bind_eq_some_iff.mp restRun
  have queryBatchRun' : runMachineEventWorkErased
      (exactOperationalTable input) beforeQueryBatch
      (.challenge .queryBatch
        ((exactOperationalTape input).messages.challengeUse .queryBatch)) =
        some afterQueryBatch := by
    simpa [challengeEvent] using queryBatchRun
  obtain ⟨outputs, afterBlocks, squeezeRun, _afterExact, outputsLength,
      _recordMember⟩ := challenge_event_work_erased_exposes_record
    (exactOperationalTable input) beforeQueryBatch afterQueryBatch .queryBatch
      ((exactOperationalTape input).messages.challengeUse .queryBatch)
      queryBatchRun'
  obtain ⟨advances, advancesLength, coordinates, _callsExact⟩ :=
    squeeze_many_coordinates (exactOperationalTable input)
      (.challenge .queryBatch)
      ((exactOperationalTape input).messages.challengeUse
        .queryBatch).blocksUsed beforeQueryBatch afterBlocks outputs squeezeRun
  have ordered : ExactRootOrderedQ16Chain input producerInput
      beforeQueryBatch.digest outputs advances :=
    gamma_table_coordinate_chain_has_exact_root_order transitionRoom input
      producerInput beforeQueryBatch.digest producerLookup coordinates
  exact ⟨producerInput, beforeQueryBatch.digest, outputs, advances,
    producerLookup, ⟨beforeDomain, rfl⟩, ordered, outputsLength,
    advancesLength⟩

#print axioms after_accepted_query_scan_query_batch_split
#print axioms exact_operational_query_batch_domain_produces_initial_digest
#print axioms exact_operational_query_batch_domain_and_chain

end
end AspisK1.V7Tag73ExactQueryBatchPrefixBoundaryOrigin
