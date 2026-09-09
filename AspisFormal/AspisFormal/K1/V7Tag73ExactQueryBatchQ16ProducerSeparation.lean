import AspisFormal.K1.V7Tag73ExactGammaQ16ProducerSeparation
import AspisFormal.K1.V7Tag73ExactQueryBatchPrefixBoundaryOrigin

/-!
# Query-batch chain separation from q16 producers

The query-batch sampler begins at the digest returned by the literal
34-byte empty-domain absorption.  A q16 candidate producer has a 35-byte
source input and a recursive q16 producer has a 33-byte advance source.
Clean-root answer uniqueness therefore keeps every state of the subsequently
consumed query-batch duplex disjoint from the completed q16 producer
inventory, even when the adversary exposed a coordinate first.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactQueryBatchQ16ProducerSeparation

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalDagProducerInvariant
open AspisK1.V7Tag73ExactAlphaQ16ProducerSeparation
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagProducerRecordProvenance
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactGammaQ16ProducerSeparation
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactQueryBatchPrefixBoundaryOrigin
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- The empty query-batch-domain absorption cannot be the source coordinate
of a q16 producer: the three source grammars have lengths 34, 35, and 33. -/
theorem query_batch_boundary_avoids_q16_producer_sources
    (beforeDomainDigest base : Digest256)
    (producers : List Q16DagProducer)
    (inventory : Q16DagProducerInventoryValid base producers) :
    ∀ producer ∈ producers,
      bytes beforeDomainDigest ++ [domAbsorb, queryBatchChallengeLabel] ≠
        producer.sourceInput := by
  intro producer producerMember equal
  rcases inventory producer producerMember with candidate | advanced
  · rw [candidate.2] at equal
    have lengths := congrArg List.length equal
    simp at lengths
  · obtain ⟨parent, _parentMember, _counterExact, _blockExact,
      sourceExact⟩ := advanced
    rw [sourceExact] at equal
    have lengths := congrArg List.length equal
    simp at lengths

/-- The complete consumed query-batch state chain avoids every q16 producer
reconstructed from the same accepted production root. -/
theorem exact_operational_query_batch_chain_avoids_full_dag_producers
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
    (trial : ExactCompilerExposureTrial parameters) :
    ∃ (producerInput : ShaInput) (initialDigest : Digest256)
        (outputs advances : List Digest256),
      ExactRootOrderedQ16Chain input producerInput initialDigest outputs
          advances ∧
      outputs.length =
          ((exactOperationalTape input).messages.challengeUse
            .queryBatch).blocksUsed ∧
      advances.length = outputs.length ∧
      ChainStatesAvoidQ16Producers
        (indexedStateAfterRecords transitionFuel
          (exactDagTrialController transitionFuel trial)
          (exactFixedRootRecords input.package.root)
          (exactDagCandidateInitialState input)).memory.producers
        initialDigest advances := by
  obtain ⟨producerInput, initialDigest, outputs, advances, producerLookup,
      ⟨beforeDomain, producerInputExact⟩, chain, outputsLength,
      advancesLength⟩ :=
    exact_operational_query_batch_domain_and_chain transitionRoom input
  let reached := indexedStateAfterRecords transitionFuel
    (exactDagTrialController transitionFuel trial)
    (exactFixedRootRecords input.package.root)
    (exactDagCandidateInitialState input)
  have invariant : Q16DagMemoryProducerInvariant reached.memory := by
    simpa [reached] using exact_dag_candidate_root_producer_invariant input trial
  have avoids : ChainStatesAvoidQ16Producers reached.memory.producers
      initialDigest advances := by
    cases baseExact : reached.memory.q16Base with
    | none =>
        have empty := invariant.noBaseHasNoProducers baseExact
        simp [empty, ChainStatesAvoidQ16Producers]
    | some base =>
        have inventory : Q16DagProducerInventoryValid base
            reached.memory.producers :=
          invariant.inventoryValid base baseExact
        have provenance : ∀ producer ∈ reached.memory.producers,
            ∃ actor,
              (.machineFresh actor producer.sourceInput producer.digest :
                  UnifiedExposureRecord) ∈
                exactFixedRootRecords input.package.root := by
          intro producer producerMember
          apply exact_dag_prefix_producer_has_literal_record input trial
            (exactFixedRootRecords input.package.root) [] (by simp) producer
          simpa [reached] using producerMember
        apply exact_root_ordered_chain_avoids_q16_producers input base
          reached.memory.producers inventory provenance chain
        intro producer producerMember
        rw [producerInputExact]
        apply query_batch_boundary_avoids_q16_producer_sources
          beforeDomain.digest base reached.memory.producers inventory producer
            producerMember
  exact ⟨producerInput, initialDigest, outputs, advances, chain, outputsLength,
    advancesLength, by simpa [reached] using avoids⟩

/-- Every query-batch output and advance consumed by production is residual
for the q16 DAG at its literal pre-answer root state. -/
theorem exact_operational_query_batch_consumed_coordinates_are_not_q16
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
    (trial : ExactCompilerExposureTrial parameters) :
    ∃ (producerInput : ShaInput) (initialDigest : Digest256)
        (outputs advances : List Digest256),
      ExactRootOrderedQ16Chain input producerInput initialDigest outputs
          advances ∧
      outputs.length =
          ((exactOperationalTape input).messages.challengeUse
            .queryBatch).blocksUsed ∧
      advances.length = outputs.length ∧
      (∀ state ∈ initialDigest :: advances,
        ∀ output actor prior later,
          exactFixedRootRecords input.package.root =
              prior ++
                (.machineFresh actor (gammaOutputInput state) output :
                  UnifiedExposureRecord) :: later →
          (exactDagTrialController transitionFuel trial).preferredSlot
            (indexedStateAfterRecords transitionFuel
              (exactDagTrialController transitionFuel trial) prior
              (exactDagCandidateInitialState input)) = none) ∧
      (∀ state advanced actor prior later,
        exactFixedRootRecords input.package.root =
            prior ++
              (.machineFresh actor (gammaAdvanceInput state) advanced :
                UnifiedExposureRecord) :: later →
        (exactDagTrialController transitionFuel trial).preferredSlot
          (indexedStateAfterRecords transitionFuel
            (exactDagTrialController transitionFuel trial) prior
            (exactDagCandidateInitialState input)) = none) := by
  obtain ⟨producerInput, initialDigest, outputs, advances, chain,
      outputsLength, advancesLength, avoids⟩ :=
    exact_operational_query_batch_chain_avoids_full_dag_producers
      transitionRoom input trial
  refine ⟨producerInput, initialDigest, outputs, advances, chain,
    outputsLength, advancesLength, ?_, ?_⟩
  · intro state stateMember output actor prior later decomposition
    apply exact_gamma_state_output_is_dag_residual_of_completed_avoid input trial
      state
    · intro producer producerMember
      exact avoids state stateMember producer producerMember
    · exact decomposition
  · intro state advanced actor prior later decomposition
    exact exact_alpha_advance_is_residual_at_literal_root_prefix input trial
      state advanced actor prior later decomposition

#print axioms query_batch_boundary_avoids_q16_producer_sources
#print axioms exact_operational_query_batch_chain_avoids_full_dag_producers
#print axioms exact_operational_query_batch_consumed_coordinates_are_not_q16

end
end AspisK1.V7Tag73ExactQueryBatchQ16ProducerSeparation
