import AspisFormal.K1.V7Tag73ExactCandidateQueryBatchChainRouting
import AspisFormal.K1.V7Tag73ExactAlphaZeroControllerAlignment
import AspisFormal.K1.V7Tag73ExactAlphaQ16ProducerSeparation
import AspisFormal.K1.V7Tag73ExactAlphaQ16InventoryDisjoint
import AspisFormal.K1.V7Tag73ExactQueryBatchQ16ProducerSeparation
import AspisFormal.K1.V7Tag73AlphaFinalWorkQ16ControllerProjection
import AspisFormal.K1.V7Tag73ExactAlphaFinalWorkQ16RootRouting
import AspisFormal.K1.V7Tag73FoldOuterSourceSeparation
import AspisFormal.K1.V7Tag73FoldAlphaFinalWorkQ16ControllerProjection
import AspisFormal.K1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting

/-!
# Query-batch / alpha producer separation

Query-batch and alpha squeeze inputs intentionally have the same 33-byte
grammar.  They therefore cannot be separated by a raw-input classifier.  This
module instead proves the causal fact needed by the complete candidate router:
the deployed query-batch state chain avoids every alpha producer reconstructed
from the same accepted root.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactQueryBatchAlphaProducerSeparation

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AlphaZeroCausalController
open AspisK1.V7Tag73AlphaZeroProducerInvariant
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73AlphaFinalWorkQ16ControllerProjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73CausalGammaPrefixCoordinates
open AspisK1.V7Tag73CausalDagFinalWorkQ16Controller
open AspisK1.V7Tag73CausalDagProducerInvariant
open AspisK1.V7Tag73ExactAlphaQ16ProducerSeparation
open AspisK1.V7Tag73ExactAlphaQ16InventoryDisjoint
open AspisK1.V7Tag73ExactAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactAlphaZeroControllerAlignment
open AspisK1.V7Tag73ExactCandidateQueryBatchChainRouting
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldAlphaFinalWorkQ16RootRouting
open AspisK1.V7Tag73ExactGammaQ16ProducerSeparation
open AspisK1.V7Tag73ExactDagCandidateLabeledRootRouting
open AspisK1.V7Tag73ExactDagProducerRecordProvenance
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactQ16CausalCoordinateOrder
open AspisK1.V7Tag73ExactQueryBatchQ16ProducerSeparation
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerComposition
open AspisK1.V7Tag73FoldAlphaFinalWorkQ16ControllerProjection
open AspisK1.V7Tag73FoldOuterSourceSeparation
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73IndexedControllerTraceAlignment
open AspisK1.V7Tag73IndexedExposureCausalRouter
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerNativeGammaReplay
open AspisK1.V7Tag73SchedulerCausalQ16Router
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Every live logical block-zero alpha producer has the exact deployed
43-byte fold-nonce source grammar. -/
def AlphaBlockZeroSourcesHaveLength43
    (producers : List AlphaZeroProducer) : Prop :=
  ∀ producer ∈ producers, producer.block.val = 0 →
    producer.sourceInput.length = 43

theorem update_alpha_zero_preserves_block_zero_source_length
    (producers : List AlphaZeroProducer) (input : ShaInput)
    (answer : Digest256)
    (valid : AlphaBlockZeroSourcesHaveLength43 producers) :
    AlphaBlockZeroSourcesHaveLength43
      (updateAlphaZeroProducers producers input answer) := by
  cases advanced : alphaZeroAdvancedSlot? producers input with
  | none =>
      simpa [updateAlphaZeroProducers, advanced] using valid
  | some block =>
      obtain ⟨parent, parentMember, _inputExact, blockExact⟩ :=
        alpha_zero_advanced_slot_cases producers input block advanced
      intro producer member blockZero
      simp only [updateAlphaZeroProducers, advanced, List.mem_append,
        List.mem_singleton] at member
      rcases member with old | added
      · exact valid producer old blockZero
      · subst producer
        simp only at blockZero
        omega

theorem alpha_zero_after_memory_preserves_block_zero_source_length
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat)
    (state : IndexedUnifiedExposureState globalOracleCalls
      AlphaZeroControllerMemory)
    (answer : Digest256)
    (valid : AlphaBlockZeroSourcesHaveLength43 state.memory.producers) :
    AlphaBlockZeroSourcesHaveLength43
      (alphaZeroAfterMemory transitionFuel boundaryIndex state answer).producers := by
  unfold alphaZeroAfterMemory
  cases inputExact : unifiedInputBeforeAnswer? transitionFuel state.cursor with
  | none => simpa [inputExact] using valid
  | some input =>
      simp only
      split
      next boundary =>
        intro producer member blockZero
        simp only [List.mem_singleton] at member
        subst producer
        have recognized : isAlphaZeroBoundaryInput input = true := by
          by_contra notRecognized
          have falseExact : isAlphaZeroBoundaryInput input = false :=
            Bool.eq_false_of_not_eq_true notRecognized
          simp [falseExact] at boundary
        simp only [isAlphaZeroBoundaryInput, Bool.and_eq_true] at recognized
        simpa using (of_decide_eq_true recognized.1.1)
      next _ =>
        exact update_alpha_zero_preserves_block_zero_source_length
          state.memory.producers input answer valid

theorem alpha_zero_records_preserve_block_zero_source_length
    {globalOracleCalls : Nat}
    (transitionFuel boundaryIndex : Nat) :
    ∀ (records : List UnifiedExposureRecord)
      (state : IndexedUnifiedExposureState globalOracleCalls
        AlphaZeroControllerMemory),
      AlphaBlockZeroSourcesHaveLength43 state.memory.producers →
      AlphaBlockZeroSourcesHaveLength43
        (indexedStateAfterRecords transitionFuel
          (alphaZeroCausalController transitionFuel boundaryIndex)
          records state).memory.producers := by
  intro records
  induction records with
  | nil => intro state valid; simpa
  | cons record rest ih =>
      intro state valid
      rw [indexed_state_after_records_cons]
      apply ih
      exact alpha_zero_after_memory_preserves_block_zero_source_length
        transitionFuel boundaryIndex state record.answer valid

/-- The state digests consumed by a duplex chain avoid an alpha inventory. -/
def ChainStatesAvoidAlphaProducers
    (producers : List AlphaZeroProducer)
    (initial : Digest256) (advances : List Digest256) : Prop :=
  ∀ state ∈ initial :: advances,
    ∀ producer ∈ producers, state ≠ producer.digest

/-- Once a chain's initial state avoids the alpha inventory, ordered root
answers and the two recursive advance grammars preserve that separation. -/
theorem exact_root_ordered_chain_avoids_alpha_producers_of_initial
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
    (producers : List AlphaZeroProducer)
    (inventory : AlphaZeroProducerInventoryValid producers)
    (zeroSources : AlphaBlockZeroSourcesHaveLength43 producers)
    (provenance : ∀ producer ∈ producers,
      ∃ actor,
        (.machineFresh actor producer.sourceInput producer.digest :
          UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root)
    {producerInput : ShaInput} {digest : Digest256}
    {outputs advances : List Digest256}
    (chain : ExactRootOrderedQ16Chain input producerInput digest outputs
      advances)
    (initialAvoid : ∀ producer ∈ producers, digest ≠ producer.digest) :
    ChainStatesAvoidAlphaProducers producers digest advances := by
  induction chain with
  | done producerInput digest producerFound =>
      intro state stateMember producer producerMember
      have stateExact : state = digest := by simpa using stateMember
      subst state
      exact initialAvoid producer producerMember
  | @next producerInput digest output advanced outputs advances producerFound
      outputFound advanceFound producerBeforeOutput producerBeforeAdvance tail ih =>
      have nextAvoid : ∀ producer ∈ producers,
          advanced ≠ producer.digest := by
        intro producer producerMember answersEqual
        obtain ⟨actor, producerRecord⟩ := provenance producer producerMember
        have sourceExact := clean_root_answer_eq_fixes_source_input input
          (gammaAdvanceInput digest) producer.sourceInput advanced
          producer.digest advanceFound actor producerRecord answersEqual
        rcases inventory producer producerMember with zero | advancedSource
        · have producerLength := zeroSources producer producerMember zero
          have equalLength := congrArg List.length sourceExact
          simp [gammaAdvanceInput] at equalLength
          omega
        · obtain ⟨parent, _parentMember, _blockExact, sourceInputExact⟩ :=
            advancedSource
          rw [sourceInputExact] at sourceExact
          exact initialAvoid parent _parentMember
            (advance_input_eq_implies_state_eq digest parent.digest sourceExact)
      have tailAvoid := ih nextAvoid
      intro state stateMember producer producerMember
      simp only [List.mem_cons] at stateMember
      rcases stateMember with current | later
      · simpa [current] using initialAvoid producer producerMember
      · exact tailAvoid state (by simpa using later) producer producerMember

/-- A query-batch chain whose 34-byte boundary is in the exact root cannot
meet any alpha chain rooted at a 43-byte fold-nonce boundary. -/
theorem exact_root_ordered_query_batch_chain_avoids_alpha_producers
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
    (producers : List AlphaZeroProducer)
    (inventory : AlphaZeroProducerInventoryValid producers)
    (zeroSources : AlphaBlockZeroSourcesHaveLength43 producers)
    (provenance : ∀ producer ∈ producers,
      ∃ actor,
        (.machineFresh actor producer.sourceInput producer.digest :
          UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root)
    {producerInput : ShaInput} {digest : Digest256}
    {outputs advances : List Digest256}
    (chain : ExactRootOrderedQ16Chain input producerInput digest outputs
      advances)
    (boundaryLength : producerInput.length = 34) :
    ChainStatesAvoidAlphaProducers producers digest advances := by
  apply exact_root_ordered_chain_avoids_alpha_producers_of_initial input
    producers inventory zeroSources provenance chain
  intro producer producerMember answersEqual
  obtain ⟨actor, producerRecord⟩ := provenance producer producerMember
  have sourceExact := clean_root_answer_eq_fixes_source_input input
    producerInput producer.sourceInput digest producer.digest
      (exact_root_ordered_q16_chain_producer_lookup chain)
      actor producerRecord answersEqual
  rcases inventory producer producerMember with zero | advanced
  · have producerLength := zeroSources producer producerMember zero
    have equalLength := congrArg List.length sourceExact
    omega
  · obtain ⟨parent, _parentMember, _blockExact, sourceInputExact⟩ := advanced
    rw [sourceInputExact] at sourceExact
    have equalLength := congrArg List.length sourceExact
    simp at equalLength
    omega

/-- Every state feeding an actually consumed duplex output is either the
boundary digest or one of the preceding advance answers. -/
theorem gamma_chain_state_mem_initial_cons_advances
    (initial : Digest256) : ∀ (advances : List Digest256) (index : Nat),
    index < advances.length →
    gammaChainState initial advances index ∈ initial :: advances := by
  intro advances
  induction advances generalizing initial with
  | nil => intro index impossible; simp at impossible
  | cons head tail ih =>
      intro index inBounds
      cases index with
      | zero => simp [gammaChainState]
      | succ index =>
          have tailBound : index < tail.length := by simpa using inBounds
          have member := ih head index tailBound
          simp only [gammaChainState]
          exact List.mem_cons_of_mem initial member

/-- At a literal query-batch output record, the standalone alpha controller
is residual.  This is causal separation, not raw-input classification. -/
theorem exact_query_batch_state_output_is_alpha_residual
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
    (boundaryIndex : Nat)
    {producerInput : ShaInput} {initialDigest : Digest256}
    {outputs advances : List Digest256}
    (chain : ExactRootOrderedQ16Chain input producerInput initialDigest outputs
      advances)
    (boundaryLength : producerInput.length = 34)
    (state : Digest256)
    (stateMember : state ∈ initialDigest :: advances)
    (output : Digest256) (actor : QueryActor)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root = prior ++
      (.machineFresh actor (gammaOutputInput state) output :
        UnifiedExposureRecord) :: later) :
    (alphaZeroCausalController transitionFuel boundaryIndex).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex) prior
        (exactAlphaZeroInitialState input)) = none := by
  let controller := alphaZeroCausalController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel boundaryIndex
  let initial := exactAlphaZeroInitialState input
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  have invariant : AlphaZeroMemoryProducerInvariant reached.memory := by
    apply exact_alpha_zero_prefix_producer_invariant input boundaryIndex prior
      ((.machineFresh actor (gammaOutputInput state) output :
        UnifiedExposureRecord) :: later)
    simpa [controller, initial] using decomposition
  have zeroSources :
      AlphaBlockZeroSourcesHaveLength43 reached.memory.producers := by
    apply alpha_zero_records_preserve_block_zero_source_length transitionFuel
      boundaryIndex prior initial
    simp [initial, exactAlphaZeroInitialState,
      inactiveAlphaZeroMemory, AlphaBlockZeroSourcesHaveLength43]
  have provenance : ∀ producer ∈ reached.memory.producers,
      ∃ sourceActor,
        (.machineFresh sourceActor producer.sourceInput producer.digest :
          UnifiedExposureRecord) ∈ exactFixedRootRecords input.package.root := by
    intro producer producerMember
    obtain ⟨sourceActor, sourceMember⟩ :=
      exact_alpha_prefix_producer_has_literal_record input boundaryIndex prior
        ((.machineFresh actor (gammaOutputInput state) output :
          UnifiedExposureRecord) :: later) (by
            simpa [controller, initial] using decomposition) producer (by
            simpa [reached, controller, initial] using producerMember)
    exact ⟨sourceActor, by
      rw [decomposition]
      exact List.mem_append_left _ sourceMember⟩
  have avoids := exact_root_ordered_query_batch_chain_avoids_alpha_producers
    input reached.memory.producers invariant.inventoryValid zeroSources
      provenance chain boundaryLength
  have stateAvoid : ∀ producer ∈ reached.memory.producers,
      state ≠ producer.digest := avoids state stateMember
  have aligned : unifiedRecordAtAnswer transitionFuel reached.cursor output =
      .machineFresh actor (gammaOutputInput state) output := by
    have rootAligned := exact_root_records_aligned_for_alpha_zero_controller
      input boundaryIndex prior
        (.machineFresh actor (gammaOutputInput state) output) later decomposition
    simpa [reached, controller, initial,
      UnifiedExposureRecord.answer] using rootAligned
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some (gammaOutputInput state) :=
    aligned_machine_record_has_exact_input transitionFuel reached.cursor actor
      (gammaOutputInput state) output aligned
  change alphaZeroPreferredSlot transitionFuel reached = none
  cases preferred : alphaZeroPreferredSlot transitionFuel reached with
  | none => rfl
  | some slot =>
      obtain ⟨selectedInput, producer, selectedExact, producerMember,
          outputExact, _slotExact⟩ :=
        alpha_zero_preferred_slot_has_producer transitionFuel reached slot
          preferred
      exfalso
      apply stateAvoid producer producerMember
      apply output_input_eq_implies_state_eq state producer.digest
      have inputsEqual : gammaOutputInput state = selectedInput :=
        Option.some.inj (inputExact.symm.trans selectedExact)
      simpa [gammaOutputInput] using inputsEqual.trans outputExact

/-- An advance input can never be an alpha output coordinate, independently
of producer state. -/
theorem exact_query_batch_state_advance_is_alpha_residual
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
    (boundaryIndex : Nat) (state advanced : Digest256) (actor : QueryActor)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root = prior ++
      (.machineFresh actor (gammaAdvanceInput state) advanced :
        UnifiedExposureRecord) :: later) :
    (alphaZeroCausalController transitionFuel boundaryIndex).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (alphaZeroCausalController transitionFuel boundaryIndex) prior
        (exactAlphaZeroInitialState input)) = none := by
  let controller := alphaZeroCausalController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel boundaryIndex
  let initial := exactAlphaZeroInitialState input
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  have aligned : unifiedRecordAtAnswer transitionFuel reached.cursor advanced =
      .machineFresh actor (gammaAdvanceInput state) advanced := by
    have rootAligned := exact_root_records_aligned_for_alpha_zero_controller
      input boundaryIndex prior
        (.machineFresh actor (gammaAdvanceInput state) advanced) later
          decomposition
    simpa [reached, controller, initial,
      UnifiedExposureRecord.answer] using rootAligned
  have inputExact : unifiedInputBeforeAnswer? transitionFuel reached.cursor =
      some (gammaAdvanceInput state) :=
    aligned_machine_record_has_exact_input transitionFuel reached.cursor actor
      (gammaAdvanceInput state) advanced aligned
  change alphaZeroPreferredSlot transitionFuel reached = none
  cases preferred : alphaZeroPreferredSlot transitionFuel reached with
  | none => rfl
  | some slot =>
      obtain ⟨selectedInput, producer, selectedExact, _producerMember,
          outputExact, _slotExact⟩ :=
        alpha_zero_preferred_slot_has_producer transitionFuel reached slot
          preferred
      exfalso
      apply advance_input_ne_output_input state producer.digest
      have inputsEqual : gammaAdvanceInput state = selectedInput :=
        Option.some.inj (inputExact.symm.trans selectedExact)
      simpa [gammaAdvanceInput] using inputsEqual.trans outputExact

/-- The same exact query-batch chain avoids the completed final-work/q16 DAG
for any fixed exposure trial. -/
theorem exact_query_batch_chain_avoids_completed_dag_producers
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
    (trial : ExactCompilerExposureTrial parameters)
    (beforeDomainDigest initialDigest : Digest256)
    {outputs advances : List Digest256}
    (chain : ExactRootOrderedQ16Chain input
      (bytes beforeDomainDigest ++ [domAbsorb, queryBatchChallengeLabel])
      initialDigest outputs advances) :
    ChainStatesAvoidQ16Producers
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial)
        (exactFixedRootRecords input.package.root)
        (exactDagCandidateInitialState input)).memory.producers
      initialDigest advances := by
  let reached := indexedStateAfterRecords transitionFuel
    (exactDagTrialController transitionFuel trial)
    (exactFixedRootRecords input.package.root)
    (exactDagCandidateInitialState input)
  have invariant : Q16DagMemoryProducerInvariant reached.memory := by
    simpa [reached] using exact_dag_candidate_root_producer_invariant input trial
  cases baseExact : reached.memory.q16Base with
  | none =>
      have empty := invariant.noBaseHasNoProducers baseExact
      simp [reached, empty, ChainStatesAvoidQ16Producers]
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
      exact query_batch_boundary_avoids_q16_producer_sources
        beforeDomainDigest base reached.memory.producers inventory producer
          producerMember

/-- Literal query-batch output coordinates are residual for the fixed
final-work/q16 trial controller. -/
theorem exact_query_batch_state_output_is_dag_residual
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
    (trial : ExactCompilerExposureTrial parameters)
    (beforeDomainDigest initialDigest : Digest256)
    {outputs advances : List Digest256}
    (chain : ExactRootOrderedQ16Chain input
      (bytes beforeDomainDigest ++ [domAbsorb, queryBatchChallengeLabel])
      initialDigest outputs advances)
    (state : Digest256) (stateMember : state ∈ initialDigest :: advances)
    (output : Digest256) (actor : QueryActor)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root = prior ++
      (.machineFresh actor (gammaOutputInput state) output :
        UnifiedExposureRecord) :: later) :
    (exactDagTrialController transitionFuel trial).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) prior
        (exactDagCandidateInitialState input)) = none := by
  have completedAvoid :=
    exact_query_batch_chain_avoids_completed_dag_producers input trial
      beforeDomainDigest initialDigest chain
  apply exact_gamma_state_output_is_dag_residual_of_completed_avoid input trial
    state _ output actor prior later decomposition
  intro producer producerMember
  exact completedAvoid state stateMember producer producerMember

/-- Literal query-batch advance coordinates are also residual for the fixed
final-work/q16 trial controller. -/
theorem exact_query_batch_state_advance_is_dag_residual
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
    (trial : ExactCompilerExposureTrial parameters)
    (state advanced : Digest256) (actor : QueryActor)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root = prior ++
      (.machineFresh actor (gammaAdvanceInput state) advanced :
        UnifiedExposureRecord) :: later) :
    (exactDagTrialController transitionFuel trial).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (exactDagTrialController transitionFuel trial) prior
        (exactDagCandidateInitialState input)) = none := by
  exact exact_alpha_advance_is_residual_at_literal_root_prefix input trial
    state advanced actor prior later decomposition

/-- The complete 517-slot alpha/final-work/q16 product is residual at a
query-batch output. -/
theorem exact_query_batch_state_output_is_517_residual
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
    (trial : ExactCompilerExposureTrial parameters) (boundaryIndex : Nat)
    (beforeDomainDigest initialDigest : Digest256)
    {outputs advances : List Digest256}
    (chain : ExactRootOrderedQ16Chain input
      (bytes beforeDomainDigest ++ [domAbsorb, queryBatchChallengeLabel])
      initialDigest outputs advances)
    (state : Digest256) (stateMember : state ∈ initialDigest :: advances)
    (output : Digest256) (actor : QueryActor)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root = prior ++
      (.machineFresh actor (gammaOutputInput state) output :
        UnifiedExposureRecord) :: later) :
    (alphaFinalWorkQ16DagController transitionFuel trial.val
      (alphaZeroCausalController transitionFuel boundaryIndex)).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (alphaFinalWorkQ16DagController transitionFuel trial.val
          (alphaZeroCausalController transitionFuel boundaryIndex)) prior
        (exactAlphaFinalWorkQ16InitialState input)) = none := by
  let alphaController := alphaZeroCausalController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel boundaryIndex
  let controller := alphaFinalWorkQ16DagController transitionFuel trial.val
    alphaController
  let reached := indexedStateAfterRecords transitionFuel controller prior
    (exactAlphaFinalWorkQ16InitialState input)
  have alphaNone := exact_query_batch_state_output_is_alpha_residual input
    boundaryIndex chain (by simp) state stateMember output actor prior later
      decomposition
  have alphaProjected : alphaController.preferredSlot
      (alphaIndexedState reached) = none := by
    rw [alpha_indexed_state_after_composed_records]
    simpa [alphaController] using alphaNone
  have dagNone := exact_query_batch_state_output_is_dag_residual input trial
    beforeDomainDigest initialDigest chain state stateMember output actor prior
      later decomposition
  have dagProjected :
      (finalWorkQ16DagController
        (globalFull256OracleCallCap parameters) transitionFuel trial.val
        ).preferredSlot (finalWorkQ16IndexedState reached) = none := by
    rw [final_work_q16_indexed_state_after_composed_records]
    simpa [exactDagTrialController, exactDagCandidateInitialState,
      alphaController] using dagNone
  change controller.preferredSlot reached = none
  simp [controller, alphaFinalWorkQ16DagController, alphaProjected,
    dagProjected]

/-- The complete 517-slot product is residual at a query-batch advance. -/
theorem exact_query_batch_state_advance_is_517_residual
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
    (trial : ExactCompilerExposureTrial parameters) (boundaryIndex : Nat)
    (state advanced : Digest256) (actor : QueryActor)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root = prior ++
      (.machineFresh actor (gammaAdvanceInput state) advanced :
        UnifiedExposureRecord) :: later) :
    (alphaFinalWorkQ16DagController transitionFuel trial.val
      (alphaZeroCausalController transitionFuel boundaryIndex)).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (alphaFinalWorkQ16DagController transitionFuel trial.val
          (alphaZeroCausalController transitionFuel boundaryIndex)) prior
        (exactAlphaFinalWorkQ16InitialState input)) = none := by
  let alphaController := alphaZeroCausalController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel boundaryIndex
  let controller := alphaFinalWorkQ16DagController transitionFuel trial.val
    alphaController
  let reached := indexedStateAfterRecords transitionFuel controller prior
    (exactAlphaFinalWorkQ16InitialState input)
  have alphaNone := exact_query_batch_state_advance_is_alpha_residual input
    boundaryIndex state advanced actor prior later decomposition
  have alphaProjected : alphaController.preferredSlot
      (alphaIndexedState reached) = none := by
    rw [alpha_indexed_state_after_composed_records]
    simpa [alphaController] using alphaNone
  have dagNone := exact_query_batch_state_advance_is_dag_residual input trial
    state advanced actor prior later decomposition
  have dagProjected :
      (finalWorkQ16DagController
        (globalFull256OracleCallCap parameters) transitionFuel trial.val
        ).preferredSlot (finalWorkQ16IndexedState reached) = none := by
    rw [final_work_q16_indexed_state_after_composed_records]
    simpa [exactDagTrialController, exactDagCandidateInitialState,
      alphaController] using dagNone
  change controller.preferredSlot reached = none
  simp [controller, alphaFinalWorkQ16DagController, alphaProjected,
    dagProjected]

/-- Any exact 33-byte root coordinate that is residual for the underlying
517-slot controller is residual for the complete 518-slot controller at the
accepted fold trial. -/
theorem exact_33_byte_517_residual_lifts_to_518
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
    (boundaryIndex : Nat)
    (foldDigest foldAnswer : Digest256) (foldActor : QueryActor)
    (foldPrior foldLater : List UnifiedExposureRecord)
    (foldExact : exactFixedRootRecords input.package.root = foldPrior ++
      (.machineFresh foldActor
        (bytes foldDigest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected)
        foldAnswer : UnifiedExposureRecord) :: foldLater)
    (trialExact : foldTrial.val = foldPrior.length)
    (queryInput : ShaInput) (answer : Digest256) (actor : QueryActor)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root = prior ++
      (.machineFresh actor queryInput answer : UnifiedExposureRecord) :: later)
    (inputLength : queryInput.length = 33)
    (underlyingNone :
      (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
        (alphaZeroCausalController transitionFuel boundaryIndex)).preferredSlot
        (indexedStateAfterRecords transitionFuel
          (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
            (alphaZeroCausalController transitionFuel boundaryIndex)) prior
          (exactAlphaFinalWorkQ16InitialState input)) = none) :
    (foldAlphaFinalWorkQ16Controller foldTrial.val
      (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
        (alphaZeroCausalController transitionFuel boundaryIndex))).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (foldAlphaFinalWorkQ16Controller foldTrial.val
          (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
            (alphaZeroCausalController transitionFuel boundaryIndex))) prior
        (exactFoldAlphaFinalWorkQ16InitialState input)) = none := by
  let underlying := alphaFinalWorkQ16DagController
    (globalOracleCalls := globalFull256OracleCallCap parameters)
    transitionFuel finalTrial.val
      (alphaZeroCausalController transitionFuel boundaryIndex)
  let controller := foldAlphaFinalWorkQ16Controller foldTrial.val underlying
  let initial := exactFoldAlphaFinalWorkQ16InitialState input
  let reached := indexedStateAfterRecords transitionFuel controller prior initial
  have distinct : prior.length ≠ foldTrial.val :=
    exact_33_byte_root_prefix_ne_fold_trial input foldTrial foldDigest foldAnswer
      foldActor foldPrior foldLater foldExact trialExact actor queryInput answer
      prior later decomposition inputLength
  have reachedIndex : reached.exposureIndex = prior.length := by
    rw [show reached.exposureIndex = initial.exposureIndex + prior.length by
      exact indexed_state_after_records_exposure_index transitionFuel
        controller prior initial]
    have initialZero : initial.exposureIndex = 0 := by rfl
    rw [initialZero, Nat.zero_add]
  have notFold : ¬(reached.memory.1 = false ∧
      reached.exposureIndex = foldTrial.val) := by
    intro selected
    exact distinct (reachedIndex.symm.trans selected.2)
  have projectedNone : underlying.preferredSlot
      (underlyingIndexedState reached) = none := by
    rw [underlying_indexed_state_after_fold_records]
    have initialProjection : underlyingIndexedState initial =
        exactAlphaFinalWorkQ16InitialState input := by rfl
    rw [initialProjection]
    exact underlyingNone
  change controller.preferredSlot reached = none
  simp [controller, foldAlphaFinalWorkQ16Controller, notFold, projectedNone]

/-- Complete 518-slot residual result for a query-batch output. -/
theorem exact_query_batch_state_output_is_518_residual
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
    (boundaryIndex : Nat)
    (foldDigest foldAnswer : Digest256) (foldActor : QueryActor)
    (foldPrior foldLater : List UnifiedExposureRecord)
    (foldExact : exactFixedRootRecords input.package.root = foldPrior ++
      (.machineFresh foldActor
        (bytes foldDigest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected)
        foldAnswer : UnifiedExposureRecord) :: foldLater)
    (trialExact : foldTrial.val = foldPrior.length)
    (beforeDomainDigest initialDigest : Digest256)
    {outputs advances : List Digest256}
    (chain : ExactRootOrderedQ16Chain input
      (bytes beforeDomainDigest ++ [domAbsorb, queryBatchChallengeLabel])
      initialDigest outputs advances)
    (state : Digest256) (stateMember : state ∈ initialDigest :: advances)
    (output : Digest256) (actor : QueryActor)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root = prior ++
      (.machineFresh actor (gammaOutputInput state) output :
        UnifiedExposureRecord) :: later) :
    (foldAlphaFinalWorkQ16Controller foldTrial.val
      (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
        (alphaZeroCausalController transitionFuel boundaryIndex))).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (foldAlphaFinalWorkQ16Controller foldTrial.val
          (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
            (alphaZeroCausalController transitionFuel boundaryIndex))) prior
        (exactFoldAlphaFinalWorkQ16InitialState input)) = none := by
  apply exact_33_byte_517_residual_lifts_to_518 input foldTrial finalTrial
    boundaryIndex foldDigest foldAnswer foldActor foldPrior foldLater foldExact
      trialExact (gammaOutputInput state) output actor prior later decomposition
      (by simp [gammaOutputInput])
  exact exact_query_batch_state_output_is_517_residual input finalTrial
    boundaryIndex beforeDomainDigest initialDigest chain state stateMember output
      actor prior later decomposition

/-- Complete 518-slot residual result for a query-batch advance. -/
theorem exact_query_batch_state_advance_is_518_residual
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
    (boundaryIndex : Nat)
    (foldDigest foldAnswer : Digest256) (foldActor : QueryActor)
    (foldPrior foldLater : List UnifiedExposureRecord)
    (foldExact : exactFixedRootRecords input.package.root = foldPrior ++
      (.machineFresh foldActor
        (bytes foldDigest ++ [domGrind] ++
          bytes (exactOperationalTape input).messages.foldGrinding.selected)
        foldAnswer : UnifiedExposureRecord) :: foldLater)
    (trialExact : foldTrial.val = foldPrior.length)
    (state advanced : Digest256) (actor : QueryActor)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root = prior ++
      (.machineFresh actor (gammaAdvanceInput state) advanced :
        UnifiedExposureRecord) :: later) :
    (foldAlphaFinalWorkQ16Controller foldTrial.val
      (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
        (alphaZeroCausalController transitionFuel boundaryIndex))).preferredSlot
      (indexedStateAfterRecords transitionFuel
        (foldAlphaFinalWorkQ16Controller foldTrial.val
          (alphaFinalWorkQ16DagController transitionFuel finalTrial.val
            (alphaZeroCausalController transitionFuel boundaryIndex))) prior
        (exactFoldAlphaFinalWorkQ16InitialState input)) = none := by
  apply exact_33_byte_517_residual_lifts_to_518 input foldTrial finalTrial
    boundaryIndex foldDigest foldAnswer foldActor foldPrior foldLater foldExact
      trialExact (gammaAdvanceInput state) advanced actor prior later
      decomposition (by simp [gammaAdvanceInput])
  exact exact_query_batch_state_advance_is_517_residual input finalTrial
    boundaryIndex state advanced actor prior later decomposition

#print axioms AlphaBlockZeroSourcesHaveLength43
#print axioms alpha_zero_records_preserve_block_zero_source_length
#print axioms exact_root_ordered_chain_avoids_alpha_producers_of_initial
#print axioms exact_root_ordered_query_batch_chain_avoids_alpha_producers
#print axioms gamma_chain_state_mem_initial_cons_advances
#print axioms exact_query_batch_state_output_is_alpha_residual
#print axioms exact_query_batch_state_advance_is_alpha_residual
#print axioms exact_query_batch_chain_avoids_completed_dag_producers
#print axioms exact_query_batch_state_output_is_dag_residual
#print axioms exact_query_batch_state_advance_is_dag_residual
#print axioms exact_query_batch_state_output_is_517_residual
#print axioms exact_query_batch_state_advance_is_517_residual
#print axioms exact_33_byte_517_residual_lifts_to_518
#print axioms exact_query_batch_state_output_is_518_residual
#print axioms exact_query_batch_state_advance_is_518_residual

end
end AspisK1.V7Tag73ExactQueryBatchAlphaProducerSeparation
