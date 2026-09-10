import AspisFormal.K1.V7Tag73GammaRestoredK14Scope
import AspisFormal.K1.V7Tag73RootQueryBatchForkBridge

/-!
# Provenance scope for the restoration-native K1.3 query-batch challenge

The degree-sixteen K1.3 batching argument must range over the challenge of
the child created by the typed root query-batch restoration.  It must not
identify that fresh child challenge with the already fixed challenge of the
accepted root.  This module gives the child the same request and execution
provenance already used by the restoration-native K1.4 gamma argument.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73QueryBatchRestoredK13Scope

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ActualNodeCausalProvenance
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ConcreteRootSweepClient
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalNodeExecution
open AspisK1.V7Tag73ExactFixedOperationalNodeProgramming
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73PreparedRestorationRoles
open AspisK1.V7Tag73ProjectedNodeForkCursor
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73RootQueryBatchForkBridge
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- One concrete request selects block zero of the accepted root verifier's
query-batch squeeze before either programmed answer is exposed. -/
structure ExactRootQueryBatchRestorationRequest
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (request : ConcreteRestorationRequest) : Type where
  rootNode : request.nodeId = 0
  transition : FutureFreeTransition
  reply : VerifierReply
  transitionExact : verifierTransitionAt?
      input.package.root.fixedRoot.base.runtime.node
      request.verifierTransitionIndex = some transition
  transitionWithin : request.verifierTransitionIndex < 1513
  eventExact : transition.event =
    .verifier (.squeezePair (.challenge .queryBatch) 0) reply

/-- A root transition index is the literal block-zero query-batch squeeze. -/
def IsRootQueryBatchTransitionIndex
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (index : Nat) : Prop :=
  ∃ transition reply,
    verifierTransitionAt? input.package.root.fixedRoot.base.runtime.node index =
        some transition ∧
      index < 1513 ∧
      transition.event =
        .verifier (.squeezePair (.challenge .queryBatch) 0) reply

theorem exact_operational_input_has_root_query_batch_transition_index
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ∃ index, IsRootQueryBatchTransitionIndex input index := by
  obtain ⟨index, transition, reply, transitionExact, within, eventExact⟩ :=
    exact_clean_root_has_indexed_query_batch_transition
      input.package.root.fixedRoot.base
  exact ⟨index, transition, reply, transitionExact, within, eventExact⟩

/-- Canonical least typed request used by the restored K1.3 source. -/
noncomputable def exactOperationalRootQueryBatchRestorationRequest
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : ConcreteRestorationRequest := by
  classical
  exact
    { nodeId := 0
      verifierTransitionIndex := Nat.find
        (exact_operational_input_has_root_query_batch_transition_index input) }

/-- The canonical request retains its exact typed root provenance. -/
noncomputable def
    exact_operational_root_query_batch_restoration_request_is_typed
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    ExactRootQueryBatchRestorationRequest input
      (exactOperationalRootQueryBatchRestorationRequest input) := by
  classical
  let found := Nat.find_spec
    (exact_operational_input_has_root_query_batch_transition_index input)
  let transition := Classical.choose found
  let transitionFacts := Classical.choose_spec found
  let reply := Classical.choose transitionFacts
  have facts := Classical.choose_spec transitionFacts
  exact
    { rootNode := rfl
      transition := transition
      reply := reply
      transitionExact := facts.1
      transitionWithin := facts.2.1
      eventExact := facts.2.2 }

/-- A restoration-wide K1.3 certificate whose node was actually inserted by
the canonical root query-batch request. -/
structure ExactQueryBatchRestoredOperationalK13Certificate
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (decoder : ExactDecoderInstantiation QM31Exact)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) : Type where
  request : ConcreteRestorationRequest
  requestIsQueryBatch : ExactRootQueryBatchRestorationRequest input request
  requestCanonical :
    request = exactOperationalRootQueryBatchRestorationRequest input
  certificate : ExactRestoredOperationalK13Certificate decoder input
  parentRequestExact : certificate.node.parentRequest = some request

/-- The scoped query-batch certificate is necessarily a nonroot child. -/
theorem query_batch_restored_certificate_is_not_root
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (k13 : ExactQueryBatchRestoredOperationalK13Certificate decoder input) :
    k13.certificate.node ≠
      input.package.root.fixedRoot.base.runtime.node := by
  intro nodeExact
  have rootParent :
      input.package.root.fixedRoot.base.runtime.node.parentRequest = none := rfl
  have childParent := k13.parentRequestExact
  rw [nodeExact, rootParent] at childParent
  cases childParent

/-- Every scoped child is one of the literal nodes inserted by the completed
production restoration client, with the same retained parent request. -/
theorem query_batch_restored_certificate_has_exact_projected_execution
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (positive : 0 < transitionFuel)
    (k13 : ExactQueryBatchRestoredOperationalK13Certificate decoder input) :
    Nonempty { execution : ProjectedRestorationNodeExecution
        (Final := ConcreteRestorationClientRun Statement Tag73K12ParsedProof
          Payload (ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
            Payload Witness))
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)
        configuration.machine.environment configuration.restorationConfiguration
        (runExactPlainRom transitionFuel configuration sample).trace
        (exactRestorationAccumulator input) k13.certificate.node //
      execution.prepared.request = k13.request } := by
  have nonroot : k13.certificate.node.parentRequest ≠ none := by
    rw [k13.parentRequestExact]
    exact Option.some_ne_none k13.request
  obtain ⟨execution⟩ := exact_operational_nonroot_node_has_projected_execution
    positive input k13.certificate.node k13.certificate.member nonroot
  have requestExact : execution.prepared.request = k13.request := by
    apply Option.some.inj
    exact execution.parentRequestExact.symm.trans k13.parentRequestExact
  exact ⟨⟨execution, requestExact⟩⟩

/-- The projected child's executable preparer selects the exact canonical
root transition named by its typed query-batch request. -/
theorem query_batch_restored_certificate_execution_has_exact_transition
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (positive : 0 < transitionFuel)
    (k13 : ExactQueryBatchRestoredOperationalK13Certificate decoder input) :
    Nonempty { execution : ProjectedRestorationNodeExecution
        (Final := ConcreteRestorationClientRun Statement Tag73K12ParsedProof
          Payload (ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
            Payload Witness))
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)
        configuration.machine.environment configuration.restorationConfiguration
        (runExactPlainRom transitionFuel configuration sample).trace
        (exactRestorationAccumulator input) k13.certificate.node //
      execution.prepared.request = k13.request ∧
        execution.prepared.transition = k13.requestIsQueryBatch.transition ∧
        execution.prepared.parentNode =
          input.package.root.fixedRoot.base.runtime.node } := by
  obtain ⟨⟨execution, requestExact⟩⟩ :=
    query_batch_restored_certificate_has_exact_projected_execution positive k13
  have selected := ready_preparation_parent_is_stored
    (configuration.machine.blackBox.start sample.1
      configuration.machine.observation)
    configuration.restorationConfiguration (exactRestorationAccumulator input)
    execution.prepared.request execution.prepared execution.preparationExact
  have rootLookup := input.package.root.full.projection.nodeStoreInvariant.1
  change (exactRestorationAccumulator input).node? 0 =
    some input.package.root.fixedRoot.base.runtime.node at rootLookup
  have parentExact : execution.prepared.parentNode =
      input.package.root.fixedRoot.base.runtime.node := by
    apply Option.some.inj
    calc
      some execution.prepared.parentNode =
          (exactRestorationAccumulator input).node?
            execution.prepared.request.nodeId := selected.1.symm
      _ = (exactRestorationAccumulator input).node? k13.request.nodeId := by
        rw [requestExact]
      _ = (exactRestorationAccumulator input).node? 0 := by
        rw [k13.requestIsQueryBatch.rootNode]
      _ = some input.package.root.fixedRoot.base.runtime.node := rootLookup
  have selectedTransition := selected.2.2.2
  rw [requestExact, parentExact] at selectedTransition
  have transitionExact : execution.prepared.transition =
      k13.requestIsQueryBatch.transition := by
    apply Option.some.inj
    exact selectedTransition.symm.trans
      k13.requestIsQueryBatch.transitionExact
  exact ⟨⟨execution, requestExact, transitionExact, parentExact⟩⟩

/-- The child pair is typed as block-zero query-batch before either scheduled
answer is inspected. -/
theorem query_batch_restored_certificate_has_block_zero_query_batch_pair
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (positive : 0 < transitionFuel)
    (k13 : ExactQueryBatchRestoredOperationalK13Certificate decoder input) :
    ∃ (execution : ProjectedRestorationNodeExecution
        (Final := ConcreteRestorationClientRun Statement Tag73K12ParsedProof
          Payload (ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
            Payload Witness))
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)
        configuration.machine.environment configuration.restorationConfiguration
        (runExactPlainRom transitionFuel configuration sample).trace
        (exactRestorationAccumulator input) k13.certificate.node)
      (role : PreparedRestorationPairRole),
      execution.prepared.request = k13.request ∧
      execution.prepared.transition = k13.requestIsQueryBatch.transition ∧
      preparedRestorationPairRole? execution.prepared = some role ∧
      role.owner = .challenge .queryBatch ∧
      role.block = 0 ∧
      execution.scheduled.outputInput = role.outputInput ∧
      execution.scheduled.advanceInput = role.advanceInput := by
  obtain ⟨⟨execution, requestExact, transitionExact, _parentExact⟩⟩ :=
    query_batch_restored_certificate_execution_has_exact_transition positive k13
  obtain ⟨role, roleExact, outputExact, advanceExact, _outputGrammar,
      _advanceGrammar⟩ :=
    projected_restoration_node_has_exact_fork_role execution
  have eventExact : execution.prepared.transition.event =
      .verifier (.squeezePair (.challenge .queryBatch) 0)
        k13.requestIsQueryBatch.reply := by
    rw [transitionExact]
    exact k13.requestIsQueryBatch.eventExact
  have ownerExact : role.owner = .challenge .queryBatch := by
    unfold preparedRestorationPairRole? at roleExact
    rw [eventExact] at roleExact
    cases roleExact
    rfl
  have blockExact : role.block = 0 := by
    unfold preparedRestorationPairRole? at roleExact
    rw [eventExact] at roleExact
    cases roleExact
    rfl
  exact ⟨execution, role, requestExact, transitionExact, roleExact,
    ownerExact, blockExact, outputExact, advanceExact⟩

/-- The child's retained trace reaches its own scheduled query-batch output
in the literal production cursor.  This is the correct pre-answer coordinate;
no equality with the accepted root's old query-batch value is asserted. -/
theorem
    query_batch_restored_certificate_trace_prefix_reaches_scheduled_output
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample}
    (positive : 0 < transitionFuel)
    (k13 : ExactQueryBatchRestoredOperationalK13Certificate decoder input) :
    ∃ (execution : ProjectedRestorationNodeExecution
          (Final := ConcreteRestorationClientRun Statement Tag73K12ParsedProof
            Payload (ExactPlainRomWitnessExtractor Statement
              Tag73K12ParsedProof Payload Witness))
          (configuration.machine.blackBox.start sample.1
            configuration.machine.observation)
          configuration.machine.environment
          configuration.restorationConfiguration
          (runExactPlainRom transitionFuel configuration sample).trace
          (exactRestorationAccumulator input) k13.certificate.node)
        (role : PreparedRestorationPairRole)
        (pairRoom : execution.scheduled.frozenHistory.length + 2 ≤
          globalFull256OracleCallCap parameters)
        (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
          SchedulerNativeCursor (globalFull256OracleCallCap parameters)
            (SchedulerNativePlainRomResult TapeIdentity Statement
              Tag73K12ParsedProof Payload
              (ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
                Payload Witness))),
      execution.prepared.request = k13.request ∧
      execution.prepared.transition = k13.requestIsQueryBatch.transition ∧
      preparedRestorationPairRole? execution.prepared = some role ∧
      role.owner = .challenge .queryBatch ∧
      role.block = 0 ∧
      seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (exactPlainRomCursor configuration sample.1)
            (execution.traceBeforePair.map UnifiedExposureRecord.answer)) =
        .forkOutput execution.scheduled.frozenHistory pairRoom
          execution.scheduled.outputInput execution.scheduled.advanceInput
          execution.scheduled.template next := by
  obtain ⟨execution, role, requestExact, transitionExact, roleExact,
      ownerExact, blockExact, _outputExact, _advanceExact⟩ :=
    query_batch_restored_certificate_has_block_zero_query_batch_pair positive k13
  have runExact :
      runSchedulerNativeListRun transitionFuel
          (exactPlainRomCursor configuration sample.1)
          (freshAnswerTapeToList sample.2) =
        runExactPlainRom transitionFuel configuration sample := by
    simpa [runExactPlainRom] using
      (run_scheduler_native_eq_list_run transitionFuel
        (exactCompilerTargetCaps parameters).length
        (exactPlainRomCursor configuration sample.1) sample.2).symm
  have traceExact :
      (runSchedulerNativeListRun transitionFuel
          (exactPlainRomCursor configuration sample.1)
          (freshAnswerTapeToList sample.2)).trace =
        execution.traceBeforePair ++
          scheduledPairRecords execution.scheduled ++
          (execution.proverRecords ++ execution.verifierRecords ++
            execution.traceAfterVerifier) := by
    rw [runExact]
    simpa [List.append_assoc] using execution.fullTraceExact
  obtain ⟨pairRoom, next, cursorExact⟩ :=
    seek_after_trace_prefix_is_scheduled_fork_output transitionFuel
      (exactPlainRomCursor configuration sample.1)
      (freshAnswerTapeToList sample.2) execution.traceBeforePair
      (execution.proverRecords ++ execution.verifierRecords ++
        execution.traceAfterVerifier) execution.scheduled traceExact
  exact ⟨execution, role, pairRoom, next, requestExact, transitionExact,
    roleExact, ownerExact, blockExact, cursorExact⟩

/-- In the production one-round root sweep, the canonical query-batch request
can insert at most one child. -/
theorem one_round_query_batch_restored_certificates_have_same_node
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {extractor : ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
      Payload Witness}
    {withinForkCap : 1 * 1513 ≤ parameters.forkRequestCap}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    {decoder : ExactDecoderInstantiation QM31Exact}
    {input : ExactK12OperationalInput transitionFuel
      (exactRootSweepWitnessConfiguration base 1 extractor withinForkCap)
      projection fixedInstance sample}
    (_positive : 0 < transitionFuel)
    (left right : ExactQueryBatchRestoredOperationalK13Certificate decoder
      input) :
    left.certificate.node = right.certificate.node := by
  have nodup :
      (storedParentRequests (exactRestorationAccumulator input)).Nodup := by
    apply returned_one_round_root_sweep_stored_parent_requests_nodup
      transitionFuel
      (exactFixedClientContinuationFuel transitionFuel input.package.root)
      base sample.1 input.package.root.fixedRoot.base.runtime
      extractor input.package.root.full.projection.rootPrefixes.verifier.remaining
      input.package.root.full.clientRun
    simpa only [exactRootSweepWitnessConfiguration, Nat.one_mul] using
      input.package.factorization.computedClientListTerminalExact
  apply node_eq_of_same_stored_parent_request nodup
  · exact left.certificate.member
  · exact right.certificate.member
  · rw [left.parentRequestExact, left.requestCanonical]
  · rw [right.parentRequestExact, right.requestCanonical]

#print axioms ExactRootQueryBatchRestorationRequest
#print axioms exact_operational_input_has_root_query_batch_transition_index
#print axioms exactOperationalRootQueryBatchRestorationRequest
#print axioms
  exact_operational_root_query_batch_restoration_request_is_typed
#print axioms ExactQueryBatchRestoredOperationalK13Certificate
#print axioms query_batch_restored_certificate_is_not_root
#print axioms query_batch_restored_certificate_has_exact_projected_execution
#print axioms
  query_batch_restored_certificate_execution_has_exact_transition
#print axioms
  query_batch_restored_certificate_has_block_zero_query_batch_pair
#print axioms
  query_batch_restored_certificate_trace_prefix_reaches_scheduled_output
#print axioms
  one_round_query_batch_restored_certificates_have_same_node

end
end AspisK1.V7Tag73QueryBatchRestoredK13Scope
