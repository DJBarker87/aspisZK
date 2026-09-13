import AspisFormal.K1.V7Tag73QueryBatchRestoredK13Scope

/-!
# Query-batch restoration provenance without a successful K1.3 certificate

The old scope is indexed by `ExactQueryBatchRestoredOperationalK13Certificate`.
That is a useful success interface, but cannot itself describe the child on
which a failed classifier is being analysed. This module removes ONLY that
success requirement. Every request, stored-node membership, source trace and
programmed pair remains the actual one.

There is deliberately no theorem asserting that the canonical request inserts
an accepting child. No selector below is claimed to be pre-answer measurable.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace AspisK1.V7Tag73StoredQueryBatchChild

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ActualNodeCausalProvenance
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ConcreteRootSweepClient
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedOperationalNodeExecution
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRestoredOperationalK13Classifier
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73PreparedRestorationRoles
open AspisK1.V7Tag73ProjectedNodeForkCursor
open AspisK1.V7Tag73QueryBatchRestoredK13Scope
open AspisK1.V7Tag73RestoredDerivedK13View
open AspisK1.V7Tag73RestoredNodeK13Classifier
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativePrefixTraversal
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisV5ComponentCQM31TowerExact

noncomputable section

variable {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
  {parameters : ExactCompilerResourceParameters}
  {transitionFuel : Nat}
  {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
    Observation Statement Tag73K12ParsedProof Payload Witness parameters}
  {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
  {fixedInstance : PublicInstance Statement}
  {sample : ExactCompilerSample HiddenTape parameters}

/-- Stored child of the canonical root query-batch request. It need not be
`.done`, and need not have a K1.3 success certificate. -/
structure StoredQueryBatchChild
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) where
  node : RestoredK13Node Statement Payload
  member : node ∈ (exactRestorationAccumulator input).nodes
  parentRequestExact : node.parentRequest =
    some (exactOperationalRootQueryBatchRestorationRequest input)

variable {input : ExactK12OperationalInput transitionFuel configuration
  projection fixedInstance sample}

/-- Existing successful scoped certificates embed into the larger interface. -/
def StoredQueryBatchChild.ofCertificate
    {decoder : ExactDecoderInstantiation QM31Exact}
    (success : ExactQueryBatchRestoredOperationalK13Certificate decoder input) :
    StoredQueryBatchChild input where
  node := success.certificate.node
  member := success.certificate.member
  parentRequestExact := by
    rw [success.parentRequestExact, success.requestCanonical]

/-- A rejected/failed child is still not the root. -/
theorem StoredQueryBatchChild.ne_root (child : StoredQueryBatchChild input) :
    child.node ≠ input.package.root.fixedRoot.base.runtime.node := by
  intro same
  have parent := child.parentRequestExact
  rw [same] at parent
  have rootParent :
      input.package.root.fixedRoot.base.runtime.node.parentRequest = none := rfl
  rw [rootParent] at parent
  cases parent

/-- No success premise is needed for the literal source execution. -/
theorem StoredQueryBatchChild.has_projected_execution
    (positive : 0 < transitionFuel) (child : StoredQueryBatchChild input) :
    Nonempty { execution : ProjectedRestorationNodeExecution
        (Final := ConcreteRestorationClientRun Statement Tag73K12ParsedProof
          Payload (ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
            Payload Witness))
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)
        configuration.machine.environment configuration.restorationConfiguration
        (runExactPlainRom transitionFuel configuration sample).trace
        (exactRestorationAccumulator input) child.node //
      execution.prepared.request =
        exactOperationalRootQueryBatchRestorationRequest input } := by
  have nonroot : child.node.parentRequest ≠ none := by
    rw [child.parentRequestExact]
    exact Option.some_ne_none _
  obtain ⟨execution⟩ := exact_operational_nonroot_node_has_projected_execution
    positive input child.node child.member nonroot
  have requestExact : execution.prepared.request =
      exactOperationalRootQueryBatchRestorationRequest input := by
    apply Option.some.inj
    exact execution.parentRequestExact.symm.trans child.parentRequestExact
  exact ⟨⟨execution, requestExact⟩⟩

/-- Recover the actual parent and transition from the stored request. -/
theorem StoredQueryBatchChild.has_exact_transition
    (positive : 0 < transitionFuel) (child : StoredQueryBatchChild input) :
    Nonempty { execution : ProjectedRestorationNodeExecution
        (Final := ConcreteRestorationClientRun Statement Tag73K12ParsedProof
          Payload (ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
            Payload Witness))
        (configuration.machine.blackBox.start sample.1
          configuration.machine.observation)
        configuration.machine.environment configuration.restorationConfiguration
        (runExactPlainRom transitionFuel configuration sample).trace
        (exactRestorationAccumulator input) child.node //
      execution.prepared.request =
          exactOperationalRootQueryBatchRestorationRequest input ∧
      execution.prepared.transition =
          (exact_operational_root_query_batch_restoration_request_is_typed input).transition ∧
      execution.prepared.parentNode =
          input.package.root.fixedRoot.base.runtime.node } := by
  obtain ⟨⟨execution, requestExact⟩⟩ := child.has_projected_execution positive
  let typed := exact_operational_root_query_batch_restoration_request_is_typed input
  have selected := ready_preparation_parent_is_stored
    (configuration.machine.blackBox.start sample.1 configuration.machine.observation)
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
      _ = (exactRestorationAccumulator input).node?
          (exactOperationalRootQueryBatchRestorationRequest input).nodeId := by
        rw [requestExact]
      _ = (exactRestorationAccumulator input).node? 0 := by rw [typed.rootNode]
      _ = some input.package.root.fixedRoot.base.runtime.node := rootLookup
  have selectedTransition := selected.2.2.2
  rw [requestExact, parentExact] at selectedTransition
  have transitionExact : execution.prepared.transition = typed.transition := by
    apply Option.some.inj
    exact selectedTransition.symm.trans typed.transitionExact
  exact ⟨⟨execution, requestExact, transitionExact, parentExact⟩⟩

/-- The programmed pair remains the child's block-zero query-batch pair,
including on a subsequently rejecting execution. -/
theorem StoredQueryBatchChild.has_query_batch_pair
    (positive : 0 < transitionFuel) (child : StoredQueryBatchChild input) :
    ∃ (execution : ProjectedRestorationNodeExecution
        (Final := ConcreteRestorationClientRun Statement Tag73K12ParsedProof
          Payload (ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
            Payload Witness))
        (configuration.machine.blackBox.start sample.1 configuration.machine.observation)
        configuration.machine.environment configuration.restorationConfiguration
        (runExactPlainRom transitionFuel configuration sample).trace
        (exactRestorationAccumulator input) child.node)
      (role : PreparedRestorationPairRole),
      execution.prepared.request =
        exactOperationalRootQueryBatchRestorationRequest input ∧
      preparedRestorationPairRole? execution.prepared = some role ∧
      role.owner = .challenge .queryBatch ∧ role.block = 0 ∧
      execution.scheduled.outputInput = role.outputInput ∧
      execution.scheduled.advanceInput = role.advanceInput := by
  obtain ⟨⟨execution, requestExact, transitionExact, _parentExact⟩⟩ :=
    child.has_exact_transition positive
  obtain ⟨role, roleExact, outputExact, advanceExact, _og, _ag⟩ :=
    projected_restoration_node_has_exact_fork_role execution
  let typed := exact_operational_root_query_batch_restoration_request_is_typed input
  have eventExact : execution.prepared.transition.event =
      .verifier (.squeezePair (.challenge .queryBatch) 0) typed.reply := by
    rw [transitionExact]
    exact typed.eventExact
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
  exact ⟨execution, role, requestExact, roleExact, ownerExact, blockExact,
    outputExact, advanceExact⟩

/-- Reachability of the scheduled pre-answer cut, without a successful
classifier certificate or equality to the root's old challenge. -/
theorem StoredQueryBatchChild.reaches_scheduled_output
    (positive : 0 < transitionFuel) (child : StoredQueryBatchChild input) :
    ∃ (execution : ProjectedRestorationNodeExecution
          (Final := ConcreteRestorationClientRun Statement Tag73K12ParsedProof
            Payload (ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
              Payload Witness))
          (configuration.machine.blackBox.start sample.1 configuration.machine.observation)
          configuration.machine.environment configuration.restorationConfiguration
          (runExactPlainRom transitionFuel configuration sample).trace
          (exactRestorationAccumulator input) child.node)
        (role : PreparedRestorationPairRole)
        (pairRoom : execution.scheduled.frozenHistory.length + 2 ≤
          globalFull256OracleCallCap parameters)
        (next : AspisK1.V7Tag73AtomicPairReplay.AtomicPairReplayConfiguration →
          SchedulerNativeCursor (globalFull256OracleCallCap parameters)
            (SchedulerNativePlainRomResult TapeIdentity Statement Tag73K12ParsedProof
              Payload (ExactPlainRomWitnessExtractor Statement Tag73K12ParsedProof
                Payload Witness))),
      execution.prepared.request = exactOperationalRootQueryBatchRestorationRequest input ∧
      preparedRestorationPairRole? execution.prepared = some role ∧
      role.owner = .challenge .queryBatch ∧ role.block = 0 ∧
      seekSchedulerNativeExposure transitionFuel
          (schedulerNativePrefixCursor transitionFuel
            (exactPlainRomCursor configuration sample.1)
            (execution.traceBeforePair.map UnifiedExposureRecord.answer)) =
        .forkOutput execution.scheduled.frozenHistory pairRoom
          execution.scheduled.outputInput execution.scheduled.advanceInput
          execution.scheduled.template next := by
  obtain ⟨execution, role, requestExact, roleExact, ownerExact, blockExact,
      _outputExact, _advanceExact⟩ := child.has_query_batch_pair positive
  have runExact : runSchedulerNativeListRun transitionFuel
        (exactPlainRomCursor configuration sample.1) (freshAnswerTapeToList sample.2) =
      runExactPlainRom transitionFuel configuration sample := by
    simpa [runExactPlainRom] using
      (run_scheduler_native_eq_list_run transitionFuel
        (exactCompilerTargetCaps parameters).length
        (exactPlainRomCursor configuration sample.1) sample.2).symm
  have traceExact : (runSchedulerNativeListRun transitionFuel
        (exactPlainRomCursor configuration sample.1) (freshAnswerTapeToList sample.2)).trace =
      execution.traceBeforePair ++ scheduledPairRecords execution.scheduled ++
        (execution.proverRecords ++ execution.verifierRecords ++ execution.traceAfterVerifier) := by
    rw [runExact]
    simpa [List.append_assoc] using execution.fullTraceExact
  obtain ⟨pairRoom, next, cursorExact⟩ := seek_after_trace_prefix_is_scheduled_fork_output
    transitionFuel (exactPlainRomCursor configuration sample.1)
    (freshAnswerTapeToList sample.2) execution.traceBeforePair
    (execution.proverRecords ++ execution.verifierRecords ++ execution.traceAfterVerifier)
    execution.scheduled traceExact
  exact ⟨execution, role, pairRoom, next, requestExact, roleExact, ownerExact,
    blockExact, cursorExact⟩

/-- Bridge back to the existing success interface only when success is
actually available. This is not used to reason about failed children. -/
def StoredQueryBatchChild.toCertificate
    {decoder : ExactDecoderInstantiation QM31Exact}
    (child : StoredQueryBatchChild input)
    (done : child.node.verifierFinalState.current.control = .done)
    (data : RestoredOperationalK13Data configuration.machine.environment child.node)
    (classified : RestoredOperationalK13Certificate decoder child.node data) :
    ExactQueryBatchRestoredOperationalK13Certificate decoder input where
  request := exactOperationalRootQueryBatchRestorationRequest input
  requestIsQueryBatch := exact_operational_root_query_batch_restoration_request_is_typed input
  requestCanonical := rfl
  certificate := { node := child.node, member := child.member, done := done,
                   data := data, classified := classified }
  parentRequestExact := child.parentRequestExact

/-- Two retained children for one request are equal when the actual store has
unique parent requests. The one-round root-sweep theorem supplies this premise;
it must not be assumed for an arbitrary many-round store. -/
theorem StoredQueryBatchChild.node_eq_of_requests_nodup
    (nodup : (storedParentRequests (exactRestorationAccumulator input)).Nodup)
    (left right : StoredQueryBatchChild input) : left.node = right.node := by
  apply node_eq_of_same_stored_parent_request nodup
  · exact left.member
  · exact right.member
  · exact left.parentRequestExact
  · exact right.parentRequestExact

#print axioms StoredQueryBatchChild.ne_root
#print axioms StoredQueryBatchChild.has_projected_execution
#print axioms StoredQueryBatchChild.has_exact_transition
#print axioms StoredQueryBatchChild.has_query_batch_pair
#print axioms StoredQueryBatchChild.reaches_scheduled_output
#print axioms StoredQueryBatchChild.toCertificate
#print axioms StoredQueryBatchChild.node_eq_of_requests_nodup

end
end AspisK1.V7Tag73StoredQueryBatchChild
