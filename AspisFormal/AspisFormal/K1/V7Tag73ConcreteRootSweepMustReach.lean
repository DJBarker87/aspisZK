import AspisFormal.K1.V7Tag73ActualNodeCausalProvenance
import AspisFormal.K1.V7Tag73RestoredQueryBatchCausalMarker
import AspisFormal.K1.V7Tag73RootQueryBatchForkBridge
import AspisFormal.K1.V7Tag73SchedulerNativeMustReach

/-!
# The concrete root sweep must reach its typed query-batch fork

This file supplies the temporal bridge missing from the static request-list
coverage theorem.  It follows the literal dispatcher continuation tree while
preserving node zero.  A later specialization will stop that tree at the
ready block-zero query-batch dispatcher, before either fork answer is read.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ConcreteRootSweepMustReach

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ActualNodeCausalProvenance
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ConcreteRootSweepClient
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RestoredQueryBatchCausalMarker
open AspisK1.V7Tag73RootQueryBatchForkBridge
open AspisK1.V7Tag73SchedulerNativeMustReach
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73TotalizedMachineReflection
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73UniformRawVerifierExecution

noncomputable section

universe u

/-- Charges and failure records never alter the node store. -/
theorem root_stored_after_charges_and_failure
    {Statement Proof Payload : Type u}
    (root : ConcreteRestorationNode Statement Proof Payload)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (charges : List ConcreteRestorationCharge)
    (request : ConcreteRestorationRequest)
    (reason : ConcreteRestorationFailure)
    (stored : RootStoredAtZero root accumulator) :
    RootStoredAtZero root
      ((accumulator.addCharges charges).addFailure request reason) := by
  simpa [RootStoredAtZero, ConcreteRestorationAccumulator.node?,
    ConcreteRestorationAccumulator.addCharges,
    ConcreteRestorationAccumulator.addFailure] using stored

/-- One literal request cannot prevent a target in every continuation from
being reached.  The proof also establishes internally that every accumulator
handed to a continuation still stores the immutable root at node zero. -/
theorem dispatch_one_preserves_rooted_must_reach
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (target : SchedulerNativeCursor globalOracleCalls
      (ConcreteRestorationClientRun Statement Proof Payload Result) → Prop)
    (root : ConcreteRestorationNode Statement Proof Payload)
    (startProgram : OracleMachine
      (CheckedRawTag73AdversaryReturnedValue Statement Proof Payload))
    (environment : FutureFreeEnvironment)
    (configuration : ConcreteRestorationConfiguration)
    (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
    (request : ConcreteRestorationRequest)
    (resume : ConcreteRestorationReply →
      ConcreteRestorationAccumulator Statement Proof Payload →
        SchedulerNativeCursor globalOracleCalls
          (ConcreteRestorationClientRun Statement Proof Payload Result))
    (rootStored : RootStoredAtZero root accumulator)
    (continuations : ∀ reply nextAccumulator,
      RootStoredAtZero root nextAccumulator →
        SchedulerNativeCursorMustReach target
          (resume reply nextAccumulator)) :
    SchedulerNativeCursorMustReach target
      (dispatchOneConcreteRestoration startProgram environment configuration
        accumulator request resume) := by
  have failureSafe : ∀
      (failureRequest : ConcreteRestorationRequest)
      (reason : ConcreteRestorationFailure)
      (nextAccumulator :
        ConcreteRestorationAccumulator Statement Proof Payload)
      (nextRoot : RootStoredAtZero root nextAccumulator),
      SchedulerNativeCursorMustReach target
        (resume (.failed reason)
          (nextAccumulator.addFailure failureRequest reason)) := by
    intro failureRequest reason nextAccumulator nextRoot
    apply continuations (.failed reason)
    simpa [RootStoredAtZero, ConcreteRestorationAccumulator.node?,
      ConcreteRestorationAccumulator.addFailure] using nextRoot
  generalize preparationExact :
    prepareConcreteRestorationFromStartProgram startProgram configuration
      accumulator request = preparation
  cases preparation with
  | failed reason prefixSteps prefixRestarts =>
      simp only [dispatchOneConcreteRestoration,
        dispatchConcreteRestoration, preparationExact]
      apply failureSafe request reason
      simpa [RootStoredAtZero, ConcreteRestorationAccumulator.node?,
        ConcreteRestorationAccumulator.addCharges] using rootStored
  | ready prepared =>
      let prefixRestarts := if prepared.prefixRun.isSome then 1 else 0
      let withPrefix := accumulator.addCharges
        [.prefixReplayQueries prepared.prefixSteps, .restart prefixRestarts]
      have withPrefixRoot : RootStoredAtZero root withPrefix := by
        simpa [withPrefix, RootStoredAtZero,
          ConcreteRestorationAccumulator.node?,
          ConcreteRestorationAccumulator.addCharges] using rootStored
      simp only [dispatchOneConcreteRestoration,
        dispatchConcreteRestoration, preparationExact]
      unfold dispatchPreparedRestoration
      by_cases prefixCoherent :
          HistoryTotalCoherent prepared.programmingBase
      next =>
        simp only [prefixCoherent, if_pos]
        by_cases globalLimit :
            configuration.oracleLimits.totalCalls ≤ globalOracleCalls
        next =>
          simp only [globalLimit, if_pos]
          by_cases pairRoom : prepared.programmingBase.history.length + 2 ≤
              globalOracleCalls
          next =>
            simp only [pairRoom, if_pos]
            apply SchedulerNativeCursorMustReach.forkPair
            intro scheduled frozenExact outputExact advanceExact templateExact
            let afterCoordinates := withPrefix.addCharges
              [.forkUniformCoordinates 2]
            have afterCoordinatesRoot : RootStoredAtZero root afterCoordinates := by
              simpa [afterCoordinates, RootStoredAtZero,
                ConcreteRestorationAccumulator.node?,
                ConcreteRestorationAccumulator.addCharges] using withPrefixRoot
            cases programmed : programConcretePair configuration.oracleLimits
                configuration.pairProgrammingOrder prepared.programmingBase
                prepared.outputInput prepared.advanceInput
                scheduled.configuration.forkOutput
                scheduled.configuration.forkAdvance with
            | failed reason inserted =>
                simp only [programmed]
                apply failureSafe prepared.request reason
                  (afterCoordinates.addCharges [.programmedPoints inserted])
                simpa [RootStoredAtZero, ConcreteRestorationAccumulator.node?,
                  ConcreteRestorationAccumulator.addCharges] using
                    afterCoordinatesRoot
            | ready afterBoth =>
                simp only [programmed]
                let afterProgramming := afterCoordinates.addCharges
                  [.programmedPoints 2]
                have afterProgrammingRoot : RootStoredAtZero root
                    afterProgramming := by
                  simpa [afterProgramming, RootStoredAtZero,
                    ConcreteRestorationAccumulator.node?,
                    ConcreteRestorationAccumulator.addCharges] using
                      afterCoordinatesRoot
                by_cases afterCoherent : HistoryTotalCoherent afterBoth
                next =>
                  simp only [afterCoherent, if_pos]
                  by_cases proverRoom : StageHasOracleRoom
                      configuration.oracleLimits afterBoth
                      configuration.proverReplayFuel
                  next =>
                    simp only [proverRoom, if_pos]
                    let atProverStart := afterProgramming.addCharges [.restart 1]
                    apply SchedulerNativeCursorMustReach.machine
                    intro proverStage proverFinalOracle proverFinalCoherent
                    cases proverStage with
                    | completed proverResult =>
                      simp only
                      let proverQueries :=
                        (historySince afterBoth proverFinalOracle).length
                      let afterProver := atProverStart.addCharges
                        [.completeFromStartQueries proverQueries]
                      have afterProverRoot : RootStoredAtZero root afterProver := by
                        simpa [afterProver, atProverStart, RootStoredAtZero,
                          ConcreteRestorationAccumulator.node?,
                          ConcreteRestorationAccumulator.addCharges] using
                            afterProgrammingRoot
                      cases proverResult with
                      | error failure =>
                          cases failure with
                          | oracleAbort reason =>
                              exact failureSafe prepared.request
                                (.proverReplayAbort reason) afterProver
                                  afterProverRoot
                          | timeout =>
                              exact failureSafe prepared.request
                                .proverReplayTimeout afterProver afterProverRoot
                      | ok adversaryValue =>
                          simp only
                          by_cases bindingMismatch :
                              V7Tag73InteractiveAncestor.FixedBindings.ofContext
                                  adversaryValue.rawMessages.context ≠
                                prepared.restoredState.current.bindings
                          next =>
                            rw [dif_pos bindingMismatch]
                            exact failureSafe prepared.request
                              .restoredBindingMismatch afterProver afterProverRoot
                          next =>
                            rw [dif_neg bindingMismatch]
                            by_cases verifierRoom : StageHasOracleRoom
                                configuration.oracleLimits proverFinalOracle
                                configuration.verifierFuel
                            next =>
                              simp only [verifierRoom, if_pos]
                              apply SchedulerNativeCursorMustReach.machine
                              intro verifierStage verifierFinalOracle
                                verifierFinalCoherent
                              cases verifierStage with
                              | completed verifierResult =>
                                simp only
                                let verifierQueries :=
                                  (historySince proverFinalOracle
                                    verifierFinalOracle).length
                                let afterVerifier := afterProver.addCharges
                                  [.verifierSuffixQueries verifierQueries]
                                have afterVerifierRoot : RootStoredAtZero root
                                    afterVerifier := by
                                  simpa [afterVerifier, RootStoredAtZero,
                                    ConcreteRestorationAccumulator.node?,
                                    ConcreteRestorationAccumulator.addCharges]
                                    using afterProverRoot
                                cases verifierResult with
                                | error failure =>
                                    cases failure with
                                    | oracleAbort reason =>
                                        exact failureSafe prepared.request
                                          (.verifierSuffixAbort reason)
                                            afterVerifier afterVerifierRoot
                                    | timeout =>
                                        exact failureSafe prepared.request
                                          .verifierSuffixTimeout afterVerifier
                                            afterVerifierRoot
                                | ok verifierFinalState =>
                                    let node : ConcreteRestorationNode Statement
                                        Proof Payload :=
                                      { parentRequest := some prepared.request
                                        adversaryValue := adversaryValue
                                        proverEntryOracle := afterBoth
                                        proverFinalOracle := proverFinalOracle
                                        verifierEntryOracle := proverFinalOracle
                                        verifierFinalOracle := verifierFinalOracle
                                        verifierEntryState :=
                                          prepared.restoredState
                                        verifierFinalState := verifierFinalState }
                                    let charged := afterVerifier.addCharges
                                      [.verifierTransitions
                                        verifierFinalState.transitions.length]
                                    apply continuations
                                      (.added (charged.addNode node).1)
                                      (charged.addNode node).2
                                    exact
                                      V7Tag73OperationalNodeCertificate.node_lookup_preserved_by_add_node
                                      charged node root 0 (by
                                        simpa [charged, RootStoredAtZero,
                                          ConcreteRestorationAccumulator.node?,
                                          ConcreteRestorationAccumulator.addCharges]
                                          using afterVerifierRoot)
                            next =>
                              rw [dif_neg verifierRoom]
                              exact failureSafe prepared.request
                                .verifierSuffixRoom afterProver afterProverRoot
                  next =>
                    simp only [proverRoom, if_neg]
                    exact failureSafe prepared.request .proverReplayRoom
                      afterProgramming afterProgrammingRoot
                next =>
                  simp only [afterCoherent, if_neg]
                  exact failureSafe prepared.request
                    .incoherentProgrammedOracle afterProgramming
                      afterProgrammingRoot
          next =>
            simp only [prefixCoherent, globalLimit, pairRoom]
            exact failureSafe prepared.request .pairExposureLimit withPrefix
              withPrefixRoot
        next =>
          rw [dif_neg globalLimit]
          exact failureSafe prepared.request .globalLimitTooSmall withPrefix
            withPrefixRoot
      next =>
        rw [dif_neg prefixCoherent]
        exact failureSafe prepared.request .incoherentPrefixOracle withPrefix
          withPrefixRoot

/-- If every adaptive request path of a finite client contains one selected
root transition, the literal fuel-bounded interpreter must reach the typed
block-zero query-batch fork for that transition.  Failed requests before the
target are allowed: the proof follows their real continuations and uses only
the immutable root slot. -/
theorem finite_client_path_target_must_reach_query_batch
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (runs : RootProjectedTotalizedRuns machine hidden runtime)
    (configuration : ConcreteRestorationConfiguration)
    (totalLimitMono : machine.adversaryLimits.totalCalls ≤
      configuration.oracleLimits.totalCalls)
    (freshLimitMono : machine.adversaryLimits.freshCalls ≤
      configuration.oracleLimits.freshCalls)
    (transitionIndex : Nat)
    (transition : FutureFreeTransition)
    (transitionExact : verifierTransitionAt? runtime.node transitionIndex =
      some transition)
    (reply : VerifierReply)
    (eventExact : transition.event =
      .verifier (.squeezePair (.challenge .queryBatch) 0) reply)
    (environment : FutureFreeEnvironment)
    (globalRoom : configuration.oracleLimits.totalCalls ≤ globalOracleCalls)
    (pairRoomAtTarget : ∀
      (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (prepared : PreparedConcreteRestoration Statement Proof Payload),
      RootStoredAtZero runtime.node accumulator →
      prepareConcreteRestorationFromStartProgram
          (machine.blackBox.start hidden machine.observation) configuration
          accumulator
          { nodeId := 0, verifierTransitionIndex := transitionIndex } =
        .ready prepared →
      prepared.programmingBase.history.length + 2 ≤ globalOracleCalls)
    (fuel count : Nat)
    (client : ConcreteRestorationClient Result)
    (result : Result)
    (exactCount : ExactRequestCount result count client)
    (fuelEnough : count ≤ fuel)
    (everyPath : ∀ requests,
      ConcreteRequestPath client requests →
        { nodeId := 0, verifierTransitionIndex := transitionIndex } ∈
          requests) :
    SchedulerNativeCursorMustReach
      (fun cursor =>
        typedRestoredQueryBatchForkStartsHere (Result := Result)
          (machine.blackBox.start hidden machine.observation) environment
          configuration cursor.erase = true)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls)
        (machine.blackBox.start hidden machine.observation) environment
        runtime.node configuration fuel client) := by
  let startProgram := machine.blackBox.start hidden machine.observation
  let targetRequest : ConcreteRestorationRequest :=
    { nodeId := 0, verifierTransitionIndex := transitionIndex }
  let target := fun cursor : SchedulerNativeCursor globalOracleCalls
      (ConcreteRestorationClientRun Statement Proof Payload Result) =>
    typedRestoredQueryBatchForkStartsHere (Result := Result) startProgram
      environment configuration cursor.erase = true
  let motive := fun (remainingFuel : Nat)
      (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (residualClient : ConcreteRestorationClient Result)
      (cursor : SchedulerNativeCursor globalOracleCalls
        (ConcreteRestorationClientRun Statement Proof Payload Result)) =>
    RootStoredAtZero runtime.node accumulator →
      ∀ residualResult residualCount,
        ExactRequestCount residualResult residualCount residualClient →
        residualCount ≤ remainingFuel →
        (∀ requests, ConcreteRequestPath residualClient requests →
          targetRequest ∈ requests) →
        SchedulerNativeCursorMustReach target cursor
  have induction :=
    start_concrete_restoration_client_from_root_dependent_induction
      (globalOracleCalls := globalOracleCalls) startProgram environment
      runtime.node configuration fuel client motive
      (by
        intro remainingFuel accumulator terminalResult rootStored
          residualResult residualCount residualExact residualEnough pathHit
        have impossible := pathHit [] (.pure terminalResult)
        simpa [targetRequest] using impossible)
      (by
        intro accumulator request next rootStored residualResult residualCount
          residualExact residualEnough pathHit
        cases residualExact with
        | restore certifiedRequest certifiedNext tails => omega)
      (by
        intro remainingFuel accumulator request next resume continuations
          rootStored residualResult residualCount residualExact residualEnough
          pathHit
        cases residualExact with
        | restore certifiedRequest certifiedNext tails =>
          by_cases selected : request = targetRequest
          · subst request
            obtain ⟨prepared, role, ready, coherent, transitionPrepared,
                roleExact, ownerExact, blockExact, _outputExact,
                _advanceExact, _header⟩ :=
              literal_root_query_batch_dispatch_emits_typed_fork machine hidden
                runtime runs configuration totalLimitMono freshLimitMono
                transitionIndex transition transitionExact 0 reply eventExact
                environment accumulator rootStored resume
            have requestExact :=
              V7Tag73ConcreteRestorationTraceInduction.ready_preparation_request_exact
                startProgram configuration accumulator targetRequest prepared
                (by simpa [startProgram, targetRequest] using ready)
            have readyAtPrepared :
                prepareConcreteRestorationFromStartProgram startProgram
                    configuration accumulator prepared.request =
                  .ready prepared := by
              rw [requestExact]
              simpa [startProgram, targetRequest] using ready
            apply SchedulerNativeCursorMustReach.here
            simpa [target, requestExact] using
              (typed_query_batch_dispatch_one_is_marked startProgram
                environment configuration accumulator prepared role resume
                  readyAtPrepared roleExact ownerExact blockExact coherent
                  globalRoom
                  (pairRoomAtTarget accumulator prepared rootStored ready))
          · apply dispatch_one_preserves_rooted_must_reach target runtime.node
              startProgram environment configuration accumulator request resume
              rootStored
            intro branchReply nextAccumulator nextRoot
            apply continuations branchReply nextAccumulator nextRoot
              residualResult _ (tails branchReply) (by omega)
            intro requests tailPath
            have fullPath : ConcreteRequestPath (.restore request next)
                (request :: requests) := .restore branchReply tailPath
            have member := pathHit (request :: requests) fullPath
            simp only [List.mem_cons] at member
            rcases member with atHead | inTail
            · exact (selected atHead.symm).elim
            · exact inTail)
  apply induction
  · simpa [RootStoredAtZero, ConcreteRestorationAccumulator.node?,
      initialRestorationAccumulatorFromRoot]
  · exact exactCount
  · exact fuelEnough
  · simpa [targetRequest] using everyPath

/-- One deployed root-sweep round therefore reaches the selected typed
query-batch fork.  This is temporal execution coverage, stronger than mere
membership of the request in the static request list. -/
theorem deployed_root_sweep_must_reach_query_batch
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {globalOracleCalls : Nat}
    (machine : UniformRawVerifierMachine HiddenTape TapeIdentity Observation
      Statement Proof Payload)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (runs : RootProjectedTotalizedRuns machine hidden runtime)
    (configuration : ConcreteRestorationConfiguration)
    (totalLimitMono : machine.adversaryLimits.totalCalls ≤
      configuration.oracleLimits.totalCalls)
    (freshLimitMono : machine.adversaryLimits.freshCalls ≤
      configuration.oracleLimits.freshCalls)
    (transitionIndex : Nat)
    (transitionWithin : transitionIndex < 1513)
    (transition : FutureFreeTransition)
    (transitionExact : verifierTransitionAt? runtime.node transitionIndex =
      some transition)
    (reply : VerifierReply)
    (eventExact : transition.event =
      .verifier (.squeezePair (.challenge .queryBatch) 0) reply)
    (environment : FutureFreeEnvironment)
    (globalRoom : configuration.oracleLimits.totalCalls ≤ globalOracleCalls)
    (pairRoomAtTarget : ∀
      (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (prepared : PreparedConcreteRestoration Statement Proof Payload),
      RootStoredAtZero runtime.node accumulator →
      prepareConcreteRestorationFromStartProgram
          (machine.blackBox.start hidden machine.observation) configuration
          accumulator
          { nodeId := 0, verifierTransitionIndex := transitionIndex } =
        .ready prepared →
      prepared.programmingBase.history.length + 2 ≤ globalOracleCalls)
    (result : Result) :
    SchedulerNativeCursorMustReach
      (fun cursor =>
        typedRestoredQueryBatchForkStartsHere (Result := Result)
          (machine.blackBox.start hidden machine.observation) environment
          configuration cursor.erase = true)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls)
        (machine.blackBox.start hidden machine.observation) environment
        runtime.node configuration 1513
          (deployedRootSweepClient 1 result)) := by
  apply finite_client_path_target_must_reach_query_batch machine hidden runtime
    runs configuration totalLimitMono freshLimitMono transitionIndex transition
    transitionExact reply eventExact environment globalRoom pairRoomAtTarget
    1513 1513 (deployedRootSweepClient 1 result) result
  · exact deployed_root_sweep_client_exact_request_count 1 result
  · omega
  · intro requests path
    exact deployed_root_sweep_every_path_covers_transition 1 result path
      (by omega) transitionIndex transitionWithin

#print axioms root_stored_after_charges_and_failure
#print axioms dispatch_one_preserves_rooted_must_reach
#print axioms finite_client_path_target_must_reach_query_batch
#print axioms deployed_root_sweep_must_reach_query_batch

end
end AspisK1.V7Tag73ConcreteRootSweepMustReach
