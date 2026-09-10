import AspisFormal.K1.V7Tag73ConcreteRootSweepMustReach
import AspisFormal.K1.V7Tag73RestoredQueryBatchBlockMarker

/-!
# Root-sweep reachability for an arbitrary query-batch block

The original temporal theorem stops at query-batch block zero.  This variant
keeps the same literal finite-client induction while retaining an arbitrary
deployed block index.  It is the execution bridge needed to route every block
actually consumed by the bounded nonzero sampler without classifying raw SHA
inputs.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ConcreteRootSweepMustReachQueryBatchBlock

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ActualNodeCausalProvenance
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ConcreteRestorationTraceInduction
open AspisK1.V7Tag73ConcreteRootSweepClient
open AspisK1.V7Tag73ConcreteRootSweepMustReach
open AspisK1.V7Tag73ExactCompilerOperationalCaps
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73RestoredQueryBatchBlockMarker
open AspisK1.V7Tag73RootQueryBatchForkBridge
open AspisK1.V7Tag73SchedulerNativeMustReach
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73TotalizedMachineReflection
open AspisK1.V7Tag73UniformRawVerifierExecution

noncomputable section

/-- If every request path covers a selected transition for block `block`, the
literal fuel-bounded root-sweep interpreter must reach that typed fork before
either programmed answer is read. -/
theorem finite_client_path_target_must_reach_query_batch_block
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
    (block : Fin 12)
    (reply : VerifierReply)
    (eventExact : transition.event =
      .verifier (.squeezePair (.challenge .queryBatch) block.val) reply)
    (environment : FutureFreeEnvironment)
    (globalRoom : configuration.oracleLimits.totalCalls ≤ globalOracleCalls)
    (forkRoom : machine.adversaryFuel + 2 ≤ globalOracleCalls)
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
        typedRestoredQueryBatchBlockForkStartsHere (Result := Result) block
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
    typedRestoredQueryBatchBlockForkStartsHere (Result := Result) block
      startProgram environment configuration cursor.erase = true
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
            obtain ⟨prepared, role, ready, coherent, historyBound,
                transitionPrepared, roleExact, ownerExact, blockExact,
                _outputExact, _advanceExact, _header⟩ :=
              literal_root_query_batch_dispatch_emits_typed_fork machine hidden
                runtime runs configuration totalLimitMono freshLimitMono
                transitionIndex transition transitionExact block.val reply
                eventExact environment accumulator rootStored resume
            have requestExact :=
              ready_preparation_request_exact startProgram configuration
                accumulator targetRequest prepared
                (by simpa [startProgram, targetRequest] using ready)
            have readyAtPrepared :
                prepareConcreteRestorationFromStartProgram startProgram
                    configuration accumulator prepared.request =
                  .ready prepared := by
              rw [requestExact]
              simpa [startProgram, targetRequest] using ready
            apply SchedulerNativeCursorMustReach.here
            simpa [target, requestExact] using
              (typed_query_batch_block_dispatch_one_is_marked block
                startProgram environment configuration accumulator prepared
                role resume readyAtPrepared roleExact ownerExact blockExact
                coherent globalRoom (by omega))
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

/-- One deployed exhaustive root-sweep round reaches any selected typed
query-batch block transition covered by the immutable root. -/
theorem deployed_root_sweep_must_reach_query_batch_block
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
    (rounds : Nat)
    (roundsPositive : 0 < rounds)
    (transition : FutureFreeTransition)
    (transitionExact : verifierTransitionAt? runtime.node transitionIndex =
      some transition)
    (block : Fin 12)
    (reply : VerifierReply)
    (eventExact : transition.event =
      .verifier (.squeezePair (.challenge .queryBatch) block.val) reply)
    (environment : FutureFreeEnvironment)
    (globalRoom : configuration.oracleLimits.totalCalls ≤ globalOracleCalls)
    (forkRoom : machine.adversaryFuel + 2 ≤ globalOracleCalls)
    (result : Result) :
    SchedulerNativeCursorMustReach
      (fun cursor =>
        typedRestoredQueryBatchBlockForkStartsHere (Result := Result) block
          (machine.blackBox.start hidden machine.observation) environment
          configuration cursor.erase = true)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls)
        (machine.blackBox.start hidden machine.observation) environment
        runtime.node configuration (rounds * 1513)
          (deployedRootSweepClient rounds result)) := by
  apply finite_client_path_target_must_reach_query_batch_block machine hidden
    runtime runs configuration totalLimitMono freshLimitMono transitionIndex
    transition transitionExact block reply eventExact environment globalRoom
    forkRoom (rounds * 1513) (rounds * 1513)
      (deployedRootSweepClient rounds result) result
  · exact deployed_root_sweep_client_exact_request_count rounds result
  · exact Nat.le_refl _
  · intro requests path
    exact deployed_root_sweep_every_path_covers_transition rounds result path
      roundsPositive transitionIndex transitionWithin

/-- The exact compiler adequacy arithmetic supplies all resource premises for
the block-indexed deployed root sweep. -/
theorem exact_deployed_root_sweep_must_reach_query_batch_block
    {HiddenTape TapeIdentity Observation Statement Proof Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {canonicalDriverFuel transitionFuel : Nat}
    (configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Result parameters)
    (adequate : ExactPlainRomOperationalAdequacy canonicalDriverFuel
      transitionFuel configuration)
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (runs : RootProjectedTotalizedRuns configuration.machine hidden runtime)
    (transitionIndex : Nat)
    (transitionWithin : transitionIndex < 1513)
    (rounds : Nat)
    (roundsPositive : 0 < rounds)
    (transition : FutureFreeTransition)
    (transitionExact : verifierTransitionAt? runtime.node transitionIndex =
      some transition)
    (block : Fin 12)
    (reply : VerifierReply)
    (eventExact : transition.event =
      .verifier (.squeezePair (.challenge .queryBatch) block.val) reply)
    (environment : FutureFreeEnvironment)
    (result : Result) :
    SchedulerNativeCursorMustReach
      (fun cursor =>
        typedRestoredQueryBatchBlockForkStartsHere (Result := Result) block
          (configuration.machine.blackBox.start hidden
            configuration.machine.observation)
          environment configuration.restorationConfiguration cursor.erase =
            true)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (configuration.machine.blackBox.start hidden
          configuration.machine.observation)
        environment runtime.node configuration.restorationConfiguration
          (rounds * 1513) (deployedRootSweepClient rounds result)) := by
  have replayExtendsRoot :=
    adequate_replay_limits_extend_root_adversary configuration adequate
  have forkRoom : configuration.machine.adversaryFuel + 2 ≤
      globalFull256OracleCallCap parameters := by
    have fuelBound := configuration.bounds.rootAdversaryFuel
    unfold globalFull256OracleCallCap deployedFull256VerifierCallCap
    omega
  exact deployed_root_sweep_must_reach_query_batch_block
    configuration.machine hidden runtime runs configuration.restorationConfiguration
    replayExtendsRoot.1 replayExtendsRoot.2 transitionIndex transitionWithin
    rounds roundsPositive transition transitionExact block reply eventExact
    environment configuration.bounds.replayTotalCalls forkRoom result

#print axioms finite_client_path_target_must_reach_query_batch_block
#print axioms deployed_root_sweep_must_reach_query_batch_block
#print axioms exact_deployed_root_sweep_must_reach_query_batch_block

end
end AspisK1.V7Tag73ConcreteRootSweepMustReachQueryBatchBlock
