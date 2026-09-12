import AspisFormal.K1.V7Tag73ConcreteRootSweepMustReachGamma
import AspisFormal.K1.V7Tag73SchedulerNativeMustReachForkCap

/-!
# Per-request fork cap for concrete restoration reachability

One concrete restoration request allocates at most one atomic pair.  This
strengthens the existing rooted must-reach dispatcher theorem with the exact
two-coordinate allowance required by the restored-gamma suffix audit.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73ConcreteRestorationMustReachForkCap

open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ActualNodeCausalProvenance
open AspisK1.V7Tag73ConcreteRestorationClient
open AspisK1.V7Tag73ConcreteRootSweepMustReachGamma
open AspisK1.V7Tag73ConcreteRootSweepClient
open AspisK1.V7Tag73CompletedRootProjection
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerOperationalCaps
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactLegalSameTapeEvent
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FutureFreeFullControl
open AspisK1.V7Tag73InteractiveAncestor
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73RawSameTapeSource
open AspisK1.V7Tag73RestoredChallengeCausalMarker
open AspisK1.V7Tag73RootGammaForkBridge
open AspisK1.V7Tag73SchedulerNativeMustReachForkCap
open AspisK1.V7Tag73SchedulerNativePlainRomExperiment
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73TotalizedMachineReflection
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73UniformRawVerifierExecution

noncomputable section

universe u

/-- A non-target concrete restoration request adds at most one two-coordinate
fork before any bounded target in its continuation. -/
theorem dispatch_one_preserves_rooted_must_reach_with_fork_cap
    {Statement Proof Payload Result : Type u}
    {globalOracleCalls : Nat}
    (target : SchedulerNativeCursor globalOracleCalls
      (ConcreteRestorationClientRun Statement Proof Payload Result) → Prop)
    (tailCap : Nat)
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
        SchedulerNativeCursorMustReachWithForkCap target tailCap
          (resume reply nextAccumulator)) :
    SchedulerNativeCursorMustReachWithForkCap target (2 + tailCap)
      (dispatchOneConcreteRestoration startProgram environment configuration
        accumulator request resume) := by
  have failureTail : ∀
      (failureRequest : ConcreteRestorationRequest)
      (reason : ConcreteRestorationFailure)
      (nextAccumulator :
        ConcreteRestorationAccumulator Statement Proof Payload)
      (nextRoot : RootStoredAtZero root nextAccumulator),
      SchedulerNativeCursorMustReachWithForkCap target tailCap
        (resume (.failed reason)
          (nextAccumulator.addFailure failureRequest reason)) := by
    intro failureRequest reason nextAccumulator nextRoot
    apply continuations (.failed reason)
      (nextAccumulator.addFailure failureRequest reason)
    simpa [RootStoredAtZero, ConcreteRestorationAccumulator.node?,
      ConcreteRestorationAccumulator.addFailure] using nextRoot
  have failureSafe : ∀
      (failureRequest : ConcreteRestorationRequest)
      (reason : ConcreteRestorationFailure)
      (nextAccumulator :
        ConcreteRestorationAccumulator Statement Proof Payload)
      (nextRoot : RootStoredAtZero root nextAccumulator),
      SchedulerNativeCursorMustReachWithForkCap target (2 + tailCap)
        (resume (.failed reason)
          (nextAccumulator.addFailure failureRequest reason)) := by
    intro failureRequest reason nextAccumulator nextRoot
    exact scheduler_native_must_reach_fork_cap_mono
      (failureTail failureRequest reason nextAccumulator nextRoot) (by omega)
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
      by_cases prefixCoherent : HistoryTotalCoherent prepared.programmingBase
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
            apply SchedulerNativeCursorMustReachWithForkCap.forkPair
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
                exact failureTail prepared.request reason
                  (afterCoordinates.addCharges [.programmedPoints inserted]) (by
                    simpa [RootStoredAtZero,
                      ConcreteRestorationAccumulator.node?,
                      ConcreteRestorationAccumulator.addCharges] using
                        afterCoordinatesRoot)
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
                    apply SchedulerNativeCursorMustReachWithForkCap.machine
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
                              exact failureTail prepared.request
                                (.proverReplayAbort reason) afterProver
                                afterProverRoot
                          | timeout =>
                              exact failureTail prepared.request
                                .proverReplayTimeout afterProver afterProverRoot
                      | ok adversaryValue =>
                          simp only
                          by_cases bindingMismatch :
                              FixedBindings.ofContext
                                  adversaryValue.rawMessages.context ≠
                                prepared.restoredState.current.bindings
                          next =>
                            rw [dif_pos bindingMismatch]
                            exact failureTail prepared.request
                              .restoredBindingMismatch afterProver afterProverRoot
                          next =>
                            rw [dif_neg bindingMismatch]
                            by_cases verifierRoom : StageHasOracleRoom
                                configuration.oracleLimits proverFinalOracle
                                configuration.verifierFuel
                            next =>
                              simp only [verifierRoom, if_pos]
                              apply SchedulerNativeCursorMustReachWithForkCap.machine
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
                                        exact failureTail prepared.request
                                          (.verifierSuffixAbort reason)
                                          afterVerifier afterVerifierRoot
                                    | timeout =>
                                        exact failureTail prepared.request
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
                                      _root_.AspisK1.V7Tag73OperationalNodeCertificate.node_lookup_preserved_by_add_node
                                      charged node root 0 (by
                                        simpa [charged, RootStoredAtZero,
                                          ConcreteRestorationAccumulator.node?,
                                          ConcreteRestorationAccumulator.addCharges]
                                          using afterVerifierRoot)
                            next =>
                              rw [dif_neg verifierRoom]
                              exact failureTail prepared.request
                                .verifierSuffixRoom afterProver afterProverRoot
                  next =>
                    simp only [proverRoom, if_neg]
                    exact failureTail prepared.request .proverReplayRoom
                      afterProgramming afterProgrammingRoot
                next =>
                  simp only [afterCoherent, if_neg]
                  exact failureTail prepared.request .incoherentProgrammedOracle
                    afterProgramming afterProgrammingRoot
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

/-! ## Lifting the local cap through a finite client -/

/-- A structural certificate that a client reaches the selected request after
exactly the advertised number of preceding requests, independently of every
reply.  The `later` constructor intentionally permits an earlier occurrence;
the operational theorem stops at that occurrence and merely weakens its cap. -/
inductive ConcreteClientMustRequestWithin {Result : Type u}
    (target : ConcreteRestorationRequest) :
    Nat → ConcreteRestorationClient Result → Prop where
  | here (next : ConcreteRestorationReply → ConcreteRestorationClient Result) :
      ConcreteClientMustRequestWithin target 0 (.restore target next)
  | later (request : ConcreteRestorationRequest)
      (next : ConcreteRestorationReply → ConcreteRestorationClient Result)
      {prior : Nat}
      (tails : ∀ reply,
        ConcreteClientMustRequestWithin target prior (next reply)) :
      ConcreteClientMustRequestWithin target (prior + 1)
        (.restore request next)

/-- A client whose selected request is structurally within `requestCap`
requests reaches the typed gamma fork after at most two fork coordinates per
preceding request. -/
theorem finite_client_target_must_reach_gamma_with_fork_cap
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
      .verifier (.squeezePair (.challenge .gamma) 0) reply)
    (environment : FutureFreeEnvironment)
    (globalRoom : configuration.oracleLimits.totalCalls ≤ globalOracleCalls)
    (forkRoom : machine.adversaryFuel + 2 ≤ globalOracleCalls)
    (fuel requestCap : Nat)
    (client : ConcreteRestorationClient Result)
    (within : ConcreteClientMustRequestWithin
      { nodeId := 0, verifierTransitionIndex := transitionIndex }
      requestCap client)
    (fuelEnough : requestCap + 1 ≤ fuel) :
    SchedulerNativeCursorMustReachWithForkCap
      (fun cursor =>
        IsTypedRestoredChallengeForkStartForRequest (Result := Result)
          (.challenge .gamma)
          { nodeId := 0, verifierTransitionIndex := transitionIndex }
          (machine.blackBox.start hidden machine.observation) environment
          configuration cursor.erase)
      (2 * requestCap)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls)
        (machine.blackBox.start hidden machine.observation) environment
        runtime.node configuration fuel client) := by
  let startProgram := machine.blackBox.start hidden machine.observation
  let targetRequest : ConcreteRestorationRequest :=
    { nodeId := 0, verifierTransitionIndex := transitionIndex }
  let target := fun cursor : SchedulerNativeCursor globalOracleCalls
      (ConcreteRestorationClientRun Statement Proof Payload Result) =>
    IsTypedRestoredChallengeForkStartForRequest (Result := Result)
      (.challenge .gamma) targetRequest startProgram environment configuration
        cursor.erase
  let motive := fun (remainingFuel : Nat)
      (accumulator : ConcreteRestorationAccumulator Statement Proof Payload)
      (residualClient : ConcreteRestorationClient Result)
      (cursor : SchedulerNativeCursor globalOracleCalls
        (ConcreteRestorationClientRun Statement Proof Payload Result)) =>
    RootStoredAtZero runtime.node accumulator →
      ∀ residualCap,
        ConcreteClientMustRequestWithin targetRequest residualCap residualClient →
        residualCap + 1 ≤ remainingFuel →
        SchedulerNativeCursorMustReachWithForkCap target (2 * residualCap)
          cursor
  have induction :=
    start_concrete_restoration_client_from_root_dependent_induction
      (globalOracleCalls := globalOracleCalls) startProgram environment
      runtime.node configuration fuel client motive
      (by
        intro remainingFuel accumulator terminalResult rootStored residualCap
          certified enough
        cases certified)
      (by
        intro accumulator request next rootStored residualCap certified enough
        cases certified <;> omega)
      (by
        intro remainingFuel accumulator request next resume continuations
          rootStored residualCap certified enough
        cases certified with
        | here certifiedNext =>
            obtain ⟨prepared, role, ready, coherent, historyBound,
                transitionPrepared, roleExact, ownerExact, blockExact,
                _outputExact, _advanceExact, _header⟩ :=
              literal_root_gamma_dispatch_emits_typed_fork machine hidden
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
            apply SchedulerNativeCursorMustReachWithForkCap.here
            have exactStart :=
              typed_challenge_dispatch_one_starts_exact_request
                (.challenge .gamma) targetRequest startProgram environment
                configuration accumulator prepared role resume requestExact
                readyAtPrepared roleExact ownerExact blockExact coherent
                globalRoom (by omega)
            rw [requestExact] at exactStart
            simpa only [target] using exactStart
        | @later certifiedRequest certifiedNext prior tails =>
            by_cases selected : request = targetRequest
            · subst request
              obtain ⟨prepared, role, ready, coherent, historyBound,
                  transitionPrepared, roleExact, ownerExact, blockExact,
                  _outputExact, _advanceExact, _header⟩ :=
                literal_root_gamma_dispatch_emits_typed_fork machine hidden
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
              apply scheduler_native_must_reach_fork_cap_mono
                (SchedulerNativeCursorMustReachWithForkCap.here _ (by
                  have exactStart :=
                    typed_challenge_dispatch_one_starts_exact_request
                      (.challenge .gamma) targetRequest startProgram environment
                      configuration accumulator prepared role resume requestExact
                      readyAtPrepared roleExact ownerExact blockExact coherent
                      globalRoom (by omega)
                  rw [requestExact] at exactStart
                  simpa only [target] using exactStart))
              omega
            · simpa [Nat.mul_add, Nat.mul_one, Nat.add_comm, Nat.add_left_comm,
                Nat.add_assoc] using
                dispatch_one_preserves_rooted_must_reach_with_fork_cap
                  target (2 * prior) runtime.node startProgram environment
                  configuration accumulator request resume rootStored (by
                    intro branchReply nextAccumulator nextRoot
                    exact continuations branchReply nextAccumulator nextRoot
                      prior (tails branchReply) (by omega)))
  apply induction
  · simpa [RootStoredAtZero, ConcreteRestorationAccumulator.node?,
      initialRestorationAccumulatorFromRoot]
  · simpa [targetRequest] using within
  · exact fuelEnough

/-- The literal interval client reaches offset `offset` after exactly that
many preceding requests, regardless of the replies to those requests. -/
theorem prepend_root_transition_sweep_must_request_within
    {Result : Type u}
    (start count offset : Nat) (offsetWithin : offset < count)
    (tail : ConcreteRestorationClient Result) :
    ConcreteClientMustRequestWithin
      { nodeId := 0, verifierTransitionIndex := start + offset }
      offset (prependRootTransitionSweep start count tail) := by
  induction offset generalizing start count with
  | zero =>
      cases count with
      | zero => omega
      | succ count =>
          simpa [prependRootTransitionSweep] using
            (ConcreteClientMustRequestWithin.here
              (target := { nodeId := 0, verifierTransitionIndex := start })
              (fun _reply => prependRootTransitionSweep (start + 1) count tail))
  | succ offset ih =>
      cases count with
      | zero => omega
      | succ count =>
          rw [prependRootTransitionSweep_succ]
          apply ConcreteClientMustRequestWithin.later
          intro branchReply
          have tailWithin := ih (start + 1) count (by omega)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tailWithin

/-- In one deployed sweep, transition `i` is reached after at most the two
fork coordinates allocated by each of the `i` preceding requests. -/
theorem deployed_one_round_must_reach_gamma_with_fork_cap
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
      .verifier (.squeezePair (.challenge .gamma) 0) reply)
    (environment : FutureFreeEnvironment)
    (globalRoom : configuration.oracleLimits.totalCalls ≤ globalOracleCalls)
    (forkRoom : machine.adversaryFuel + 2 ≤ globalOracleCalls)
    (result : Result) :
    SchedulerNativeCursorMustReachWithForkCap
      (fun cursor =>
        IsTypedRestoredChallengeForkStartForRequest (Result := Result)
          (.challenge .gamma)
          { nodeId := 0, verifierTransitionIndex := transitionIndex }
          (machine.blackBox.start hidden machine.observation) environment
          configuration cursor.erase)
      (2 * transitionIndex)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalOracleCalls)
        (machine.blackBox.start hidden machine.observation) environment
        runtime.node configuration 1513
          (deployedRootSweepClient 1 result)) := by
  apply finite_client_target_must_reach_gamma_with_fork_cap machine hidden
    runtime runs configuration totalLimitMono freshLimitMono transitionIndex
    transition transitionExact reply eventExact environment globalRoom forkRoom
    1513 transitionIndex (deployedRootSweepClient 1 result)
  · change ConcreteClientMustRequestWithin
      { nodeId := 0, verifierTransitionIndex := transitionIndex }
      transitionIndex
      (prependRootTransitionSweep 0 1513 (.pure result))
    simpa using prepend_root_transition_sweep_must_request_within
      0 1513 transitionIndex transitionWithin (.pure result)
  · omega

/-- Production-facing specialization: operational adequacy discharges the
oracle-limit premises and the selected one-round root sweep carries the exact
`2 * transitionIndex` cap. -/
theorem production_one_round_configuration_must_reach_gamma_with_fork_cap
    {HiddenTape TapeIdentity Observation Statement Proof Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {canonicalDriverFuel transitionFuel : Nat}
    (base : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Proof Payload Witness parameters)
    (extractor : ExactPlainRomWitnessExtractor Statement Proof Payload Witness)
    (withinForkCap : 1 * 1513 ≤ parameters.forkRequestCap)
    (adequate : ExactPlainRomOperationalAdequacy canonicalDriverFuel
      transitionFuel
        (exactRootSweepWitnessConfiguration base 1 extractor withinForkCap))
    (hidden : HiddenTape)
    (runtime : SchedulerNativePlainRomRootRuntime TapeIdentity Statement Proof
      Payload)
    (runs : RootProjectedTotalizedRuns
      (exactRootSweepWitnessConfiguration base 1 extractor
        withinForkCap).machine hidden runtime)
    (transitionIndex : Nat)
    (transitionWithin : transitionIndex < 1513)
    (transition : FutureFreeTransition)
    (transitionExact : verifierTransitionAt? runtime.node transitionIndex =
      some transition)
    (reply : VerifierReply)
    (eventExact : transition.event =
      .verifier (.squeezePair (.challenge .gamma) 0) reply) :
    SchedulerNativeCursorMustReachWithForkCap
      (fun cursor =>
        IsTypedRestoredChallengeForkStartForRequest
          (Result := ExactPlainRomWitnessExtractor Statement Proof Payload Witness)
          (.challenge .gamma)
          { nodeId := 0, verifierTransitionIndex := transitionIndex }
          (base.machine.blackBox.start hidden base.machine.observation)
          base.machine.environment base.restorationConfiguration cursor.erase)
      (2 * transitionIndex)
      (startConcreteRestorationClientFromRoot
        (globalOracleCalls := globalFull256OracleCallCap parameters)
        (base.machine.blackBox.start hidden base.machine.observation)
        base.machine.environment runtime.node base.restorationConfiguration
        1513 (deployedRootSweepClient 1 extractor)) := by
  have replayExtendsRoot :=
    adequate_replay_limits_extend_root_adversary
      (exactRootSweepWitnessConfiguration base 1 extractor withinForkCap)
      adequate
  have forkRoom : base.machine.adversaryFuel + 2 ≤
      globalFull256OracleCallCap parameters := by
    have fuelBound := base.bounds.rootAdversaryFuel
    unfold globalFull256OracleCallCap deployedFull256VerifierCallCap
    omega
  exact deployed_one_round_must_reach_gamma_with_fork_cap base.machine hidden
    runtime runs base.restorationConfiguration replayExtendsRoot.1
    replayExtendsRoot.2 transitionIndex transitionWithin transition
    transitionExact reply eventExact base.machine.environment
    base.bounds.replayTotalCalls forkRoom extractor

#print axioms dispatch_one_preserves_rooted_must_reach_with_fork_cap
#print axioms finite_client_target_must_reach_gamma_with_fork_cap
#print axioms prepend_root_transition_sweep_must_request_within
#print axioms deployed_one_round_must_reach_gamma_with_fork_cap
#print axioms production_one_round_configuration_must_reach_gamma_with_fork_cap

end
end AspisK1.V7Tag73ConcreteRestorationMustReachForkCap
