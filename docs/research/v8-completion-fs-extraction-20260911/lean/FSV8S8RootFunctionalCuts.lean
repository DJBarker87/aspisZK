import FSV8S8TerminalExecutionCuts
import FSV8ExactRootFunctionalRun
import AspisFormal.K1.V7Tag73CompletedRootProjection

/-!
# The terminal-checked S8 root constructs its finite-script execution

This is the S8 terminal-checking counterpart of the earlier exact-root
machine-prefix bridge.  It inverts one normally returned scheduler root and
then aligns the actual verifier machine prefix with the bounded transcript
script on the same finite tape.  No verifier entry oracle, body, result, or
functional run equation is supplied by the caller.

It does not yet construct the old Merkle `AnswerPrefix` values.  That next
bridge must project the execution cuts and the final shared oracle log.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8S8RootFunctionalCuts

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73CompletedRootProjection
open AspisK1.V7Tag73ExactCompilerResources
open FSBoundedTranscript
open FSV8V7OracleMachineBridge
open FSV8V7ProgrammedAlignment
open FSV8V7WholeScriptUniformLaw
open FSV8ProgrammedProjectionAlignment
open FSV8ProjectedPrefixProjectionFacts
open FSV8SuccessfulProgrammedAlignment
open FSV8FiniteTapeSchedulerSegment
open ExtractionCollectorOperationalAlphaScheduler
open FSV8ExactRootFunctionalRun
open FSV8S7DynamicSelectedRoot

noncomputable section

abbrev Block := FSBoundedTranscript.Block

structure SuccessfulRootMachinePrefixes
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls steps : Nat}
    (configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      globalOracleCalls)
    (hidden : HiddenTape) (finiteTape : FreshAnswerTape Block steps)
    (fallback : Block)
    (runtime : FSV8S8SelectedOrdinaryTerminal.Runtime TapeIdentity) where
  adversary : ProjectedMachinePrefixReturned configuration.adversaryLimits
    .adversary configuration.adversaryFuel emptyOracle
    (configuration.blackBox.start hidden configuration.observation)
    (freshAnswerTapeToList finiteTape)
  adversaryExecution :
    consumeProjectedMachinePrefix configuration.adversaryLimits .adversary
      (freshAnswerTapeToList finiteTape) configuration.adversaryFuel emptyOracle
      (configuration.blackBox.start hidden configuration.observation)
      empty_oracle_history_total_coherent = .ok adversary
  proverProjectionFacts :
    ProjectionFacts (extendFreshTape finiteTape fallback) finiteTape
      adversary.finalState
  verifier : ProjectedMachinePrefixReturned configuration.verifierLimits
    .verifier FSV8S7DynamicSelectedRoot.verifierBudget adversary.finalState
    (compileScript
      (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
        adversary.result)) adversary.remaining
  verifierExecution :
    consumeProjectedMachinePrefix configuration.verifierLimits .verifier
      adversary.remaining FSV8S7DynamicSelectedRoot.verifierBudget
      adversary.finalState
      (compileScript
        (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
          adversary.result)) adversary.finalCoherent = .ok verifier
  runtimeExact : runtime =
    { tapeIdentity := configuration.tapeIdentity hidden
      body := adversary.result
      proverFinalOracle := adversary.finalState
      verifierFinalOracle := verifier.finalState
      output := verifier.result }

theorem returned_root_constructs_machine_prefixes
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    (configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters))
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (sample : ExactCompilerSample HiddenTape parameters)
    (fallback : Block)
    (runtime : FSV8S8SelectedOrdinaryTerminal.Runtime TapeIdentity)
    (completed :
      (FSV8S8SelectedOrdinaryTerminal.runRoot parameters configuration
        transitionFuel sample).terminal = .returned runtime) :
    Nonempty (SuccessfulRootMachinePrefixes configuration sample.1 sample.2
      fallback runtime) := by
  have completedList :
      runSchedulerNativeListTerminal transitionFuel
          (FSV8S8SelectedOrdinaryTerminal.rootCursor configuration sample.1)
          (freshAnswerTapeToList sample.2) = .returned runtime := by
    rw [← run_scheduler_native_terminal_eq_list transitionFuel
      (exactCompilerTargetCaps parameters).length
      (FSV8S8SelectedOrdinaryTerminal.rootCursor configuration sample.1) sample.2]
    exact completed
  unfold runSchedulerNativeListTerminal at completedList
  unfold FSV8S8SelectedOrdinaryTerminal.rootCursor at completedList
  rw [run_scheduler_native_list_machine_factorization_of_positive
    (transitionFuel := transitionFuel) (positive := positive)] at completedList
  obtain ⟨adversary, adversaryExecution, completedVerifier⟩ :=
    terminal_after_projected_machine_prefix_returned_elim
      (positive := positive) (completed := completedList)
  rw [run_scheduler_native_list_machine_factorization_of_positive
    (transitionFuel := transitionFuel) (positive := positive)] at completedVerifier
  obtain ⟨verifier, verifierExecution, completedRuntime⟩ :=
    terminal_after_projected_machine_prefix_returned_elim
      (positive := positive) (completed := completedVerifier)
  rw [run_scheduler_native_list_returned_from transitionFuel positive]
    at completedRuntime
  split at completedRuntime
  next continuationPositive =>
    have runtimeExact : runtime =
        { tapeIdentity := configuration.tapeIdentity sample.1
          body := adversary.result
          proverFinalOracle := adversary.finalState
          verifierFinalOracle := verifier.finalState
          output := verifier.result } := by
      exact (SchedulerNativeTerminal.returned.inj completedRuntime).symm
    have projectionFacts := returned_from_empty_projectionFacts sample.2 fallback
      configuration.adversaryLimits .adversary configuration.adversaryFuel
      (configuration.blackBox.start sample.1 configuration.observation)
      adversary
    exact ⟨{
      adversary := adversary
      adversaryExecution := adversaryExecution
      proverProjectionFacts := projectionFacts
      verifier := verifier
      verifierExecution := verifierExecution
      runtimeExact := runtimeExact }⟩
  next continuationZero => simp at completedRuntime

structure RootFunctionalRun
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls steps : Nat}
    (configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      globalOracleCalls)
    (hidden : HiddenTape) (finiteTape : FreshAnswerTape Block steps)
    (fallback : Block)
    (runtime : FSV8S8SelectedOrdinaryTerminal.Runtime TapeIdentity) where
  prefixes : SuccessfulRootMachinePrefixes configuration hidden finiteTape
    fallback runtime
  functionalResult :
    (FSOracleExecution.run (extendFreshTape finiteTape fallback)
      (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
        prefixes.adversary.result)
      (projectOracleState prefixes.adversary.finalState)).1 =
        some prefixes.verifier.result
  finalAligned :
    StateAligned (extendFreshTape finiteTape fallback) finiteTape
      prefixes.verifier.finalState
      (FSOracleExecution.run (extendFreshTape finiteTape fallback)
        (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
          prefixes.adversary.result)
        (projectOracleState prefixes.adversary.finalState)).2

structure AcceptedRootExecution
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls steps : Nat}
    (configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      globalOracleCalls)
    (hidden : HiddenTape) (finiteTape : FreshAnswerTape Block steps)
    (fallback : Block)
    (runtime : FSV8S8SelectedOrdinaryTerminal.Runtime TapeIdentity)
    (accepted : FSV8S8SelectedOrdinaryTerminal.Success runtime.body) where
  functional : RootFunctionalRun configuration hidden finiteTape fallback runtime
  postSemantic : FSBoundedTranscript.Oracle
  cuts : S8ConcreteCommitmentCuts.SemanticExecutionCuts true
    configuration.binding runtime.body (extendFreshTape finiteTape fallback)
    (projectOracleState functional.prefixes.adversary.finalState)
    postSemantic accepted.relaxed.semantic
  directSuccess :
    (FSOracleExecution.run (extendFreshTape finiteTape fallback)
      (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
        runtime.body)
      (projectOracleState functional.prefixes.adversary.finalState)).1 =
        some (.ok accepted, runtime.output.2)
  c1ToFinal : FSBoundedTranscript.Prefix cuts.c1Cut
    (FSOracleExecution.run (extendFreshTape finiteTape fallback)
      (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
        runtime.body)
      (projectOracleState functional.prefixes.adversary.finalState)).2
  c2ToFinal : FSBoundedTranscript.Prefix cuts.postC2
    (FSOracleExecution.run (extendFreshTape finiteTape fallback)
      (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
        runtime.body)
      (projectOracleState functional.prefixes.adversary.finalState)).2

theorem returned_root_constructs_functional_run
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    (configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters))
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (sample : ExactCompilerSample HiddenTape parameters)
    (fallback : Block)
    (runtime : FSV8S8SelectedOrdinaryTerminal.Runtime TapeIdentity)
    (completed :
      (FSV8S8SelectedOrdinaryTerminal.runRoot parameters configuration
        transitionFuel sample).terminal = .returned runtime) :
    Nonempty (RootFunctionalRun configuration sample.1 sample.2 fallback runtime) := by
  obtain ⟨prefixes⟩ := returned_root_constructs_machine_prefixes parameters
    configuration transitionFuel positive sample fallback runtime completed
  have remainingEq :
      remainingFreshAnswers sample.2 prefixes.adversary.finalState =
        prefixes.adversary.remaining :=
    remainingFreshAnswers_eq_adversary_remaining sample.2
      configuration.adversaryLimits .adversary configuration.adversaryFuel
      (configuration.blackBox.start sample.1 configuration.observation)
      prefixes.adversary
  have machineExact := returned_prefix_is_finite_tape_run_of_available_eq
    prefixes.proverProjectionFacts configuration.verifierLimits .verifier
    FSV8S7DynamicSelectedRoot.verifierBudget
    (compileScript
      (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
        prefixes.adversary.result))
    prefixes.adversary.remaining remainingEq.symm prefixes.verifier
  have alignedEntry := project_state_aligned prefixes.proverProjectionFacts
  have functional := returned_compileScript_aligned
    configuration.verifierLimits .verifier
    (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
      prefixes.adversary.result)
    prefixes.adversary.finalState
    (projectOracleState prefixes.adversary.finalState)
    prefixes.verifier.result prefixes.verifier.finalState prefixes.verifier.steps
    alignedEntry (by simpa [FSV8S7DynamicSelectedRoot.verifierBudget] using machineExact)
  exact ⟨{
    prefixes := prefixes,
    functionalResult := functional.1,
    finalAligned := functional.2
  }⟩

/-- Eliminate the scheduler's dependent `Runtime.output` index only after the
functional record has been decomposed into its non-dependent adversary and
verifier prefixes.  This avoids transporting an independently supplied
`Success runtime.body` witness through the runtime equality. -/
theorem functional_run_result_on_runtime
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls steps : Nat}
    {configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      globalOracleCalls}
    {hidden : HiddenTape} {finiteTape : FreshAnswerTape Block steps}
    {fallback : Block}
    {runtime : FSV8S8SelectedOrdinaryTerminal.Runtime TapeIdentity}
    (functional : RootFunctionalRun configuration hidden finiteTape fallback
      runtime) :
    (FSOracleExecution.run (extendFreshTape finiteTape fallback)
      (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
        runtime.body)
      (projectOracleState functional.prefixes.adversary.finalState)).1 =
        some runtime.output := by
  obtain ⟨prefixes, functionalResult, _finalAligned⟩ := functional
  obtain ⟨adversary, _adversaryExecution, _projectionFacts, verifier,
      _verifierExecution, runtimeExact⟩ := prefixes
  cases runtimeExact
  exact functionalResult

/-- If the runtime returned by the scheduler is accepting, the same root
constructs the direct terminal-checked script success and its chronological
semantic cuts.  `initial` is definitionally the projected post-adversary
state, not a caller-selected oracle. -/
theorem returned_root_acceptance_constructs_execution_cuts
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    (configuration : DynamicConfiguration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters))
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (sample : ExactCompilerSample HiddenTape parameters)
    (fallback : Block)
    (runtime : FSV8S8SelectedOrdinaryTerminal.Runtime TapeIdentity)
    (accepted : FSV8S8SelectedOrdinaryTerminal.Success runtime.body)
    (completed :
      (FSV8S8SelectedOrdinaryTerminal.runRoot parameters configuration
        transitionFuel sample).terminal = .returned runtime)
    (acceptedRuntime : runtime.output.1 = .ok accepted) :
    Nonempty (AcceptedRootExecution configuration sample.1 sample.2 fallback
      runtime accepted) := by
  obtain ⟨functional⟩ := returned_root_constructs_functional_run parameters
    configuration transitionFuel positive sample fallback runtime completed
  have runtimeOutput : runtime.output =
      (.ok accepted, runtime.output.2) := by
    apply Prod.ext
    · exact acceptedRuntime
    · rfl
  have functionalResultRuntime :
      (FSOracleExecution.run (extendFreshTape sample.2 fallback)
        (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
          runtime.body)
        (projectOracleState functional.prefixes.adversary.finalState)).1 =
          some runtime.output :=
    functional_run_result_on_runtime functional
  have directSuccess :
      (FSOracleExecution.run (extendFreshTape sample.2 fallback)
        (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
          runtime.body)
        (projectOracleState functional.prefixes.adversary.finalState)).1 =
          some (.ok accepted, runtime.output.2) := by
    rw [← runtimeOutput]
    exact functionalResultRuntime
  obtain ⟨postSemantic, postSuffix, cuts, _result, semanticRun, _parsed,
      _beforeRun, _throughRun, _afterRun, _prefixInitial, prefixC1, prefixC2,
      suffixRun, finalOracle, _finalDigest, _operands, _terminal⟩ :=
    FSV8S8TerminalExecutionCuts.successful_run_constructs_terminal_execution_cuts
      configuration.binding runtime.body (extendFreshTape sample.2 fallback)
      (projectOracleState functional.prefixes.adversary.finalState)
      accepted runtime.output.2 directSuccess
  have suffixPrefix : Prefix postSemantic postSuffix := by
    have extended := FSOracleExecution.run_extends
      (extendFreshTape sample.2 fallback)
      (FSV8S4VerifierOnlySuffix.selectedSuffixBeforePoints
        accepted.relaxed.semantic.z
        (FSV8S7DynamicSelectedRoot.operationalCuts cuts.wire) runtime.body
        accepted.relaxed.semantic.finalDigest) postSemantic
    rw [suffixRun] at extended
    exact extended
  have postSuffixIsFinal : postSuffix =
      (FSOracleExecution.run (extendFreshTape sample.2 fallback)
        (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
          runtime.body)
        (projectOracleState functional.prefixes.adversary.finalState)).2 :=
    finalOracle.symm
  have c1ToFinal : Prefix cuts.c1Cut
      (FSOracleExecution.run (extendFreshTape sample.2 fallback)
        (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
          runtime.body)
        (projectOracleState functional.prefixes.adversary.finalState)).2 := by
    rw [← postSuffixIsFinal]
    exact prefix_trans prefixC1 (prefix_trans prefixC2 suffixPrefix)
  have c2ToFinal : Prefix cuts.postC2
      (FSOracleExecution.run (extendFreshTape sample.2 fallback)
        (FSV8S8SelectedOrdinaryTerminal.verifierScript configuration.binding
          runtime.body)
        (projectOracleState functional.prefixes.adversary.finalState)).2 := by
    rw [← postSuffixIsFinal]
    exact prefix_trans prefixC2 suffixPrefix
  exact ⟨{
    functional := functional
    postSemantic := postSemantic
    cuts := cuts
    directSuccess := directSuccess
    c1ToFinal := c1ToFinal
    c2ToFinal := c2ToFinal }⟩

#print axioms returned_root_constructs_machine_prefixes
#print axioms returned_root_constructs_functional_run
#print axioms functional_run_result_on_runtime
#print axioms returned_root_acceptance_constructs_execution_cuts

end
end AspisV8Completion.FSV8S8RootFunctionalCuts
