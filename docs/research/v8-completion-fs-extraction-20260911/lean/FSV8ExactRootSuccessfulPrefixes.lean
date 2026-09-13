import FSV8ExactRootCursor
import FSV8ProjectedPrefixProjectionFacts
import AspisFormal.K1.V7Tag73CompletedRootProjection

/-!
# Successful exact V8 root machine prefixes

This leaf inverts a normally returned exact root into the actual adversary
machine prefix and the actual whole-verifier machine prefix.  Both prefixes
consume one literal partition of the same master answer tape.  No internal
pre-alpha cut or worst-case continuation-room premise is introduced here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8ExactRootSuccessfulPrefixes

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73SchedulerNativeResult
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73SchedulerMachineFactorization
open AspisK1.V7Tag73CompletedRootProjection
open FSBoundedTranscript
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8V7OracleMachineBridge
open FSV8V7WholeScriptUniformLaw
open FSV8ProgrammedProjectionAlignment
open FSV8ProjectedPrefixProjectionFacts
open FSV8ExactRootCursor

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

/-- The two normally returned machine segments underlying one returned exact
root.  `runtimeExact` identifies every runtime field with those segments;
`proverProjectionFacts` uses the original master tape, not a reconstructed
analysis tape. -/
structure SuccessfulRootMachinePrefixes
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls n m steps : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (hidden : HiddenTape) (finiteTape : FreshAnswerTape Block steps)
    (fallback : Block) (runtime : Runtime TapeIdentity configuration.z) where
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
    .verifier (stagedBudget n m) adversary.finalState
    (compileScript (wholeStagedScript configuration.firstWork
      configuration.secondWork configuration.z configuration.cuts
      adversary.result configuration.initialDigest)) adversary.remaining
  verifierExecution :
    consumeProjectedMachinePrefix configuration.verifierLimits .verifier
      adversary.remaining (stagedBudget n m) adversary.finalState
      (compileScript (wholeStagedScript configuration.firstWork
        configuration.secondWork configuration.z configuration.cuts
        adversary.result configuration.initialDigest)) adversary.finalCoherent =
      .ok verifier
  runtimeExact : runtime =
    { tapeIdentity := configuration.tapeIdentity hidden
      body := adversary.result
      proverFinalOracle := adversary.finalState
      verifierFinalOracle := verifier.finalState
      output := verifier.result }

/-- A returned fixed-tape execution of the exact root constructs both actual
machine prefixes and their exact runtime.  Remaining tape coordinates are
retained in the two dependent prefix records. -/
theorem returned_exact_root_constructs_machine_prefixes
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (positive : 0 < transitionFuel)
    (sample : ExactCompilerSample HiddenTape parameters)
    (fallback : Block) (runtime : Runtime TapeIdentity configuration.z)
    (completed :
      (runExactRoot parameters configuration transitionFuel sample).terminal =
        .returned runtime) :
    Nonempty (SuccessfulRootMachinePrefixes configuration sample.1 sample.2
      fallback runtime) := by
  have completedList :
      runSchedulerNativeListTerminal transitionFuel
          (rootCursor configuration sample.1)
          (freshAnswerTapeToList sample.2) = .returned runtime := by
    rw [← run_scheduler_native_terminal_eq_list transitionFuel
      (exactCompilerTargetCaps parameters).length
      (rootCursor configuration sample.1) sample.2]
    exact completed
  unfold runSchedulerNativeListTerminal at completedList
  unfold rootCursor at completedList
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
    exact ⟨
      { adversary := adversary
        adversaryExecution := adversaryExecution
        proverProjectionFacts := projectionFacts
        verifier := verifier
        verifierExecution := verifierExecution
        runtimeExact := runtimeExact }⟩
  next continuationZero => simp at completedRuntime

#print axioms returned_exact_root_constructs_machine_prefixes

end
end AspisV8Completion.FSV8ExactRootSuccessfulPrefixes
