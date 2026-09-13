import FSV8ExactRootSuccessfulPrefixes
import FSV8SuccessfulProgrammedAlignment
import FSV8FiniteTapeSchedulerSegment

/-!
# Exact-root success constructs the functional verifier run

This file connects a normally returned exact scheduler root to the actual
bounded-transcript interpretation of the verifier script.  The fresh-answer
suffix is derived from the adversary prefix's literal tape partition.  No
static room premise or equality of controllers on unreachable histories is
assumed.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8ExactRootFunctionalRun

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ProjectedMachinePrefix
open AspisK1.V7Tag73ExactCompilerResources
open FSBoundedTranscript
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedSuccessfulReplay
open ExtractionCollectorOperationalAlphaScheduler
open FSV8V7OracleMachineBridge
open FSV8V7ProgrammedAlignment
open FSV8V7WholeScriptUniformLaw
open FSV8ProgrammedProjectionAlignment
open FSV8FiniteTapeSchedulerSegment
open FSV8SuccessfulProgrammedAlignment
open FSV8ExactRootCursor
open FSV8ExactRootSuccessfulPrefixes

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

/-- One exact-root success together with the functional run that its actual
verifier machine prefix constructs.  All fields are outputs of the theorem. -/
structure ExactRootFunctionalRun
    {HiddenTape TapeIdentity Observation : Type}
    {globalOracleCalls n m steps : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      globalOracleCalls n m)
    (hidden : HiddenTape) (finiteTape : FreshAnswerTape Block steps)
    (fallback : Block) (runtime : Runtime TapeIdentity configuration.z) where
  prefixes : SuccessfulRootMachinePrefixes configuration hidden finiteTape
    fallback runtime
  functionalResult :
    (FSOracleExecution.run (extendFreshTape finiteTape fallback)
      (wholeStagedScript configuration.firstWork configuration.secondWork
        configuration.z configuration.cuts prefixes.adversary.result
        configuration.initialDigest)
      (projectOracleState prefixes.adversary.finalState)).1 =
        some prefixes.verifier.result
  finalAligned :
    StateAligned (extendFreshTape finiteTape fallback) finiteTape
      prefixes.verifier.finalState
      (FSOracleExecution.run (extendFreshTape finiteTape fallback)
        (wholeStagedScript configuration.firstWork configuration.secondWork
          configuration.z configuration.cuts prefixes.adversary.result
          configuration.initialDigest)
        (projectOracleState prefixes.adversary.finalState)).2

/-- The unused suffix retained by the adversary projected prefix is exactly
the suffix obtained by dropping the actual fresh-call count from the same
master tape. -/
theorem remainingFreshAnswers_eq_adversary_remaining
    {Result : Type} {steps : Nat}
    (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (program : OracleMachine Result)
    (returned : ProjectedMachinePrefixReturned limits actor fuel emptyOracle
      program (freshAnswerTapeToList finiteTape)) :
    remainingFreshAnswers finiteTape returned.finalState = returned.remaining := by
  have freshExact := projected_fresh_returned_trace_fresh_calls_exact
    limits actor fuel emptyOracle program returned.freshQueries returned.result
      returned.finalState returned.steps returned.trace
  have dropped := congrArg (List.drop returned.freshQueries.length)
    returned.availableExact
  unfold remainingFreshAnswers
  rw [freshExact]
  simp only [emptyOracle, Nat.zero_add]
  simpa using dropped

/-- Available-list reindexing for the finite-tape run theorem.  The returned
record itself remains the source of the result, final oracle and step count;
no cast-created replacement record is introduced. -/
theorem returned_prefix_is_finite_tape_run_of_available_eq
    {Result : Type} {steps : Nat} {tape : FSBoundedTranscript.Tape}
    {finiteTape : FreshAnswerTape Block steps} {state : OracleState}
    (facts : ProjectionFacts tape finiteTape state)
    (limits : OracleLimits) (actor : QueryActor) (fuel : Nat)
    (program : OracleMachine Result) (available : List Block)
    (availableEq : available = remainingFreshAnswers finiteTape state)
    (returned : ProjectedMachinePrefixReturned limits actor fuel state program
      available) :
    runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel
        state program =
      { halt := .returned returned.result
        oracle := returned.finalState
        steps := returned.steps } := by
  subst available
  exact returned_prefix_is_finite_tape_run facts limits actor fuel program
    returned

/-- A normally returned exact root constructs the same-body functional
verifier execution and an aligned final oracle state. -/
theorem returned_exact_root_constructs_functional_run
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
    Nonempty (ExactRootFunctionalRun configuration sample.1 sample.2 fallback
      runtime) := by
  obtain ⟨prefixes⟩ := returned_exact_root_constructs_machine_prefixes
    parameters configuration transitionFuel positive sample fallback runtime
      completed
  have remainingEq :
      remainingFreshAnswers sample.2 prefixes.adversary.finalState =
        prefixes.adversary.remaining :=
    remainingFreshAnswers_eq_adversary_remaining sample.2
      configuration.adversaryLimits .adversary configuration.adversaryFuel
      (configuration.blackBox.start sample.1 configuration.observation)
      prefixes.adversary
  have machineExact := returned_prefix_is_finite_tape_run_of_available_eq
    prefixes.proverProjectionFacts configuration.verifierLimits .verifier
    (stagedBudget n m)
    (compileScript (wholeStagedScript configuration.firstWork
      configuration.secondWork configuration.z configuration.cuts
      prefixes.adversary.result configuration.initialDigest))
    prefixes.adversary.remaining remainingEq.symm prefixes.verifier
  have alignedEntry := project_state_aligned prefixes.proverProjectionFacts
  have functional := returned_compileScript_aligned
    configuration.verifierLimits .verifier
    (wholeStagedScript configuration.firstWork configuration.secondWork
      configuration.z configuration.cuts prefixes.adversary.result
      configuration.initialDigest)
    prefixes.adversary.finalState
    (projectOracleState prefixes.adversary.finalState)
    prefixes.verifier.result prefixes.verifier.finalState prefixes.verifier.steps
    alignedEntry (by simpa [stagedBudget] using machineExact)
  exact ⟨{
    prefixes := prefixes
    functionalResult := functional.1
    finalAligned := functional.2 }⟩

#print axioms remainingFreshAnswers_eq_adversary_remaining
#print axioms returned_prefix_is_finite_tape_run_of_available_eq
#print axioms returned_exact_root_constructs_functional_run

end
end AspisV8Completion.FSV8ExactRootFunctionalRun
