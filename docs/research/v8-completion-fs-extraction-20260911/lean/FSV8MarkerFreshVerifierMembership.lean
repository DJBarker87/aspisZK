import FSV8MarkerFreshVerifierQueryBridge
import FSV8ProgrammedAlphaMarkerHistoryPrefix
import FSV8CompiledWholeFactorization

/-!
# The fresh alpha marker belongs to the actual verifier machine prefix

This leaf connects the literal source marker query to the proof-relevant
fresh-query list of the same returned exact-root verifier segment.  It uses
the actual finite-tape machine execution and the actual projected prefix; no
caller supplies an unrelated semantic program or answer log.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 2600

namespace AspisV8Completion.FSV8MarkerFreshVerifierMembership

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerGammaTraceOccurrence
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorOperationalAlphaScheduler
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8V7OracleMachineBridge
open FSV8V7WholeScriptUniformLaw
open FSV8ProgrammedProjectionAlignment
open FSV8ExactRootCursor
open FSV8ExactRootFunctionalRun
open FSV8PostOODGammaScript
open FSLiveSourceFunctionalMiddle
open FSV8ExecutablePreAlphaFactorization
open FSV8BeforeAlphaMarkerFactorization
open FSV8ProgrammedAlphaCandidateDisposition
open FSV8ProgrammedAlphaCutWitness
open FSV8ProgrammedAlphaMarkerHistoryPrefix
open FSV8MarkerFreshVerifierQueryBridge
open FSV8FreshQueryRecord
open FSV8ReturnedBindKnownPrefix
open FSV8ExecutableWholeFactorization
open FSV8CompiledWholeFactorization
open FSLiveSelectedMiddleQueryRho

noncomputable section

abbrev Block := FSBoundedTranscript.Block

/-- A successful missing marker query from the source-shaped cut occurs at
one exact coordinate of the returned verifier segment's fresh-query list. -/
theorem markerFresh_pair_mem_actual_verifier_freshQueries
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (sample : ExactCompilerSample HiddenTape parameters)
    (fallback : Block) (runtime : Runtime TapeIdentity configuration.z)
    (execution : ExactRootFunctionalRun configuration sample.1 sample.2
      fallback runtime)
    (record : Record execution.prefixes.adversary.result configuration.z)
    (finalDigest : Block)
    (verifierExact : execution.prefixes.verifier.result =
      (.ok record, finalDigest))
    (out : FSV7OODBodyScript.Result) (gamma : FSNonzeroQM31.K)
    (sourceDigest : Block)
    (boundary : PreAlpha out gamma execution.prefixes.adversary.result
      configuration.z)
    (preDigest : Block)
    (before : BeforeAlphaMarker out gamma
      execution.prefixes.adversary.result configuration.z)
    (middle : Success out gamma execution.prefixes.adversary.result
      configuration.z)
    (middleResultDigest : Block)
    (cutWitness : ProgrammedAlphaCutWitness
      (tape := extendFreshTape sample.2 fallback) sample.2
      configuration.verifierLimits .verifier
      configuration.firstWork configuration.secondWork configuration.z
      execution.prefixes.adversary.result configuration.initialDigest
      execution.prefixes.adversary.finalState
      (projectOracleState execution.prefixes.adversary.finalState)
      (stagedBudget n m) out gamma sourceDigest boundary preDigest before
      middle middleResultDigest)
    (markerNext : OracleState)
    (markerQuery :
      let sourceRun := sourceMachineRun sample.2
        configuration.verifierLimits .verifier configuration.firstWork
        configuration.secondWork execution.prefixes.adversary.result
        configuration.initialDigest execution.prefixes.adversary.finalState
        (stagedBudget n m)
      let middleFuel := stagedBudget n m - sourceRun.steps
      let markerRun := runMachine (controllerFromFreshAnswerTape sample.2)
        configuration.verifierLimits .verifier middleFuel sourceRun.oracle
        (compileScript (beforeAlphaMarkerScript out gamma
          execution.prefixes.adversary.result configuration.z sourceDigest))
      queryOracle (controllerFromFreshAnswerTape sample.2)
        configuration.verifierLimits .verifier markerRun.oracle
        (List.ofFn before.digest ++ [0, 20] ++
          (0 :: alpha0NonceBytes execution.prefixes.adversary.result)) =
        .ok (boundary.digest, markerNext))
    (markerFinal :
      let sourceRun := sourceMachineRun sample.2
        configuration.verifierLimits .verifier configuration.firstWork
        configuration.secondWork execution.prefixes.adversary.result
        configuration.initialDigest execution.prefixes.adversary.finalState
        (stagedBudget n m)
      let middleFuel := stagedBudget n m - sourceRun.steps
      let markerRun := runMachine (controllerFromFreshAnswerTape sample.2)
        configuration.verifierLimits .verifier middleFuel sourceRun.oracle
        (compileScript (beforeAlphaMarkerScript out gamma
          execution.prefixes.adversary.result configuration.z sourceDigest))
      let markerContinuation := runMachine
        (controllerFromFreshAnswerTape sample.2)
        configuration.verifierLimits .verifier
        (middleFuel - markerRun.steps) markerRun.oracle
        (compileScript (alphaMarkerContinuation out gamma
          execution.prefixes.adversary.result configuration.z before))
      markerContinuation.oracle = markerNext)
    (missing :
      let sourceRun := sourceMachineRun sample.2
        configuration.verifierLimits .verifier configuration.firstWork
        configuration.secondWork execution.prefixes.adversary.result
        configuration.initialDigest execution.prefixes.adversary.finalState
        (stagedBudget n m)
      let middleFuel := stagedBudget n m - sourceRun.steps
      let markerRun := runMachine (controllerFromFreshAnswerTape sample.2)
        configuration.verifierLimits .verifier middleFuel sourceRun.oracle
        (compileScript (beforeAlphaMarkerScript out gamma
          execution.prefixes.adversary.result configuration.z sourceDigest))
      lookupEntry markerRun.oracle
        (List.ofFn before.digest ++ [0, 20] ++
          (0 :: alpha0NonceBytes execution.prefixes.adversary.result)) = none) :
    (List.ofFn before.digest ++ [0, 20] ++
        (0 :: alpha0NonceBytes execution.prefixes.adversary.result),
      boundary.digest) ∈ execution.prefixes.verifier.freshQueries := by
  let sourceRun := sourceMachineRun sample.2 configuration.verifierLimits
    .verifier configuration.firstWork configuration.secondWork
    execution.prefixes.adversary.result configuration.initialDigest
    execution.prefixes.adversary.finalState (stagedBudget n m)
  let middleFuel := stagedBudget n m - sourceRun.steps
  let markerRun := runMachine (controllerFromFreshAnswerTape sample.2)
    configuration.verifierLimits .verifier middleFuel sourceRun.oracle
    (compileScript (beforeAlphaMarkerScript out gamma
      execution.prefixes.adversary.result configuration.z sourceDigest))
  let markerContinuation := runMachine
    (controllerFromFreshAnswerTape sample.2)
    configuration.verifierLimits .verifier
    (middleFuel - markerRun.steps) markerRun.oracle
    (compileScript (alphaMarkerContinuation out gamma
      execution.prefixes.adversary.result configuration.z before))
  let markerInput := List.ofFn before.digest ++ [0, 20] ++
    (0 :: alpha0NonceBytes execution.prefixes.adversary.result)
  have markerQuery' : queryOracle (controllerFromFreshAnswerTape sample.2)
      configuration.verifierLimits .verifier markerRun.oracle markerInput =
      .ok (boundary.digest, markerNext) := by
    simpa only [sourceRun, middleFuel, markerRun, markerInput] using markerQuery
  have missing' : lookupEntry markerRun.oracle markerInput = none := by
    simpa only [sourceRun, middleFuel, markerRun, markerInput] using missing
  have markerHistory := successful_missing_query_appends_fresh_record
    (controllerFromFreshAnswerTape sample.2) configuration.verifierLimits
    .verifier markerRun.oracle markerNext markerInput boundary.digest missing'
    markerQuery'
  have entryToSource := runMachine_entry_history_prefix_final
    (controllerFromFreshAnswerTape sample.2) configuration.verifierLimits
    .verifier (stagedBudget n m) execution.prefixes.adversary.finalState
    (compileScript (sourceThenGammaScript configuration.firstWork
      configuration.secondWork execution.prefixes.adversary.result
      configuration.initialDigest))
  have sourceToMarker := runMachine_entry_history_prefix_final
    (controllerFromFreshAnswerTape sample.2) configuration.verifierLimits
    .verifier middleFuel sourceRun.oracle
    (compileScript (beforeAlphaMarkerScript out gamma
      execution.prefixes.adversary.result configuration.z sourceDigest))
  have entryToMarker : execution.prefixes.adversary.finalState.history <+:
      markerRun.oracle.history := by
    exact entryToSource.trans sourceToMarker
  have remainingEq :
      execution.prefixes.adversary.remaining =
        remainingFreshAnswers sample.2
          execution.prefixes.adversary.finalState := by
    exact (remainingFreshAnswers_eq_adversary_remaining sample.2
      configuration.adversaryLimits .adversary configuration.adversaryFuel
      (configuration.blackBox.start sample.1 configuration.observation)
      execution.prefixes.adversary).symm
  have wholeMachineExact := returned_prefix_is_finite_tape_run_of_available_eq
    execution.prefixes.proverProjectionFacts configuration.verifierLimits
    .verifier (stagedBudget n m)
    (compileScript (wholeStagedScript configuration.firstWork
      configuration.secondWork configuration.z configuration.cuts
      execution.prefixes.adversary.result configuration.initialDigest))
    execution.prefixes.adversary.remaining remainingEq
    execution.prefixes.verifier
  have wholeSuccess :
      (runMachine (controllerFromFreshAnswerTape sample.2)
        configuration.verifierLimits .verifier (stagedBudget n m)
        execution.prefixes.adversary.finalState
        (compileScript (factoredWholeStagedScript configuration.firstWork
          configuration.secondWork configuration.z configuration.cuts
          execution.prefixes.adversary.result
          configuration.initialDigest))).halt =
        .returned (.ok record, finalDigest) := by
    rw [compile_factoredWholeStagedScript_eq_wholeStagedScript]
    rw [wholeMachineExact]
    exact congrArg MachineHalt.returned verifierExact
  have markerToWhole :=
    programmed_marker_successor_history_prefix_factored_whole sample.2
      configuration.verifierLimits .verifier configuration.firstWork
      configuration.secondWork configuration.z configuration.cuts
      execution.prefixes.adversary.result configuration.initialDigest
      execution.prefixes.adversary.finalState
      (projectOracleState execution.prefixes.adversary.finalState)
      (stagedBudget n m) record finalDigest
      (project_state_aligned execution.prefixes.proverProjectionFacts)
      wholeSuccess out gamma sourceDigest boundary preDigest before middle
      middleResultDigest cutWitness
  have markerFinal' : markerContinuation.oracle = markerNext := by
    simpa only [sourceRun, middleFuel, markerRun, markerContinuation] using
      markerFinal
  have markerNextToWhole : markerNext.history <+:
      (runMachine (controllerFromFreshAnswerTape sample.2)
        configuration.verifierLimits .verifier (stagedBudget n m)
        execution.prefixes.adversary.finalState
        (compileScript (factoredWholeStagedScript configuration.firstWork
          configuration.secondWork configuration.z configuration.cuts
          execution.prefixes.adversary.result
          configuration.initialDigest))).oracle.history := by
    rw [← markerFinal']
    simpa only [sourceRun, middleFuel, markerRun, markerContinuation] using
      markerToWhole
  have wholeOracleExact :
      (runMachine (controllerFromFreshAnswerTape sample.2)
        configuration.verifierLimits .verifier (stagedBudget n m)
        execution.prefixes.adversary.finalState
        (compileScript (factoredWholeStagedScript configuration.firstWork
          configuration.secondWork configuration.z configuration.cuts
          execution.prefixes.adversary.result
          configuration.initialDigest))).oracle =
        execution.prefixes.verifier.finalState := by
    rw [compile_factoredWholeStagedScript_eq_wholeStagedScript,
      wholeMachineExact]
  have markerNextToFinal : markerNext.history <+:
      execution.prefixes.verifier.finalState.history := by
    rw [← wholeOracleExact]
    exact markerNextToWhole
  have enumerated := markerFresh_mem_fresh_enumeration_of_history_prefixes
    execution.prefixes.adversary.finalState markerRun.oracle markerNext
    execution.prefixes.verifier.finalState .verifier markerInput
    boundary.digest entryToMarker markerHistory markerNextToFinal
  have enumerationExact :=
    projected_fresh_returned_trace_fresh_query_enumeration_exact
      configuration.verifierLimits .verifier (stagedBudget n m)
      execution.prefixes.adversary.finalState
      (compileScript (wholeStagedScript configuration.firstWork
        configuration.secondWork configuration.z configuration.cuts
        execution.prefixes.adversary.result configuration.initialDigest))
      execution.prefixes.verifier.freshQueries
      execution.prefixes.verifier.result execution.prefixes.verifier.finalState
      execution.prefixes.verifier.steps execution.prefixes.verifier.trace
  rw [enumerationExact] at enumerated
  exact enumerated

#print axioms markerFresh_pair_mem_actual_verifier_freshQueries

end
end AspisV8Completion.FSV8MarkerFreshVerifierMembership
