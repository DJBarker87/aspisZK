import FSV8ExactRootFunctionalRun
import FSV8SuccessfulWholeLiveAlpha

/-!
# Accepted exact root constructs the live functional execution

Normal scheduler return alone retains ordinary verifier rejection.  This
leaf adds the actual `Runtime.accepted?` observation and consequently obtains
the successful whole-script record needed by the existing live-challenge
decomposition.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000
set_option maxRecDepth 1800

namespace AspisV8Completion.FSV8AcceptedExactRootLiveExecution

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ExactCompilerResources
open FSBoundedTranscript
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedBodySource
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8V7OracleMachineBridge
open FSV8V7WholeScriptUniformLaw
open FSV8ExactRootCursor
open FSV8ExactRootSuccessfulPrefixes
open FSV8ExactRootFunctionalRun
open FSV8SuccessfulWholeLiveAlpha

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

/-- An accepted exact-root run produces the concrete accepted record and the
existing causal live-alpha execution for its own adversary-returned body. -/
theorem returned_accepted_exact_root_constructs_live_execution
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
        .returned runtime)
    (accepted : SelectedAccepted configuration.z)
    (acceptedExact : runtime.accepted? = some accepted) :
    ∃ execution : ExactRootFunctionalRun configuration sample.1 sample.2
        fallback runtime,
      ∃ record digest,
        execution.prefixes.verifier.result = (.ok record, digest) ∧
        WholeLiveAlphaExecution configuration.firstWork configuration.secondWork
          configuration.z configuration.cuts
          execution.prefixes.adversary.result configuration.initialDigest
          (extendFreshTape sample.2 fallback)
          (projectOracleState execution.prefixes.adversary.finalState)
          record digest := by
  obtain ⟨execution⟩ := returned_exact_root_constructs_functional_run
    parameters configuration transitionFuel positive sample fallback runtime
      completed
  rw [execution.prefixes.runtimeExact] at acceptedExact
  cases runtimeOutput : execution.prefixes.verifier.result with
  | mk outcome digest =>
      cases outcome with
      | error error =>
          simp [Runtime.accepted?, runtimeOutput] at acceptedExact
      | ok record =>
          have verifierResultExact :
              execution.prefixes.verifier.result = (.ok record, digest) := by
            exact runtimeOutput
          have functionalSuccess :
              (FSOracleExecution.run (extendFreshTape sample.2 fallback)
                (wholeStagedScript configuration.firstWork
                  configuration.secondWork configuration.z configuration.cuts
                  execution.prefixes.adversary.result
                  configuration.initialDigest)
                (projectOracleState
                  execution.prefixes.adversary.finalState)).1 =
                some (.ok record, digest) := by
            rw [execution.functionalResult, verifierResultExact]
          exact ⟨execution, record, digest, verifierResultExact,
            successful_whole_constructs_live_alpha configuration.firstWork
              configuration.secondWork configuration.z configuration.cuts
              execution.prefixes.adversary.result configuration.initialDigest
              (extendFreshTape sample.2 fallback)
              (projectOracleState execution.prefixes.adversary.finalState)
              record digest functionalSuccess⟩

#print axioms returned_accepted_exact_root_constructs_live_execution

end
end AspisV8Completion.FSV8AcceptedExactRootLiveExecution
