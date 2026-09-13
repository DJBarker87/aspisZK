import FSV8AcceptedExactRootLiveExecution
import FSV8ProgrammedWholeAlphaCut
import FSV8CompiledWholeFactorization

/-!
# Accepted exact root constructs the programmed alpha cut

This is the same-body root-level endpoint for the deterministic alpha prefix.
It starts from the actual exact scheduler root and its acceptance observation,
recovers the verifier machine run from the adversary's literal remaining tape,
rewrites only by the proved compiler factorisation, and constructs the alpha
cut on that same body and projected oracle state.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 2600

namespace AspisV8Completion.FSV8AcceptedExactRootProgrammedAlphaCut

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ExactCompilerResources
open FSBoundedTranscript
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedBodySource
open ExtractionCollectorVerifiedSuccessfulReplay
open ExtractionCollectorOperationalAlphaScheduler
open FSV8V7OracleMachineBridge
open FSV8V7WholeScriptUniformLaw
open FSV8ProgrammedProjectionAlignment
open FSV8ExactRootCursor
open FSV8ExactRootSuccessfulPrefixes
open FSV8ExactRootFunctionalRun
open FSV8AcceptedExactRootLiveExecution
open FSV8CompiledWholeFactorization
open FSV8ExecutableWholeFactorization
open FSV8ProgrammedWholeAlphaCut

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

/-- Actual exact-root acceptance constructs the programmed alpha cut for the
literal adversary-returned body.  No marker state, challenge, or semantic
program is accepted as a premise. -/
theorem returned_accepted_exact_root_constructs_programmed_alpha_cut
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
        SelectedAccepted.mk execution.prefixes.adversary.result record digest =
          accepted ∧
        ProgrammedAlphaCut
          (tape := extendFreshTape sample.2 fallback) sample.2
          configuration.verifierLimits .verifier
          configuration.firstWork configuration.secondWork configuration.z
          execution.prefixes.adversary.result configuration.initialDigest
          execution.prefixes.adversary.finalState
          (projectOracleState execution.prefixes.adversary.finalState)
          (stagedBudget n m) := by
  obtain ⟨execution, record, digest, verifierResultExact, _liveExecution⟩ :=
    returned_accepted_exact_root_constructs_live_execution parameters
      configuration transitionFuel positive sample fallback runtime completed
      accepted acceptedExact
  have remainingEq :
      remainingFreshAnswers sample.2 execution.prefixes.adversary.finalState =
        execution.prefixes.adversary.remaining :=
    remainingFreshAnswers_eq_adversary_remaining sample.2
      configuration.adversaryLimits .adversary configuration.adversaryFuel
      (configuration.blackBox.start sample.1 configuration.observation)
      execution.prefixes.adversary
  have machineExact := returned_prefix_is_finite_tape_run_of_available_eq
    execution.prefixes.proverProjectionFacts configuration.verifierLimits
    .verifier (stagedBudget n m)
    (compileScript (wholeStagedScript configuration.firstWork
      configuration.secondWork configuration.z configuration.cuts
      execution.prefixes.adversary.result configuration.initialDigest))
    execution.prefixes.adversary.remaining remainingEq.symm
    execution.prefixes.verifier
  have wholeReturned :
      (runMachine (controllerFromFreshAnswerTape sample.2)
        configuration.verifierLimits .verifier (stagedBudget n m)
        execution.prefixes.adversary.finalState
        (compileScript (wholeStagedScript configuration.firstWork
          configuration.secondWork configuration.z configuration.cuts
          execution.prefixes.adversary.result
          configuration.initialDigest))).halt =
        .returned (.ok record, digest) := by
    rw [machineExact]
    exact congrArg MachineHalt.returned verifierResultExact
  have factoredReturned :
      (runMachine (controllerFromFreshAnswerTape sample.2)
        configuration.verifierLimits .verifier (stagedBudget n m)
        execution.prefixes.adversary.finalState
        (compileScript (factoredWholeStagedScript configuration.firstWork
          configuration.secondWork configuration.z configuration.cuts
          execution.prefixes.adversary.result
          configuration.initialDigest))).halt =
        .returned (.ok record, digest) := by
    rw [compile_factoredWholeStagedScript_eq_wholeStagedScript]
    exact wholeReturned
  have acceptedValueExact :
      SelectedAccepted.mk execution.prefixes.adversary.result record digest =
        accepted := by
    rw [execution.prefixes.runtimeExact, verifierResultExact] at acceptedExact
    simpa [Runtime.accepted?] using acceptedExact
  have alignedEntry := project_state_aligned
    execution.prefixes.proverProjectionFacts
  have cut := returned_factoredWhole_constructs_programmed_alpha_cut
    configuration.verifierLimits .verifier configuration.firstWork
    configuration.secondWork configuration.z configuration.cuts
    execution.prefixes.adversary.result configuration.initialDigest
    execution.prefixes.adversary.finalState
    (projectOracleState execution.prefixes.adversary.finalState)
    (stagedBudget n m) record digest alignedEntry factoredReturned
  exact ⟨execution, record, digest, verifierResultExact, acceptedValueExact, cut⟩

#print axioms returned_accepted_exact_root_constructs_programmed_alpha_cut

end
end AspisV8Completion.FSV8AcceptedExactRootProgrammedAlphaCut
