import FSV8AcceptedExactRootProgrammedAlphaCut
import FSV8ProgrammedAlphaCandidateDisposition

/-!
# Accepted exact root constructs the programmed alpha candidate disposition

This root-level corollary combines the exact-root programmed alpha cut with
the candidate-disposition leaf, retaining the literal adversary-returned body,
projected state, and root fuel.  It makes no additional assumption and claims
no probability or extraction statement.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 2600

namespace AspisV8Completion.FSV8AcceptedExactRootProgrammedAlphaCandidateDisposition

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ExactCompilerResources
open FSBoundedTranscript
open FSV8V7WholeScriptUniformLaw
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedBodySource
open ExtractionCollectorVerifiedSuccessfulReplay
open ExtractionCollectorOperationalAlphaScheduler
open FSV8V7OracleMachineBridge
open FSV8ExactRootCursor
open FSV8ExactRootSuccessfulPrefixes
open FSV8ExactRootFunctionalRun
open FSV8AcceptedExactRootLiveExecution
open FSV8AcceptedExactRootProgrammedAlphaCut
open FSV8ProgrammedAlphaCandidateDisposition

noncomputable section

abbrev Block := FSBoundedTranscript.Block

theorem returned_accepted_exact_root_constructs_programmed_alpha_candidate_disposition
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
        ProgrammedAlphaCandidateDisposition
          (finiteTape := sample.2)
          configuration.verifierLimits .verifier
          configuration.firstWork configuration.secondWork configuration.z
          execution.prefixes.adversary.result configuration.initialDigest
          execution.prefixes.adversary.finalState
          (stagedBudget n m) := by
  obtain ⟨execution, record, digest, verifierResultExact,
      acceptedValueExact, cut⟩ :=
    returned_accepted_exact_root_constructs_programmed_alpha_cut parameters
      configuration transitionFuel positive sample fallback runtime completed
      accepted acceptedExact
  have disposition := programmed_alpha_cut_constructs_candidate_disposition
    (tape := extendFreshTape sample.2 fallback)
    (finiteTape := sample.2) configuration.verifierLimits .verifier
    configuration.firstWork configuration.secondWork configuration.z
    execution.prefixes.adversary.result configuration.initialDigest
    execution.prefixes.adversary.finalState
    (projectOracleState execution.prefixes.adversary.finalState)
    (stagedBudget n m)
    cut
  exact ⟨execution, record, digest, verifierResultExact, acceptedValueExact,
    disposition⟩

#print axioms returned_accepted_exact_root_constructs_programmed_alpha_candidate_disposition

end
end AspisV8Completion.FSV8AcceptedExactRootProgrammedAlphaCandidateDisposition
