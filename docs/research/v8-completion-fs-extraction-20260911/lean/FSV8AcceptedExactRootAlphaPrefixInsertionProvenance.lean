import FSV8AcceptedExactRootProgrammedAlphaCandidateDisposition
import FSV8ProgrammedAlphaPrefixInsertionProvenance

/-!
# Accepted exact root constructs alpha prefix-insertion provenance

This leaf lifts the five-way, record-carrying alpha disposition to the exact
accepted root.  The body, post-adversary root state, finite answer tape and
verifier actor remain those constructed by the same accepted execution.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000

namespace AspisV8Completion.FSV8AcceptedExactRootAlphaPrefixInsertionProvenance

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
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
open FSV8AcceptedExactRootProgrammedAlphaCandidateDisposition
open FSV8ProgrammedAlphaCandidateDisposition
open FSV8ProgrammedAlphaPrefixInsertionProvenance

noncomputable section

abbrev Block := FSBoundedTranscript.Block

theorem returned_accepted_exact_root_constructs_strong_alpha_disposition
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
        ∃ out : FSV7OODBodyScript.Result, ∃ gamma : FSNonzeroQM31.K,
          ∃ sourceDigest : Block,
            ∃ boundary : FSV8ExecutablePreAlphaFactorization.PreAlpha out
              gamma execution.prefixes.adversary.result configuration.z,
              let sourceRun := sourceMachineRun sample.2
                configuration.verifierLimits .verifier configuration.firstWork
                configuration.secondWork execution.prefixes.adversary.result
                configuration.initialDigest
                execution.prefixes.adversary.finalState (stagedBudget n m)
              let preRun := preAlphaMachineRun sample.2
                configuration.verifierLimits .verifier configuration.firstWork
                configuration.secondWork execution.prefixes.adversary.result
                configuration.initialDigest
                execution.prefixes.adversary.finalState (stagedBudget n m) out
                gamma configuration.z sourceDigest
              StrongCausalAlphaDisposition
                execution.prefixes.adversary.finalState sourceRun.oracle
                preRun.oracle .verifier
                (List.ofFn boundary.digest ++ [1]) := by
  obtain ⟨execution, record, digest, verifierResultExact,
      acceptedValueExact, programmed⟩ :=
    returned_accepted_exact_root_constructs_programmed_alpha_candidate_disposition
      parameters configuration transitionFuel positive sample fallback runtime
      completed accepted acceptedExact
  obtain ⟨out, gamma, sourceDigest, boundary, strong⟩ :=
    programmed_candidate_constructs_strong_disposition sample.2
      configuration.verifierLimits .verifier configuration.firstWork
      configuration.secondWork configuration.z
      execution.prefixes.adversary.result configuration.initialDigest
      execution.prefixes.adversary.finalState (stagedBudget n m) programmed
  exact ⟨execution, record, digest, verifierResultExact, acceptedValueExact,
    out, gamma, sourceDigest, boundary, strong⟩

#print axioms returned_accepted_exact_root_constructs_strong_alpha_disposition

end
end AspisV8Completion.FSV8AcceptedExactRootAlphaPrefixInsertionProvenance
