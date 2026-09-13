import FSV8AcceptedExactRootAlphaPrefixInsertionProvenance
import FSV8RootedAlphaFreshDisposition

/-!
# Accepted exact root constructs fresh alpha insertion provenance

This lifts the fresh-source disposition to the same accepted exact-root run.
The returned body, post-adversary root, source and pre-alpha states are all
those constructed by that run.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 450000

namespace AspisV8Completion.FSV8AcceptedExactRootAlphaFreshDisposition

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73OperationalOracleExposure
open FSBoundedTranscript
open FSV8V7WholeScriptUniformLaw
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedBodySource
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8ExactRootCursor
open FSV8ExactRootFunctionalRun
open FSV8AcceptedExactRootLiveExecution
open FSV8ProgrammedAlphaCandidateDisposition
open FSV8AcceptedExactRootAlphaPrefixInsertionProvenance
open FSV8ProgrammedAlphaFreshDisposition
open FSV8RootedAlphaFreshDisposition

noncomputable section

abbrev Block := FSBoundedTranscript.Block

theorem returned_accepted_exact_root_constructs_fresh_alpha_disposition
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
          ∃ boundary : FSV8ExecutablePreAlphaFactorization.PreAlpha
            out gamma execution.prefixes.adversary.result configuration.z,
            let sourceRun := sourceMachineRun sample.2
              configuration.verifierLimits .verifier configuration.firstWork
              configuration.secondWork execution.prefixes.adversary.result
              configuration.initialDigest execution.prefixes.adversary.finalState
              (stagedBudget n m)
            let preRun := preAlphaMachineRun sample.2
              configuration.verifierLimits .verifier configuration.firstWork
              configuration.secondWork execution.prefixes.adversary.result
              configuration.initialDigest execution.prefixes.adversary.finalState
              (stagedBudget n m) out gamma configuration.z sourceDigest
            FreshCausalAlphaDisposition execution.prefixes.adversary.finalState
              sourceRun.oracle preRun.oracle .verifier
              (List.ofFn boundary.digest ++ [1]) := by
  obtain ⟨execution, record, digest, verifierExact, acceptedBody,
      out, gamma, sourceDigest, boundary, strong⟩ :=
    returned_accepted_exact_root_constructs_strong_alpha_disposition parameters
      configuration transitionFuel positive sample fallback runtime completed
      accepted acceptedExact
  have fresh := strong_disposition_constructs_fresh_disposition sample.2
    configuration.verifierLimits .verifier configuration.firstWork
    configuration.secondWork configuration.z
    execution.prefixes.adversary.result configuration.initialDigest
    execution.prefixes.adversary.finalState (stagedBudget n m)
    out gamma sourceDigest boundary strong
  exact ⟨execution, record, digest, verifierExact, acceptedBody,
    out, gamma, sourceDigest, boundary, fresh⟩

#print axioms returned_accepted_exact_root_constructs_fresh_alpha_disposition

/-- At the actual projected post-adversary root, the `priorTarget` alternative
is impossible: every root-table entry has a literal adversary Q1 creator.
Thus an accepted run constructs four deterministic causal origin cases intended
for subsequent probability analysis.  This theorem does not itself identify
measurable events or assign probability mass to the cases. -/
theorem returned_accepted_exact_root_constructs_rooted_alpha_disposition
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
          ∃ boundary : FSV8ExecutablePreAlphaFactorization.PreAlpha
            out gamma execution.prefixes.adversary.result configuration.z,
            let sourceRun := sourceMachineRun sample.2
              configuration.verifierLimits .verifier configuration.firstWork
              configuration.secondWork execution.prefixes.adversary.result
              configuration.initialDigest execution.prefixes.adversary.finalState
              (stagedBudget n m)
            let preRun := preAlphaMachineRun sample.2
              configuration.verifierLimits .verifier configuration.firstWork
              configuration.secondWork execution.prefixes.adversary.result
              configuration.initialDigest execution.prefixes.adversary.finalState
              (stagedBudget n m) out gamma configuration.z sourceDigest
            RootedFreshAlphaDisposition execution.prefixes.adversary.finalState
              sourceRun.oracle preRun.oracle .verifier
              (List.ofFn boundary.digest ++ [1]) := by
  obtain ⟨execution, record, digest, verifierExact, acceptedBody,
      out, gamma, sourceDigest, boundary, fresh⟩ :=
    returned_accepted_exact_root_constructs_fresh_alpha_disposition parameters
      configuration transitionFuel positive sample fallback runtime completed
      accepted acceptedExact
  let sourceRun := sourceMachineRun sample.2 configuration.verifierLimits
    .verifier configuration.firstWork configuration.secondWork
    execution.prefixes.adversary.result configuration.initialDigest
    execution.prefixes.adversary.finalState (stagedBudget n m)
  let preRun := preAlphaMachineRun sample.2 configuration.verifierLimits
    .verifier configuration.firstWork configuration.secondWork
    execution.prefixes.adversary.result configuration.initialDigest
    execution.prefixes.adversary.finalState (stagedBudget n m)
    out gamma configuration.z sourceDigest
  have rooted := projected_root_disposition_has_four_cases
    configuration.adversaryLimits configuration.adversaryFuel
    (configuration.blackBox.start sample.1 configuration.observation)
    (freshAnswerTapeToList sample.2) execution.prefixes.adversary
    sourceRun.oracle preRun.oracle .verifier
    (List.ofFn boundary.digest ++ [1]) fresh
  exact ⟨execution, record, digest, verifierExact, acceptedBody,
    out, gamma, sourceDigest, boundary, rooted⟩

#print axioms returned_accepted_exact_root_constructs_rooted_alpha_disposition

end
end AspisV8Completion.FSV8AcceptedExactRootAlphaFreshDisposition
