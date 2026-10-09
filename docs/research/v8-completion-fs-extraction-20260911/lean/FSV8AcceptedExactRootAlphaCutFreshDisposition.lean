import FSV8AcceptedExactRootProgrammedAlphaCut
import FSV8ProgrammedAlphaFreshDisposition
import FSV8ProgrammedAlphaCutWitness

/-!
# One accepted root retains both the alpha cut and fresh disposition

This bridge prevents later target analysis from combining a marker cut from
one execution with an alpha-input disposition from another.  Both facts are
constructed from the same accepted exact-root run, body, post-adversary state,
finite tape and verifier budget.

No target-event inclusion or probability statement is made.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 2600

namespace AspisV8Completion.FSV8AcceptedExactRootAlphaCutFreshDisposition

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ExactCompilerResources
open FSBoundedTranscript
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedBodySource
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8V7WholeScriptUniformLaw
open FSV8V7OracleMachineBridge
open FSV8ExactRootCursor
open FSV8ExactRootFunctionalRun
open FSV8ProgrammedProjectionAlignment
open FSV8AcceptedExactRootProgrammedAlphaCut
open FSV8ProgrammedWholeAlphaCut
open FSV8ProgrammedAlphaCandidateDisposition
open FSV8ProgrammedAlphaFreshDisposition
open FSV8ProgrammedAlphaCutWitness

noncomputable section

abbrev Block := FSBoundedTranscript.Block

theorem returned_accepted_exact_root_constructs_cut_and_fresh_disposition
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
        let cut := ProgrammedAlphaCut
          (tape := extendFreshTape sample.2 fallback) sample.2
          configuration.verifierLimits .verifier
          configuration.firstWork configuration.secondWork configuration.z
          execution.prefixes.adversary.result configuration.initialDigest
          execution.prefixes.adversary.finalState (projectOracleState
            execution.prefixes.adversary.finalState) (stagedBudget n m)
        cut ∧
        ∃ out : FSV7OODBodyScript.Result, ∃ gamma : FSNonzeroQM31.K,
          ∃ sourceDigest : Block,
          ∃ boundary : FSV8ExecutablePreAlphaFactorization.PreAlpha
            out gamma execution.prefixes.adversary.result configuration.z,
          ∃ preDigest, ∃ before, ∃ middle, ∃ middleResultDigest,
            ProgrammedAlphaCutWitness
              (tape := extendFreshTape sample.2 fallback) sample.2
              configuration.verifierLimits .verifier
              configuration.firstWork configuration.secondWork configuration.z
              execution.prefixes.adversary.result configuration.initialDigest
              execution.prefixes.adversary.finalState (projectOracleState
                execution.prefixes.adversary.finalState) (stagedBudget n m)
              out gamma sourceDigest boundary preDigest before middle
              middleResultDigest ∧
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
  obtain ⟨execution, record, digest, verifierExact, acceptedBody, cut⟩ :=
    returned_accepted_exact_root_constructs_programmed_alpha_cut parameters
      configuration transitionFuel positive sample fallback runtime completed
      accepted acceptedExact
  obtain ⟨out, gamma, sourceDigest, boundary, preDigest, before, middle,
      middleResultDigest, cutWitness⟩ :=
    programmed_alpha_cut_constructs_witness configuration.verifierLimits
      .verifier configuration.firstWork configuration.secondWork
      configuration.z execution.prefixes.adversary.result
      configuration.initialDigest execution.prefixes.adversary.finalState
      (projectOracleState execution.prefixes.adversary.finalState)
      (stagedBudget n m) cut
  have fresh := source_runs_construct_fresh_disposition sample.2
    configuration.verifierLimits .verifier configuration.firstWork
    configuration.secondWork configuration.z
    execution.prefixes.adversary.result configuration.initialDigest
    execution.prefixes.adversary.finalState (stagedBudget n m)
    out gamma sourceDigest boundary
  exact ⟨execution, record, digest, verifierExact, acceptedBody, cut,
    out, gamma, sourceDigest, boundary, preDigest, before, middle,
    middleResultDigest, cutWitness, fresh⟩

#print axioms returned_accepted_exact_root_constructs_cut_and_fresh_disposition

end
end AspisV8Completion.FSV8AcceptedExactRootAlphaCutFreshDisposition
