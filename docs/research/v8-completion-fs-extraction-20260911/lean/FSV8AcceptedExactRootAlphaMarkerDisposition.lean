import FSV8AcceptedExactRootAlphaCutFreshDisposition
import FSV8RootedAlphaFreshDisposition
import FSV8ProgrammedAlphaSourceMarkerTarget
import FSV8ProgrammedAlphaPreMarkerTarget

/-!
# Accepted exact-root alpha routing at the actual marker cut

This leaf consumes the four chronological origins of the first alpha candidate.
For one accepted exact-root execution it retains only three honest alternatives:
an adversary-Q1 input, an operational marker target created earlier by the
verifier, or a genuinely absent candidate input at its sampling cut.

The result is deterministic request-level routing.  The target-event lift and
probability charge remain separate obligations.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 3000

namespace AspisV8Completion.FSV8AcceptedExactRootAlphaMarkerDisposition

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedBodySource
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8V7WholeScriptUniformLaw
open FSV8V7OracleMachineBridge
open FSV8ExactRootCursor
open FSV8ExactRootFunctionalRun
open FSV8ProgrammedAlphaCandidateDisposition
open FSV8ProgrammedAlphaFreshDisposition
open FSV8RootedAlphaFreshDisposition
open FSV8ProgrammedAlphaCutWitness
open FSV8AcceptedExactRootAlphaCutFreshDisposition
open FSV8ExecutablePreAlphaFactorization
open FSV8BeforeAlphaMarkerFactorization
open FSLiveSelectedMiddleQueryRho
open FSV8ProgrammedAlphaSourceMarkerTarget
open FSV8ProgrammedAlphaPreMarkerTarget

noncomputable section

abbrev Block := FSBoundedTranscript.Block

/-- The causal alternatives remaining at the literal alpha marker. -/
inductive AlphaMarkerDisposition
    (root markerState candidateState : OracleState)
    (candidateInput markerInput : ShaInput) (markerAnswer : Digest256) : Prop where
  | priorAdversary
      (record : QueryRecord)
      (member : record ∈ freezeAdversaryQ1 root)
      (inputEq : record.input = candidateInput)
  | markerTarget
      (target : markerAnswer ∈
        operationalRequestTargets ∅ markerState.history markerInput)
  | freshAtCandidate
      (rootAbsent : lookupEntry root candidateInput = none)
      (candidateAbsent : lookupEntry candidateState candidateInput = none)

theorem returned_accepted_exact_root_constructs_alpha_marker_disposition
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
          ∃ boundary : PreAlpha out gamma
            execution.prefixes.adversary.result configuration.z,
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
            let middleFuel := stagedBudget n m - sourceRun.steps
            let preRun := preAlphaMachineRun sample.2
              configuration.verifierLimits .verifier configuration.firstWork
              configuration.secondWork execution.prefixes.adversary.result
              configuration.initialDigest execution.prefixes.adversary.finalState
              (stagedBudget n m) out gamma configuration.z sourceDigest
            let markerRun := runMachine
              (controllerFromFreshAnswerTape sample.2)
              configuration.verifierLimits .verifier middleFuel sourceRun.oracle
              (compileScript (beforeAlphaMarkerScript out gamma
                execution.prefixes.adversary.result configuration.z
                sourceDigest))
            AlphaMarkerDisposition execution.prefixes.adversary.finalState
              markerRun.oracle preRun.oracle
              (List.ofFn boundary.digest ++ [1])
              (List.ofFn before.digest ++ [0, 20] ++
                (0 :: alpha0NonceBytes execution.prefixes.adversary.result))
              boundary.digest := by
  obtain ⟨execution, record, digest, verifierExact, acceptedBody, cut,
      out, gamma, sourceDigest, boundary, preDigest, before, middle,
      middleResultDigest, cutWitness, fresh⟩ :=
    returned_accepted_exact_root_constructs_cut_and_fresh_disposition
      parameters configuration transitionFuel positive sample fallback runtime
      completed accepted acceptedExact
  let sourceRun := sourceMachineRun sample.2 configuration.verifierLimits
    .verifier configuration.firstWork configuration.secondWork
    execution.prefixes.adversary.result configuration.initialDigest
    execution.prefixes.adversary.finalState (stagedBudget n m)
  let middleFuel := stagedBudget n m - sourceRun.steps
  let preRun := preAlphaMachineRun sample.2 configuration.verifierLimits
    .verifier configuration.firstWork configuration.secondWork
    execution.prefixes.adversary.result configuration.initialDigest
    execution.prefixes.adversary.finalState (stagedBudget n m)
    out gamma configuration.z sourceDigest
  let markerRun := runMachine (controllerFromFreshAnswerTape sample.2)
    configuration.verifierLimits .verifier middleFuel sourceRun.oracle
    (compileScript (beforeAlphaMarkerScript out gamma
      execution.prefixes.adversary.result configuration.z sourceDigest))
  have rooted := projected_root_disposition_has_four_cases
    configuration.adversaryLimits configuration.adversaryFuel
    (configuration.blackBox.start sample.1 configuration.observation)
    (freshAnswerTapeToList sample.2) execution.prefixes.adversary
    sourceRun.oracle preRun.oracle .verifier
    (List.ofFn boundary.digest ++ [1])
    (by simpa [sourceRun, preRun] using fresh)
  have routed : AlphaMarkerDisposition
      execution.prefixes.adversary.finalState markerRun.oracle preRun.oracle
      (List.ofFn boundary.digest ++ [1])
      (List.ofFn before.digest ++ [0, 20] ++
        (0 :: alpha0NonceBytes execution.prefixes.adversary.result))
      boundary.digest := by
    cases rooted with
    | priorAdversary prior priorMember inputEq =>
        exact .priorAdversary prior priorMember inputEq
    | introducedDuringSource rootAbsent entry sourceLookup prior priorMember
        actorEq freshOrigin inputEq outputEq entryEq =>
        exact .markerTarget
          (source_creator_hits_actual_marker_request_target sample.2
            configuration.verifierLimits .verifier configuration.firstWork
            configuration.secondWork configuration.z
            execution.prefixes.adversary.result configuration.initialDigest
            execution.prefixes.adversary.finalState
            (projectOracleState execution.prefixes.adversary.finalState)
            (stagedBudget n m) out gamma sourceDigest boundary preDigest before
            middle middleResultDigest cutWitness ∅ prior
            (by simpa [sourceRun] using priorMember) inputEq).2
    | introducedDuringPreAlpha rootAbsent sourceAbsent entry candidateLookup
        prior priorMember actorEq freshOrigin inputEq outputEq entryEq =>
        exact .markerTarget
          (prealpha_inserted_candidate_hits_actual_marker_request_target
            sample.2 configuration.verifierLimits .verifier
            configuration.firstWork configuration.secondWork configuration.z
            execution.prefixes.adversary.result configuration.initialDigest
            execution.prefixes.adversary.finalState
            (projectOracleState execution.prefixes.adversary.finalState)
            (stagedBudget n m) out gamma sourceDigest boundary preDigest before
            middle middleResultDigest cutWitness ∅ entry
            (by simpa [sourceRun] using sourceAbsent)
            (by simpa [preRun] using candidateLookup))
    | freshAtCandidate rootAbsent candidateAbsent =>
        exact .freshAtCandidate rootAbsent candidateAbsent
  exact ⟨execution, record, digest, verifierExact, acceptedBody, out, gamma,
    sourceDigest, boundary, preDigest, before, middle, middleResultDigest,
    cutWitness, by simpa [sourceRun, middleFuel, preRun, markerRun] using routed⟩

#print axioms returned_accepted_exact_root_constructs_alpha_marker_disposition

end
end AspisV8Completion.FSV8AcceptedExactRootAlphaMarkerDisposition
