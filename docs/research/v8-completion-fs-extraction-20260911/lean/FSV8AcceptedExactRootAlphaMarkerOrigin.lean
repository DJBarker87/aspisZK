import FSV8AcceptedExactRootAlphaMarkerDisposition
import FSV8ProgrammedAlphaMarkerQuery

/-!
# Accepted exact-root alpha marker origin

This leaf refines the request-level marker disposition by inspecting the
literal successful marker query.  A marker target is split into a genuinely
fresh marker exposure and a cached marker replay.  The cached case is retained
as a separate obligation: target membership at a cached replay is not a
first-exposure target event.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 3000

namespace AspisV8Completion.FSV8AcceptedExactRootAlphaMarkerOrigin

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
open FSV8ProgrammedAlphaCutWitness
open FSV8ExecutablePreAlphaFactorization
open FSV8BeforeAlphaMarkerFactorization
open FSLiveSelectedMiddleQueryRho
open FSV8AcceptedExactRootAlphaMarkerDisposition
open FSV8ProgrammedAlphaMarkerQuery

noncomputable section

abbrev Block := FSBoundedTranscript.Block

/-- Causal alternatives after inspecting the actual marker lookup boundary.
The target predicate is intentionally retained in the cached case rather than
promoted to a causal first-exposure event. -/
inductive AlphaMarkerOriginDisposition
    (root markerState candidateState : OracleState)
    (candidateInput markerInput : ShaInput) (markerAnswer : Digest256) : Prop where
  | priorAdversary
      (record : QueryRecord)
      (member : record ∈ freezeAdversaryQ1 root)
      (inputEq : record.input = candidateInput)
  | markerFresh
      (target : markerAnswer ∈
        operationalRequestTargets ∅ markerState.history markerInput)
      (missing : lookupEntry markerState markerInput = none)
  | markerCached
      (target : markerAnswer ∈
        operationalRequestTargets ∅ markerState.history markerInput)
      (entry : TableEntry)
      (found : lookupEntry markerState markerInput = some entry)
      (outputExact : entry.output = markerAnswer)
  | freshAtCandidate
      (rootAbsent : lookupEntry root candidateInput = none)
      (candidateAbsent : lookupEntry candidateState candidateInput = none)

/-- The answer of a successful cached call is the answer stored at the
pre-query lookup.  This retains the value equality needed to trace the marker
back to its actual first producer. -/
theorem successful_cached_query_output_eq
    (controller : AdaptiveController) (limits : OracleLimits)
    (actor : QueryActor) (state nextState : OracleState)
    (input : ShaInput) (entry : TableEntry) (output : ShaOutput)
    (found : lookupEntry state input = some entry)
    (success : queryOracle controller limits actor state input =
      .ok (output, nextState)) :
    entry.output = output := by
  unfold queryOracle at success
  split at success <;> try contradiction
  next _ =>
    rw [found] at success
    exact (Prod.mk.inj (Except.ok.inj success)).1

/-- One accepted exact-root execution constructs the literal successful marker
query and a four-way marker-origin classification.  In particular, the
cached-marker branch is not hidden inside a probability-chargeable target
event. -/
theorem returned_accepted_exact_root_constructs_alpha_marker_origin
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
            ∃ markerNext,
              queryOracle (controllerFromFreshAnswerTape sample.2)
                configuration.verifierLimits .verifier markerRun.oracle
                (List.ofFn before.digest ++ [0, 20] ++
                  (0 :: alpha0NonceBytes execution.prefixes.adversary.result)) =
                .ok (boundary.digest, markerNext) ∧
              AlphaMarkerOriginDisposition
                execution.prefixes.adversary.finalState markerRun.oracle
                preRun.oracle (List.ofFn boundary.digest ++ [1])
                (List.ofFn before.digest ++ [0, 20] ++
                  (0 :: alpha0NonceBytes execution.prefixes.adversary.result))
                boundary.digest := by
  obtain ⟨execution, record, digest, verifierExact, acceptedBody, out, gamma,
      sourceDigest, boundary, preDigest, before, middle, middleResultDigest,
      cutWitness, routed⟩ :=
    returned_accepted_exact_root_constructs_alpha_marker_disposition
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
  let markerContinuation := runMachine
    (controllerFromFreshAnswerTape sample.2) configuration.verifierLimits
    .verifier (middleFuel - markerRun.steps) markerRun.oracle
    (compileScript (alphaMarkerContinuation out gamma
      execution.prefixes.adversary.result configuration.z before))
  have cutCopy := cutWitness
  unfold ProgrammedAlphaCutWitness at cutCopy
  rcases cutCopy with
    ⟨_sourceReturned, _sourceFunctional, _preReturned, _markerReturned,
      markerContinuationReturned, _postAlphaReturned, _markerFunctional,
      _markerAligned, _markerContinuationFunctional,
      _afterMarkerAligned⟩
  have markerContinuationReturned' :
      markerContinuation.halt = .returned (.ok boundary, preDigest) := by
    simpa only [markerContinuation, markerRun, middleFuel, sourceRun,
      sourceMachineRun] using markerContinuationReturned
  obtain ⟨markerNext, markerQuery, _markerFinal⟩ :=
    returned_marker_continuation_exposes_query sample.2
      configuration.verifierLimits .verifier out gamma
      execution.prefixes.adversary.result configuration.z boundary preDigest
      before (middleFuel - markerRun.steps) markerRun.oracle
      markerContinuationReturned'
  have refined : AlphaMarkerOriginDisposition
      execution.prefixes.adversary.finalState markerRun.oracle preRun.oracle
      (List.ofFn boundary.digest ++ [1])
      (List.ofFn before.digest ++ [0, 20] ++
        (0 :: alpha0NonceBytes execution.prefixes.adversary.result))
      boundary.digest := by
    cases routed with
    | priorAdversary prior priorMember inputEq =>
        exact .priorAdversary prior priorMember inputEq
    | markerTarget target =>
        cases found : lookupEntry markerRun.oracle
            (List.ofFn before.digest ++ [0, 20] ++
              (0 :: alpha0NonceBytes
                execution.prefixes.adversary.result)) with
        | none => exact .markerFresh target found
        | some entry =>
            exact .markerCached target entry found
              (successful_cached_query_output_eq
                (controllerFromFreshAnswerTape sample.2)
                configuration.verifierLimits .verifier markerRun.oracle
                markerNext
                (List.ofFn before.digest ++ [0, 20] ++
                  (0 :: alpha0NonceBytes
                    execution.prefixes.adversary.result))
                entry boundary.digest found markerQuery)
    | freshAtCandidate rootAbsent candidateAbsent =>
        exact .freshAtCandidate rootAbsent candidateAbsent
  refine ⟨execution, record, digest, verifierExact, acceptedBody, out, gamma,
    sourceDigest, boundary, preDigest, before, middle, middleResultDigest,
    cutWitness, ?_⟩
  dsimp only
  exact ⟨markerNext, markerQuery, refined⟩

#print axioms returned_accepted_exact_root_constructs_alpha_marker_origin
#print axioms successful_cached_query_output_eq

end
end AspisV8Completion.FSV8AcceptedExactRootAlphaMarkerOrigin
