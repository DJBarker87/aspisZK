import FSV8AcceptedExactRootAlphaCutFreshDisposition
import FSV8MarkerFreshVerifierCut
import FSV8MarkerFreshCreatorTargetEvent
import FSV8PreAlphaMarkerCreator
import FSV8ProgrammedAlphaSourceMarkerTarget
import FSV8ProgrammedAlphaPreMarkerTarget
import FSV8AcceptedExactRootAlphaMarkerOrigin

/-!
# Accepted V8 alpha marker routed to the exact-root target event

This source-specific wrapper retains the concrete fresh verifier creator in
the two pre-marker insertion cases.  A genuinely fresh marker is charged to
the existing exact-root target event.  Cached marker reuse, an adversary-Q1
candidate, and a genuinely absent candidate remain explicit alternatives.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option maxRecDepth 3200

namespace AspisV8Completion.FSV8AcceptedExactRootAlphaMarkerTargetEvent

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73ProjectedFreshController
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalCausalInjection
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73VerifierOracleStability
open AspisK1.V7Tag73CausalProgrammingFreshness
open FSAuthenticatedInterleavedPrefixMiddle
open ExtractionCollectorVerifiedBodySource
open ExtractionCollectorVerifiedSuccessfulReplay
open FSV8V7WholeScriptUniformLaw
open FSV8V7OracleMachineBridge
open FSV8ExactRootCursor
open FSV8ExactRootFunctionalRun
open FSV8PostOODGammaScript
open FSV8ProgrammedAlphaCandidateDisposition
open FSV8ProgrammedAlphaFreshDisposition
open FSV8RootedAlphaFreshDisposition
open FSV8ProgrammedAlphaCutWitness
open FSV8AcceptedExactRootAlphaCutFreshDisposition
open FSV8ExecutablePreAlphaFactorization
open FSV8BeforeAlphaMarkerFactorization
open FSLiveSelectedMiddleQueryRho
open FSV8ProgrammedAlphaMarkerQuery
open FSV8ReturnedBindKnownPrefix
open FSV8ProgrammedAlphaSourceMarkerTarget
open FSV8ProgrammedAlphaPreMarkerTarget
open FSV8AlphaMarkerPriorCreatorTarget
open FSV8MarkerFreshVerifierQueryBridge
open FSV8MarkerFreshVerifierCut
open FSV8MarkerFreshCreatorTargetEvent
open FSV8PreAlphaMarkerCreator
open FSV8AcceptedExactRootAlphaMarkerOrigin

noncomputable section

abbrev Block := FSBoundedTranscript.Block

inductive AlphaMarkerTargetEventDisposition
    (root candidateState : OracleState) (candidateInput : ShaInput)
    (markerTargetEvent : Prop) : Prop where
  | priorAdversary
      (record : QueryRecord)
      (member : record ∈ freezeAdversaryQ1 root)
      (inputEq : record.input = candidateInput)
  | freshMarkerTargetEvent (event : markerTargetEvent)
  | markerCachedFreshSource
      (markerState : OracleState) (markerInput : ShaInput)
      (markerAnswer : Digest256)
      (target : markerAnswer ∈
        operationalRequestTargets ∅ markerState.history markerInput)
      (entry : TableEntry)
      (found : lookupEntry markerState markerInput = some entry)
      (sourceExact : entry.source = .fresh)
      (outputExact : entry.output = markerAnswer)
  | markerCachedProgrammedSource
      (markerState : OracleState) (markerInput : ShaInput)
      (markerAnswer : Digest256)
      (target : markerAnswer ∈
        operationalRequestTargets ∅ markerState.history markerInput)
      (entry : TableEntry)
      (found : lookupEntry markerState markerInput = some entry)
      (sourceExact : entry.source = .programmed)
      (outputExact : entry.output = markerAnswer)
  | freshAtCandidate
      (rootAbsent : lookupEntry root candidateInput = none)
      (candidateAbsent : lookupEntry candidateState candidateInput = none)

theorem returned_accepted_exact_root_routes_alpha_marker_target_event
    {HiddenTape TapeIdentity Observation : Type}
    (parameters : ExactCompilerResourceParameters)
    {n m : Nat}
    (configuration : Configuration HiddenTape TapeIdentity Observation
      (globalFull256OracleCallCap parameters) n m)
    (transitionFuel : Nat) (transitionRoom : 2 ≤ transitionFuel)
    (sample : ExactCompilerSample HiddenTape parameters)
    (fallback : Block) (imensionalRuntime : Runtime TapeIdentity configuration.z)
    (completed :
      (runExactRoot parameters configuration transitionFuel sample).terminal =
        .returned imensionalRuntime)
    (accepted : SelectedAccepted configuration.z)
    (acceptedExact : imensionalRuntime.accepted? = some accepted) :
    ∃ execution : ExactRootFunctionalRun configuration sample.1 sample.2
        fallback imensionalRuntime,
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
              execution.prefixes.adversary.finalState
              (projectOracleState execution.prefixes.adversary.finalState)
              (stagedBudget n m) out gamma sourceDigest boundary preDigest before
              middle middleResultDigest ∧
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
            AlphaMarkerTargetEventDisposition
              execution.prefixes.adversary.finalState preRun.oracle
              (List.ofFn boundary.digest ++ [1])
              (sample ∈ targetEvent parameters configuration transitionFuel) := by
  obtain ⟨execution, record, digest, verifierExact, acceptedBody, _cut,
      out, gamma, sourceDigest, boundary, preDigest, before, middle,
      middleResultDigest, cutWitness, fresh⟩ :=
    returned_accepted_exact_root_constructs_cut_and_fresh_disposition
      parameters configuration transitionFuel (by omega) sample fallback
      imensionalRuntime completed accepted acceptedExact
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
  let markerInput := List.ofFn before.digest ++ [0, 20] ++
    (0 :: alpha0NonceBytes execution.prefixes.adversary.result)
  have rooted := projected_root_disposition_has_four_cases
    configuration.adversaryLimits configuration.adversaryFuel
    (configuration.blackBox.start sample.1 configuration.observation)
    (freshAnswerTapeToList sample.2) execution.prefixes.adversary
    sourceRun.oracle preRun.oracle .verifier
    (List.ofFn boundary.digest ++ [1]) (by
      simpa [sourceRun, preRun] using fresh)
  have cutCopy := cutWitness
  unfold ProgrammedAlphaCutWitness at cutCopy
  rcases cutCopy with
    ⟨_sourceReturned, _sourceFunctional, _preReturned, _markerReturned,
      markerContinuationReturned, _postAlphaReturned, _markerFunctional,
      _markerAligned, _markerContinuationFunctional, _afterMarkerAligned⟩
  have markerContinuationReturned' :
      markerContinuation.halt = .returned (.ok boundary, preDigest) := by
    simpa only [markerContinuation, markerRun, middleFuel, sourceRun,
      sourceMachineRun] using markerContinuationReturned
  obtain ⟨markerNext, markerQuery, markerFinal⟩ :=
    returned_marker_continuation_exposes_query sample.2
      configuration.verifierLimits .verifier out gamma
      execution.prefixes.adversary.result configuration.z boundary preDigest
      before (middleFuel - markerRun.steps) markerRun.oracle
      markerContinuationReturned'
  have routeCreator
      (creator : QueryRecord) (creatorMember : creator ∈ markerRun.oracle.history)
      (creatorActor : creator.actor = .verifier)
      (creatorFresh : creator.origin = .fresh)
      (creatorInput : creator.input = List.ofFn boundary.digest ++ [1])
      (missing : lookupEntry markerRun.oracle markerInput = none) :
      sample ∈ targetEvent parameters configuration transitionFuel := by
    have cut := markerFresh_constructs_actual_verifier_cut parameters
      configuration sample fallback imensionalRuntime execution record digest
      verifierExact out gamma sourceDigest boundary preDigest before middle
      middleResultDigest cutWitness markerNext (by
        simpa only [sourceRun, middleFuel, markerRun, markerInput] using markerQuery)
      (by simpa only [sourceRun, middleFuel, markerRun, markerContinuation] using
        markerFinal) (by simpa only [sourceRun, middleFuel, markerRun,
          markerInput] using missing)
    apply returned_fresh_marker_prior_fresh_creator_mem_root_target_event
      parameters configuration transitionFuel transitionRoom sample fallback
      imensionalRuntime execution markerRun.oracle markerNext markerInput
      boundary.digest cut.entryPrefix cut.markerHistory cut.finalPrefix creator
      creatorMember creatorActor creatorFresh
    rw [creatorInput]
    exact literal_squeeze_input_has_state_prefix boundary.digest 1
  have routed : AlphaMarkerTargetEventDisposition
      execution.prefixes.adversary.finalState preRun.oracle
      (List.ofFn boundary.digest ++ [1])
      (sample ∈ targetEvent parameters configuration transitionFuel) := by
    cases rooted with
    | priorAdversary prior priorMember inputEq =>
        exact .priorAdversary prior priorMember inputEq
    | freshAtCandidate rootAbsent candidateAbsent =>
        exact .freshAtCandidate rootAbsent candidateAbsent
    | introducedDuringSource rootAbsent entry sourceLookup creator creatorMember
        actorEq freshOrigin inputEq outputEq entryEq =>
        have target := (source_creator_hits_actual_marker_request_target sample.2
          configuration.verifierLimits .verifier configuration.firstWork
          configuration.secondWork configuration.z
          execution.prefixes.adversary.result configuration.initialDigest
          execution.prefixes.adversary.finalState
          (projectOracleState execution.prefixes.adversary.finalState)
          (stagedBudget n m) out gamma sourceDigest boundary preDigest before
          middle middleResultDigest cutWitness ∅ creator
          (by simpa [sourceRun] using creatorMember) inputEq).2
        cases found : lookupEntry markerRun.oracle markerInput with
        | some cached =>
            have outputExact := successful_cached_query_output_eq
              (controllerFromFreshAnswerTape sample.2)
              configuration.verifierLimits .verifier markerRun.oracle
              markerNext markerInput cached boundary.digest found
              (by simpa [markerInput] using markerQuery)
            cases sourceEq : cached.source with
            | fresh => exact .markerCachedFreshSource markerRun.oracle
                markerInput boundary.digest target cached found sourceEq
                outputExact
            | programmed => exact .markerCachedProgrammedSource markerRun.oracle
                markerInput boundary.digest target cached found sourceEq
                outputExact
        | none =>
            have rootToSource := runMachine_entry_history_prefix_final
              (controllerFromFreshAnswerTape sample.2)
              configuration.verifierLimits .verifier (stagedBudget n m)
              execution.prefixes.adversary.finalState
              (compileScript (sourceThenGammaScript configuration.firstWork
                configuration.secondWork execution.prefixes.adversary.result
                configuration.initialDigest))
            have sourceToMarker := runMachine_entry_history_prefix_final
              (controllerFromFreshAnswerTape sample.2)
              configuration.verifierLimits .verifier middleFuel sourceRun.oracle
              (compileScript (beforeAlphaMarkerScript out gamma
                execution.prefixes.adversary.result configuration.z sourceDigest))
            have creatorAtMarker := history_since_member_survives_prefix
              execution.prefixes.adversary.finalState sourceRun.oracle
              markerRun.oracle creator rootToSource sourceToMarker
              (by simpa [sourceRun] using creatorMember)
            exact .freshMarkerTargetEvent
              (routeCreator creator creatorAtMarker actorEq freshOrigin inputEq
                found)
    | introducedDuringPreAlpha rootAbsent sourceAbsent entry candidateLookup
        _creator _creatorMember _actorEq _freshOrigin _inputEq _outputEq
        _entryEq =>
        have target := prealpha_inserted_candidate_hits_actual_marker_request_target
          sample.2 configuration.verifierLimits .verifier
          configuration.firstWork configuration.secondWork configuration.z
          execution.prefixes.adversary.result configuration.initialDigest
          execution.prefixes.adversary.finalState
          (projectOracleState execution.prefixes.adversary.finalState)
          (stagedBudget n m) out gamma sourceDigest boundary preDigest before
          middle middleResultDigest cutWitness ∅ entry
          (by simpa [sourceRun] using sourceAbsent)
          (by simpa [preRun] using candidateLookup)
        cases found : lookupEntry markerRun.oracle markerInput with
        | some cached =>
            have outputExact := successful_cached_query_output_eq
              (controllerFromFreshAnswerTape sample.2)
              configuration.verifierLimits .verifier markerRun.oracle
              markerNext markerInput cached boundary.digest found
              (by simpa [markerInput] using markerQuery)
            cases sourceEq : cached.source with
            | fresh => exact .markerCachedFreshSource markerRun.oracle
                markerInput boundary.digest target cached found sourceEq
                outputExact
            | programmed => exact .markerCachedProgrammedSource markerRun.oracle
                markerInput boundary.digest target cached found sourceEq
                outputExact
        | none =>
            obtain ⟨creator, creatorMember, actorEq, freshOrigin, inputEq⟩ :=
              prealpha_inserted_candidate_has_before_marker_fresh_creator
                sample.2 configuration.verifierLimits .verifier
                configuration.firstWork configuration.secondWork configuration.z
                execution.prefixes.adversary.result configuration.initialDigest
                execution.prefixes.adversary.finalState
                (projectOracleState execution.prefixes.adversary.finalState)
                (stagedBudget n m) out gamma sourceDigest boundary preDigest
                before middle middleResultDigest cutWitness entry
                (by simpa [sourceRun] using sourceAbsent)
                (by simpa [preRun] using candidateLookup)
            have sourceToMarker := runMachine_entry_history_prefix_final
              (controllerFromFreshAnswerTape sample.2)
              configuration.verifierLimits .verifier middleFuel sourceRun.oracle
              (compileScript (beforeAlphaMarkerScript out gamma
                execution.prefixes.adversary.result configuration.z sourceDigest))
            have creatorAtMarker := history_since_member_survives_prefix
              sourceRun.oracle markerRun.oracle markerRun.oracle creator
              sourceToMarker (List.prefix_refl _) (by
                simpa [sourceRun, middleFuel, markerRun] using creatorMember)
            exact .freshMarkerTargetEvent
              (routeCreator creator creatorAtMarker actorEq freshOrigin inputEq
                found)
  exact ⟨execution, record, digest, verifierExact, acceptedBody, out, gamma,
    sourceDigest, boundary, preDigest, before, middle, middleResultDigest,
    cutWitness, by simpa [sourceRun, preRun] using routed⟩

#print axioms returned_accepted_exact_root_routes_alpha_marker_target_event

end
end AspisV8Completion.FSV8AcceptedExactRootAlphaMarkerTargetEvent
