import FSV8ProgrammedAlphaPreMarkerTarget

/-!
# Preserve the concrete pre-alpha creator at the marker cut

The older request-target theorem erased the fresh record after using it.  This
leaf retains that record, because exact-root target routing must prove that the
same fresh verifier record is present at the later global request state.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 2600

namespace AspisV8Completion.FSV8PreAlphaMarkerCreator

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73TranscriptSchedule
open FSV8V7OracleMachineBridge
open FSV8PostOODGammaScript
open FSLiveSourceFunctionalMiddle
open FSLiveSelectedMiddleQueryRho
open FSV8ExecutablePreAlphaFactorization
open FSV8BeforeAlphaMarkerFactorization
open FSV8ProgrammedAlphaCandidateDisposition
open FSV8ProgrammedAlphaCutWitness
open FSV8ProgrammedAlphaMarkerQuery
open FSV8ProgrammedAlphaMarkerFinalOracle
open FSV8AlphaMarkerCandidateSeparation
open FSV8ProgrammedAlphaFreshEntryProvenance

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

theorem prealpha_inserted_candidate_has_before_marker_fresh_creator
    {steps : Nat} {tape : Tape}
    (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block)
    (v7 : OracleState) (fs : State Bytes Block) (fuel : Nat)
    (out : FSV8PostOODGammaScript.OODResult) (gamma : K)
    (sourceDigest : Block)
    (boundary : PreAlpha out gamma body z) (preDigest : Block)
    (before : BeforeAlphaMarker out gamma body z)
    (middle : Success out gamma body z) (middleResultDigest : Block)
    (cutWitness : ProgrammedAlphaCutWitness (tape := tape) finiteTape limits
      actor firstWork secondWork z body digest v7 fs fuel out gamma
      sourceDigest boundary preDigest before middle middleResultDigest)
    (entry : TableEntry)
    (sourceAbsent :
      let sourceRun := sourceMachineRun finiteTape limits actor firstWork
        secondWork body digest v7 fuel
      lookupEntry sourceRun.oracle (List.ofFn boundary.digest ++ [1]) = none)
    (preLookup :
      let preRun := preAlphaMachineRun finiteTape limits actor firstWork
        secondWork body digest v7 fuel out gamma z sourceDigest
      lookupEntry preRun.oracle (List.ofFn boundary.digest ++ [1]) =
        some entry) :
    let sourceRun := sourceMachineRun finiteTape limits actor firstWork
      secondWork body digest v7 fuel
    let middleFuel := fuel - sourceRun.steps
    let markerRun := runMachine (controllerFromFreshAnswerTape finiteTape)
      limits actor middleFuel sourceRun.oracle
      (compileScript (beforeAlphaMarkerScript out gamma body z sourceDigest))
    ∃ record : QueryRecord,
      record ∈ historySince sourceRun.oracle markerRun.oracle ∧
      record.actor = actor ∧ record.origin = .fresh ∧
      record.input = List.ofFn boundary.digest ++ [1] := by
  let candidateInput := List.ofFn boundary.digest ++ [1]
  let markerInput := List.ofFn before.digest ++ [0, 20] ++
    (0 :: alpha0NonceBytes body)
  let sourceRun := sourceMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel
  let middleFuel := fuel - sourceRun.steps
  let preRun := preAlphaMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel out gamma z sourceDigest
  let markerRun := runMachine (controllerFromFreshAnswerTape finiteTape)
    limits actor middleFuel sourceRun.oracle
    (compileScript (beforeAlphaMarkerScript out gamma body z sourceDigest))
  let markerContinuation := runMachine
    (controllerFromFreshAnswerTape finiteTape) limits actor
    (middleFuel - markerRun.steps) markerRun.oracle
    (compileScript (alphaMarkerContinuation out gamma body z before))
  have cutCopy := cutWitness
  unfold ProgrammedAlphaCutWitness at cutCopy
  rcases cutCopy with
    ⟨_sourceReturned, _sourceFunctional, _preReturned, _markerReturned,
      markerReturned, _postAlphaReturned, _markerFunctional, _markerAligned,
      _markerContinuationFunctional, _afterMarkerAligned⟩
  have preOracleExact : preRun.oracle = markerContinuation.oracle := by
    simpa [sourceRun, middleFuel, preRun, markerRun, markerContinuation] using
      cut_witness_preAlpha_oracle_eq_marker_continuation finiteTape limits
        actor firstWork secondWork z body digest v7 fs fuel out gamma
        sourceDigest boundary preDigest before middle middleResultDigest
        cutWitness
  obtain ⟨nextState, markerQuery, continuationOracleExact⟩ :=
    returned_marker_continuation_exposes_query finiteTape limits actor out
      gamma body z boundary preDigest before (middleFuel - markerRun.steps)
      markerRun.oracle (by
        simpa [sourceRun, middleFuel, markerRun, markerContinuation,
          sourceMachineRun] using markerReturned)
  have markerNeCandidate : markerInput ≠ candidateInput :=
    alpha_marker_absorb_input_ne_candidate_input before.digest
      boundary.digest (alpha0NonceBytes body)
  have candidatePreserved :
      lookupEntry nextState candidateInput =
        lookupEntry markerRun.oracle candidateInput :=
    queryOracle_success_preserves_lookup_of_ne
      (controllerFromFreshAnswerTape finiteTape) limits actor markerRun.oracle
      nextState markerInput candidateInput boundary.digest markerNeCandidate
      (by simpa [markerInput] using markerQuery)
  have markerLookup : lookupEntry markerRun.oracle candidateInput = some entry := by
    rw [← candidatePreserved, ← continuationOracleExact, ← preOracleExact]
    simpa [preRun, candidateInput] using preLookup
  obtain ⟨record, member, actorEq, fresh, inputEq, _outputEq, _entryEq⟩ :=
    run_machine_lookup_of_initially_absent_is_fresh
      (controllerFromFreshAnswerTape finiteTape) limits actor middleFuel
      sourceRun.oracle
      (compileScript (beforeAlphaMarkerScript out gamma body z sourceDigest))
      candidateInput entry (by simpa [sourceRun, candidateInput] using sourceAbsent)
      (by simpa [markerRun] using markerLookup)
  exact ⟨record, by simpa [markerRun] using member, actorEq, fresh,
    by simpa [candidateInput] using inputEq⟩

#print axioms prealpha_inserted_candidate_has_before_marker_fresh_creator

end
end AspisV8Completion.FSV8PreAlphaMarkerCreator
