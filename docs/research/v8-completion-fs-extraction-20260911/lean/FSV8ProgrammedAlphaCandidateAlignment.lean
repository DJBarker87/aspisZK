import FSV8ProgrammedAlphaCandidateHistoryPrefix
import FSV8ProgrammedAlphaMarkerFinalOracle
import FSV8SuccessfulProgrammedAlignmentFuel

/-!
# Candidate-machine alignment constructed from the same programmed alpha cut

The pre-alpha machine terminal is identified with the marker continuation by
the compiled bind theorem.  Its already-proved alignment is then advanced
through the literal candidate script.  Thus the candidate terminal alignment
is constructed, not accepted as a source-interface premise.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 3000

namespace AspisV8Completion.FSV8ProgrammedAlphaCandidateAlignment

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge FSV8V7ProgrammedAlignment
open FSV8PostOODGammaScript FSLiveSourceFunctionalMiddle
open FSV8ExecutablePreAlphaFactorization
open FSV8BeforeAlphaMarkerFactorization
open FSV8ProgrammedAlphaCandidateDisposition
open FSV8ProgrammedAlphaCutWitness
open FSV8ProgrammedAlphaCandidateHistoryPrefix
open FSV8ProgrammedAlphaMarkerFinalOracle
open FSV8SuccessfulProgrammedAlignmentFuel

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

theorem programmed_cut_constructs_candidate_alignment
    {steps : Nat} {tape : Tape}
    (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block)
    (v7 : OracleState) (fs : State Bytes Block) (fuel : Nat)
    (out : OODResult) (gamma : K) (sourceDigest : Block)
    (boundary : PreAlpha out gamma body z) (preDigest : Block)
    (before : BeforeAlphaMarker out gamma body z)
    (middle : Success out gamma body z) (middleResultDigest : Block)
    (cutWitness : ProgrammedAlphaCutWitness (tape := tape) finiteTape limits
      .verifier firstWork secondWork z body digest v7 fs fuel out gamma
      sourceDigest boundary preDigest before middle middleResultDigest) :
    let sourceRun := sourceMachineRun finiteTape limits .verifier firstWork
      secondWork body digest v7 fuel
    let middleFuel := fuel - sourceRun.steps
    let middleFS :=
      (run tape (sourceThenGammaScript firstWork secondWork body digest) fs).2
    let preRun := preAlphaMachineRun finiteTape limits .verifier firstWork
      secondWork body digest v7 fuel out gamma z sourceDigest
    let markerRun := runMachine (controllerFromFreshAnswerTape finiteTape)
      limits .verifier middleFuel sourceRun.oracle
      (compileScript
        (beforeAlphaMarkerScript out gamma body z sourceDigest))
    let markerFS :=
      (run tape
        (beforeAlphaMarkerScript out gamma body z sourceDigest) middleFS).2
    let markerContinuationFS :=
      (run tape
        (alphaMarkerContinuation out gamma body z before) markerFS).2
    let candidateRun := alphaCandidateMachineRun finiteTape limits .verifier
      firstWork secondWork body digest v7 fuel out gamma z sourceDigest boundary
    ∃ alpha0 candidateDigest,
      candidateRun.halt = .returned (.ok alpha0, candidateDigest) ∧
      (run tape (FSNonzeroQM31.candidateScript boundary.digest)
        markerContinuationFS).1 = some (.ok alpha0, candidateDigest) ∧
      StateAligned tape finiteTape candidateRun.oracle
        (run tape (FSNonzeroQM31.candidateScript boundary.digest)
          markerContinuationFS).2 := by
  let sourceRun := sourceMachineRun finiteTape limits .verifier firstWork
    secondWork body digest v7 fuel
  let middleFuel := fuel - sourceRun.steps
  let middleFS :=
    (run tape (sourceThenGammaScript firstWork secondWork body digest) fs).2
  let preRun := preAlphaMachineRun finiteTape limits .verifier firstWork
    secondWork body digest v7 fuel out gamma z sourceDigest
  let markerRun := runMachine (controllerFromFreshAnswerTape finiteTape)
    limits .verifier middleFuel sourceRun.oracle
    (compileScript (beforeAlphaMarkerScript out gamma body z sourceDigest))
  let markerFS :=
    (run tape (beforeAlphaMarkerScript out gamma body z sourceDigest) middleFS).2
  let markerContinuationFS :=
    (run tape (alphaMarkerContinuation out gamma body z before) markerFS).2
  let candidateRun := alphaCandidateMachineRun finiteTape limits .verifier
    firstWork secondWork body digest v7 fuel out gamma z sourceDigest boundary
  have cutCopy := cutWitness
  unfold ProgrammedAlphaCutWitness at cutCopy
  rcases cutCopy with
    ⟨_sourceReturned, _sourceFunctional, _preReturned, _markerReturned,
      _markerContinuationReturned, _postAlphaReturned, _markerFunctional,
      _markerAligned, _markerContinuationFunctional, afterMarkerAligned⟩
  have preOracleEq := cut_witness_preAlpha_oracle_eq_marker_continuation
    finiteTape limits .verifier firstWork secondWork z body digest v7 fs fuel out
    gamma sourceDigest boundary preDigest before middle middleResultDigest
    cutWitness
  have initialAligned : StateAligned tape finiteTape preRun.oracle
      markerContinuationFS := by
    rw [preOracleEq]
    simpa [sourceRun, sourceMachineRun, middleFuel, middleFS, markerRun, markerFS,
      markerContinuationFS] using afterMarkerAligned
  obtain ⟨alpha0, candidateDigest, candidateReturned, _candidateToPost⟩ :=
    programmed_cut_constructs_candidate_history_prefix finiteTape limits
      .verifier firstWork secondWork z body digest v7 fs fuel out gamma
      sourceDigest boundary preDigest before middle middleResultDigest cutWitness
  have candidateExact : candidateRun =
      { halt := .returned (.ok alpha0, candidateDigest)
        oracle := candidateRun.oracle
        steps := candidateRun.steps } := by
    have candidateReturned' : candidateRun.halt =
        .returned (.ok alpha0, candidateDigest) := by
      simpa [candidateRun] using candidateReturned
    generalize runEq : candidateRun = actualRun
    rcases actualRun with ⟨halt, oracle, used⟩
    simp only [runEq] at candidateReturned' ⊢
    rw [candidateReturned']
  have alignedResult := returned_compileScript_aligned_with_fuel limits
    .verifier (FSNonzeroQM31.candidateScript boundary.digest)
    ((fuel - sourceRun.steps) - preRun.steps) preRun.oracle
    markerContinuationFS (.ok alpha0, candidateDigest) candidateRun.oracle
    candidateRun.steps initialAligned (by
      simpa [candidateRun, alphaCandidateMachineRun, sourceRun, preRun] using
        candidateExact)
  refine ⟨alpha0, candidateDigest, candidateReturned, ?_, ?_⟩
  · simpa [candidateRun, alphaCandidateMachineRun, sourceRun, preRun] using
      alignedResult.1
  · simpa [candidateRun, alphaCandidateMachineRun, sourceRun, preRun] using
      alignedResult.2

#print axioms programmed_cut_constructs_candidate_alignment

end
end AspisV8Completion.FSV8ProgrammedAlphaCandidateAlignment
