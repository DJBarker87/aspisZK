import FSV8ProgrammedAlphaCutWitness
import FSV8ProgrammedAlphaCandidateDisposition
import FSV8ReturnedBindMachineSplit

/-!
# Exact oracle equality across the factored alpha marker

For a fixed successful alpha-cut witness, the final oracle of the original
pre-alpha machine is exactly the final oracle of the before-marker prefix
followed by its one-query marker continuation.  This is obtained by the proved
compiled-program factorization and operational bind splitting, not by a
functional alignment assumption.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 450000
set_option maxRecDepth 2400

namespace AspisV8Completion.FSV8ProgrammedAlphaMarkerFinalOracle

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SharedOracleVerifierRunner
open FSV8V7OracleMachineBridge
open FSV8PostOODGammaScript
open FSLiveSourceFunctionalMiddle
open FSV8ExecutablePreAlphaFactorization
open FSV8BeforeAlphaMarkerFactorization
open FSV8ProgrammedAlphaCandidateDisposition
open FSV8ProgrammedAlphaCutWitness
open FSV8ReturnedBindMachineSplit
open FSV8CompileScriptAlgebra

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

theorem cut_witness_preAlpha_oracle_eq_marker_continuation
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
      sourceDigest boundary preDigest before middle middleResultDigest) :
    let sourceRun := sourceMachineRun finiteTape limits actor firstWork
      secondWork body digest v7 fuel
    let middleFuel := fuel - sourceRun.steps
    let preRun := preAlphaMachineRun finiteTape limits actor firstWork
      secondWork body digest v7 fuel out gamma z sourceDigest
    let markerRun := runMachine (controllerFromFreshAnswerTape finiteTape)
      limits actor middleFuel sourceRun.oracle
      (compileScript
        (beforeAlphaMarkerScript out gamma body z sourceDigest))
    let markerContinuation := runMachine
      (controllerFromFreshAnswerTape finiteTape) limits actor
      (middleFuel - markerRun.steps) markerRun.oracle
      (compileScript (alphaMarkerContinuation out gamma body z before))
    preRun.oracle = markerContinuation.oracle := by
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
  unfold ProgrammedAlphaCutWitness at cutWitness
  rcases cutWitness with
    ⟨_sourceReturned, _sourceFunctional, preReturned, markerReturned,
      _markerContinuationReturned, _postAlphaReturned, _markerFunctional,
      _markerAligned, _markerContinuationFunctional, _afterMarkerAligned⟩
  let markerNext :
      (Except FSLiveSourceFunctionalMiddle.Error
        (BeforeAlphaMarker out gamma body z) × Block) →
        Script Bytes Block
          (Except FSLiveSourceFunctionalMiddle.Error
            (PreAlpha out gamma body z) × Block) 1 :=
    fun boundaryDraw =>
      match boundaryDraw.1 with
      | .error e => .done (.error e, boundaryDraw.2)
      | .ok selected => alphaMarkerContinuation out gamma body z selected
  have compiledFactor :
      compileScript (factoredPreAlphaScript out gamma body z sourceDigest) =
        bindOracleMachine
          (compileScript
            (beforeAlphaMarkerScript out gamma body z sourceDigest))
          (fun value => compileScript (markerNext value)) := by
    unfold factoredPreAlphaScript
    rw [compileScript_bind]
    apply congrArg
      (bindOracleMachine
        (compileScript
          (beforeAlphaMarkerScript out gamma body z sourceDigest)))
    funext value
    rcases value with ⟨outcome, returnedDigest⟩
    cases outcome <;> rfl
  have factoredReturned :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
        middleFuel sourceRun.oracle
        (compileScript
          (factoredPreAlphaScript out gamma body z sourceDigest))).halt =
        .returned (.ok boundary, preDigest) := by
    rw [compile_factoredPreAlphaScript_eq_preAlphaScript]
    simpa [preRun, preAlphaMachineRun, sourceRun, sourceMachineRun,
      middleFuel] using preReturned
  have bindReturned :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
        middleFuel sourceRun.oracle
        (bindOracleMachine
          (compileScript
            (beforeAlphaMarkerScript out gamma body z sourceDigest))
          (fun value => compileScript (markerNext value)))).halt =
        .returned (.ok boundary, preDigest) := by
    rw [← compiledFactor]
    exact factoredReturned
  obtain ⟨value, prefixReturned, _continuationReturned, finalOracle, _steps⟩ :=
    runMachine_bind_returned_split
      (controllerFromFreshAnswerTape finiteTape) limits actor middleFuel
      sourceRun.oracle
      (compileScript
        (beforeAlphaMarkerScript out gamma body z sourceDigest))
      (fun value => compileScript (markerNext value))
      (.ok boundary, preDigest) bindReturned
  have valueExact : value = (.ok before, before.digest) := by
    have : (MachineHalt.returned value :
        MachineHalt
          (Except FSLiveSourceFunctionalMiddle.Error
            (BeforeAlphaMarker out gamma body z) × Block)) =
        .returned (.ok before, before.digest) :=
      prefixReturned.symm.trans markerReturned
    exact MachineHalt.returned.inj this
  subst value
  have finalExact :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
        middleFuel sourceRun.oracle
        (compileScript
          (factoredPreAlphaScript out gamma body z sourceDigest))).oracle =
        markerContinuation.oracle := by
    rw [compiledFactor]
    simpa [markerContinuation, markerRun, markerNext] using finalOracle
  calc
    preRun.oracle =
        (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
          middleFuel sourceRun.oracle
          (compileScript
            (factoredPreAlphaScript out gamma body z sourceDigest))).oracle := by
      rw [compile_factoredPreAlphaScript_eq_preAlphaScript]
      rfl
    _ = markerContinuation.oracle := finalExact

#print axioms cut_witness_preAlpha_oracle_eq_marker_continuation

end
end AspisV8Completion.FSV8ProgrammedAlphaMarkerFinalOracle
