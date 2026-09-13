import FSV8SuccessfulProgrammedBindCut
import FSV8BeforeAlphaMarkerFactorization
import FSV8CompileScriptAlgebra

/-!
# Successful pre-alpha execution constructs its programmed marker cut

This leaf exposes the exact state immediately before the alpha nonce marker
from one normally returned pre-alpha machine execution.  The `BeforeAlphaMarker`
value and its stored digest are produced by that execution; neither is supplied
as an independent correspondence premise.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8ProgrammedBeforeAlphaMarkerCut

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SharedOracleVerifierRunner
open FSV8V7OracleMachineBridge
open FSV8V7ProgrammedAlignment
open FSV8SuccessfulProgrammedBindCut
open FSV8ExecutablePreAlphaFactorization
open FSV8BeforeAlphaMarkerFactorization
open FSV8CompileScriptAlgebra

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

/-- A successful pre-alpha machine run constructs the actual before-marker
prefix, its programmed-aligned oracle state, and the successful one-query
continuation that returns the requested pre-alpha boundary. -/
theorem returned_preAlpha_constructs_programmed_marker_cut
    {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor)
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (digest : Block) (v7 : OracleState) (fs : State Bytes Block)
    (fuel : Nat) (boundary : PreAlpha out gamma body z)
    (finalDigest : Block)
    (aligned : StateAligned tape finiteTape v7 fs)
    (success :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (compileScript (preAlphaScript out gamma body z digest))).halt =
          .returned (.ok boundary, finalDigest)) :
    ∃ before : BeforeAlphaMarker out gamma body z,
      let prefixRun := runMachine (controllerFromFreshAnswerTape finiteTape)
        limits actor fuel v7
        (compileScript (beforeAlphaMarkerScript out gamma body z digest))
      let continuationRun := runMachine
        (controllerFromFreshAnswerTape finiteTape) limits actor
        (fuel - prefixRun.steps) prefixRun.oracle
        (compileScript (alphaMarkerContinuation out gamma body z before))
      prefixRun.halt = .returned (.ok before, before.digest) ∧
      continuationRun.halt = .returned (.ok boundary, finalDigest) ∧
      (run tape (beforeAlphaMarkerScript out gamma body z digest) fs).1 =
        some (.ok before, before.digest) ∧
      StateAligned tape finiteTape prefixRun.oracle
        (run tape (beforeAlphaMarkerScript out gamma body z digest) fs).2 := by
  have factoredSuccess :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (compileScript (factoredPreAlphaScript out gamma body z digest))).halt =
          .returned (.ok boundary, finalDigest) := by
    rw [compile_factoredPreAlphaScript_eq_preAlphaScript]
    exact success
  let markerNext :
      (Except FSLiveSourceFunctionalMiddle.Error
        (BeforeAlphaMarker out gamma body z) × Block) →
        Script Bytes Block
          (Except FSLiveSourceFunctionalMiddle.Error
            (PreAlpha out gamma body z) × Block) 1 :=
    fun boundaryDraw =>
      match boundaryDraw.1 with
      | .error e => .done (.error e, boundaryDraw.2)
      | .ok before => alphaMarkerContinuation out gamma body z before
  have compiledFactor :
      compileScript (factoredPreAlphaScript out gamma body z digest) =
        bindOracleMachine
          (compileScript (beforeAlphaMarkerScript out gamma body z digest))
          (fun value => compileScript (markerNext value)) := by
    simp only [factoredPreAlphaScript, markerNext, compileScript_bind]
    rfl
  have bindSuccess :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (bindOracleMachine
          (compileScript (beforeAlphaMarkerScript out gamma body z digest))
          (fun value => compileScript (markerNext value)))).halt =
          .returned (.ok boundary, finalDigest) := by
    rw [← compiledFactor]
    exact factoredSuccess
  obtain ⟨value, prefixReturned, continuationReturned, prefixFunctional,
      prefixAligned, _finalOracle, _totalSteps⟩ :=
    returned_bind_constructs_programmed_cut limits actor
      (beforeAlphaMarkerScript out gamma body z digest)
      markerNext
      v7 fs (.ok boundary, finalDigest) aligned bindSuccess
  rcases value with ⟨outcome, returnedDigest⟩
  cases outcome with
  | error e =>
      simp [markerNext, compileScript, runMachine] at continuationReturned
  | ok before =>
      have digestExact : returnedDigest = before.digest :=
        successful_beforeAlphaMarker_digest out gamma body z digest tape fs
          before returnedDigest prefixFunctional
      subst returnedDigest
      exact ⟨before, prefixReturned, continuationReturned, prefixFunctional,
        prefixAligned⟩

#print axioms returned_preAlpha_constructs_programmed_marker_cut

end
end AspisV8Completion.FSV8ProgrammedBeforeAlphaMarkerCut
