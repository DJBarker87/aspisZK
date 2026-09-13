import FSV8ProgrammedBeforeAlphaMarkerCut

/-!
# Successful selected middle constructs its pre-alpha machine cut

This is the source-shaped lift from the complete factored middle to its
actual pre-alpha prefix.  It retains the post-alpha continuation rather than
deriving a prefix from a separately supplied transcript.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8ProgrammedMiddlePreAlphaCut

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SharedOracleVerifierRunner
open FSV8V7OracleMachineBridge
open FSV8V7ProgrammedAlignment
open FSV8SuccessfulProgrammedBindCut
open FSV8ExecutablePreAlphaFactorization
open FSLiveSourceFunctionalMiddle

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSV8ExecutablePreAlphaFactorization.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

/-- An accepted factored middle constructs the exact successful pre-alpha
machine prefix, the aligned oracle state at its boundary, and the remaining
post-alpha machine execution. -/
theorem returned_factoredMiddle_constructs_preAlpha_cut
    {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor)
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (digest : Block) (v7 : OracleState) (fs : State Bytes Block)
    (fuel : Nat) (middle : Success out gamma body z)
    (finalDigest : Block)
    (aligned : StateAligned tape finiteTape v7 fs)
    (success :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (compileScript (factoredMiddleScript out gamma body z digest))).halt =
          .returned (.ok middle, finalDigest)) :
    ∃ boundary : PreAlpha out gamma body z, ∃ prefixDigest : Block,
      let prefixRun := runMachine (controllerFromFreshAnswerTape finiteTape)
        limits actor fuel v7
        (compileScript (preAlphaScript out gamma body z digest))
      let continuationRun := runMachine
        (controllerFromFreshAnswerTape finiteTape) limits actor
        (fuel - prefixRun.steps) prefixRun.oracle
        (compileScript (postAlphaScript out gamma body z boundary))
      prefixRun.halt = .returned (.ok boundary, prefixDigest) ∧
      continuationRun.halt = .returned (.ok middle, finalDigest) ∧
      (run tape (preAlphaScript out gamma body z digest) fs).1 =
        some (.ok boundary, prefixDigest) ∧
      StateAligned tape finiteTape prefixRun.oracle
        (run tape (preAlphaScript out gamma body z digest) fs).2 := by
  let middleNext :
      (Except FSLiveSourceFunctionalMiddle.Error
        (PreAlpha out gamma body z) ×
          FSV8ExecutablePreAlphaFactorization.Block) →
        Script (List UInt8) FSV8ExecutablePreAlphaFactorization.Block
          (FSLiveSourceFunctionalMiddle.Result out gamma body z ×
            FSV8ExecutablePreAlphaFactorization.Block)
          postAlphaBudget :=
    fun prefixDraw =>
      match prefixDraw.1 with
      | .error e => .done (Except.error e, prefixDraw.2)
      | .ok boundary => postAlphaScript out gamma body z boundary
  have compiledFactor :
      compileScript (factoredMiddleScript out gamma body z digest) =
        bindOracleMachine
          (compileScript (preAlphaScript out gamma body z digest))
          (fun value => compileScript (middleNext value)) := by
    unfold factoredMiddleScript
    rw [FSV8CompileScriptAlgebra.compileScript_bind]
    apply congrArg
      (bindOracleMachine
        (compileScript (preAlphaScript out gamma body z digest)))
    funext value
    rcases value with ⟨outcome, returnedDigest⟩
    cases outcome <;> rfl
  have bindSuccess :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (bindOracleMachine
          (compileScript (preAlphaScript out gamma body z digest))
          (fun value => compileScript (middleNext value)))).halt =
          .returned (.ok middle, finalDigest) := by
    rw [← compiledFactor]
    exact success
  obtain ⟨value, prefixReturned, continuationReturned, prefixFunctional,
      prefixAligned, _finalOracle, _totalSteps⟩ :=
    returned_bind_constructs_programmed_cut limits actor
      (preAlphaScript out gamma body z digest)
      middleNext
      v7 fs (.ok middle, finalDigest) aligned bindSuccess
  rcases value with ⟨outcome, prefixDigest⟩
  cases outcome with
  | error e =>
      simp [middleNext, compileScript, runMachine] at continuationReturned
  | ok boundary =>
      exact ⟨boundary, prefixDigest, prefixReturned, continuationReturned,
        prefixFunctional, prefixAligned⟩

#print axioms returned_factoredMiddle_constructs_preAlpha_cut

end
end AspisV8Completion.FSV8ProgrammedMiddlePreAlphaCut
