import FSV8SuccessfulProgrammedBindCut
import FSV8CompiledWholeFactorization

/-!
# Successful prefix-middle constructs its source/gamma cut

The source/OOD/gamma prefix and its continuation are obtained from the same
normally returned compiled execution.  The returned body and source values
are not supplied through a separate functional trace.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8ProgrammedPrefixMiddleCut

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SharedOracleVerifierRunner
open FSV8V7OracleMachineBridge
open FSV8V7ProgrammedAlignment
open FSV8SuccessfulProgrammedBindCut
open FSV8PostOODGammaScript
open FSAuthenticatedInterleavedPrefixMiddle
open FSV8ExecutableWholeFactorization

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

/-- Accepted prefix-middle execution constructs its actual source/OOD/gamma
prefix and the aligned entry to the corresponding factored middle wrapper. -/
theorem returned_factoredPrefixMiddle_constructs_source_cut
    {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block)
    (v7 : OracleState) (fs : State Bytes Block) (fuel : Nat)
    (staged : Partial body z) (finalDigest : Block)
    (aligned : StateAligned tape finiteTape v7 fs)
    (success :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (compileScript (factoredPrefixMiddleScript firstWork secondWork z body
          digest))).halt = .returned (.ok staged, finalDigest)) :
    ∃ out gamma prefixDigest,
      let prefixRun := runMachine (controllerFromFreshAnswerTape finiteTape)
        limits actor fuel v7
        (compileScript (sourceThenGammaScript firstWork secondWork body digest))
      let continuationRun := runMachine
        (controllerFromFreshAnswerTape finiteTape) limits actor
        (fuel - prefixRun.steps) prefixRun.oracle
        (compileScript
          (factoredMiddleContinuationAt body z out gamma prefixDigest))
      prefixRun.halt = .returned (.ok (out, gamma), prefixDigest) ∧
      continuationRun.halt = .returned (.ok staged, finalDigest) ∧
      (run tape (sourceThenGammaScript firstWork secondWork body digest) fs).1 =
        some (.ok (out, gamma), prefixDigest) ∧
      StateAligned tape finiteTape prefixRun.oracle
        (run tape (sourceThenGammaScript firstWork secondWork body digest) fs).2 := by
  let sourceNext :
      (Except (Sum FSOODSampler.Error FSNonzeroQM31.Error)
        (FSV7OODBodyScript.Result × K) × Block) →
        Script Bytes Block
          (Except FSAuthenticatedInterleavedPrefixMiddle.Error
            (Partial body z) × Block) middleBudget :=
    fun prefixDraw =>
      match prefixDraw.1 with
      | .error e => .done (Except.error (.prefix e), prefixDraw.2)
      | .ok pair =>
          factoredMiddleContinuationAt body z pair.1 pair.2 prefixDraw.2
  have compiledFactor :
      compileScript
          (factoredPrefixMiddleScript firstWork secondWork z body digest) =
        bindOracleMachine
          (compileScript (sourceThenGammaScript firstWork secondWork body digest))
          (fun value => compileScript (sourceNext value)) := by
    unfold factoredPrefixMiddleScript
    rw [FSV8CompileScriptAlgebra.compileScript_bind]
    apply congrArg
      (bindOracleMachine (compileScript
        (sourceThenGammaScript firstWork secondWork body digest)))
    funext value
    rcases value with ⟨outcome, returnedDigest⟩
    cases outcome with
    | error e => rfl
    | ok pair => rcases pair with ⟨out, gamma⟩; rfl
  have bindSuccess :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (bindOracleMachine
          (compileScript (sourceThenGammaScript firstWork secondWork body digest))
          (fun value => compileScript (sourceNext value)))).halt =
          .returned (.ok staged, finalDigest) := by
    rw [← compiledFactor]
    exact success
  obtain ⟨value, prefixReturned, continuationReturned, prefixFunctional,
      prefixAligned, _finalOracle, _totalSteps⟩ :=
    returned_bind_constructs_programmed_cut limits actor
      (sourceThenGammaScript firstWork secondWork body digest) sourceNext
      v7 fs (.ok staged, finalDigest) aligned bindSuccess
  rcases value with ⟨outcome, prefixDigest⟩
  cases outcome with
  | error e =>
      simp [sourceNext, compileScript, runMachine] at continuationReturned
  | ok pair =>
      rcases pair with ⟨out, gamma⟩
      exact ⟨out, gamma, prefixDigest, prefixReturned, continuationReturned,
        prefixFunctional, prefixAligned⟩

#print axioms returned_factoredPrefixMiddle_constructs_source_cut

end
end AspisV8Completion.FSV8ProgrammedPrefixMiddleCut
