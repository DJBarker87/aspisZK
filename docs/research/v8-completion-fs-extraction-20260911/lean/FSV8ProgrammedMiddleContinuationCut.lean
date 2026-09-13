import FSV8SuccessfulProgrammedBindCut
import FSV8CompiledWholeFactorization

/-!
# Successful factored middle continuation constructs its internal cut

This exposes the actual `factoredMiddleScript` prefix from a normally
returned `factoredMiddleContinuationAt` execution.  The continuation is the
zero-cost wrapper already present in `factoredMiddleContinuationAt`; no extra
freshness or security premise is introduced.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8ProgrammedMiddleContinuationCut

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SharedOracleVerifierRunner
open FSV8V7OracleMachineBridge
open FSV8V7ProgrammedAlignment
open FSV8SuccessfulProgrammedBindCut
open FSV8ExecutableWholeFactorization
open FSV8ExecutablePreAlphaFactorization
open FSLiveSourceFunctionalMiddle
open FSAuthenticatedInterleavedPrefixMiddle

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

/-- An accepted factored-middle wrapper constructs its actual successful
middle prefix, aligned finite-tape state, and the zero-cost wrapper
continuation which returns the accepted partial result. -/
theorem returned_factoredMiddleContinuationAt_constructs_middle_cut
    {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor)
    (body : Bytes) (z : Fin 10 → K) (out : OODResult) (gamma : K)
    (digest : Block) (v7 : OracleState) (fs : State Bytes Block)
    (fuel : Nat) (staged : Partial body z) (finalDigest : Block)
    (aligned : StateAligned tape finiteTape v7 fs)
    (success :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (compileScript (factoredMiddleContinuationAt body z out gamma digest))).halt =
          .returned (.ok staged, finalDigest)) :
    ∃ middle : Success out gamma body z, ∃ prefixDigest : Block,
      let prefixRun := runMachine (controllerFromFreshAnswerTape finiteTape)
        limits actor fuel v7
        (compileScript (factoredMiddleScript out gamma body z digest))
      let continuationRun := runMachine
        (controllerFromFreshAnswerTape finiteTape) limits actor
        (fuel - prefixRun.steps) prefixRun.oracle
        (compileScript
          (Script.done
            (Except.ok { out := out, gamma := gamma, middle := middle },
              prefixDigest) :
            Script Bytes Block
              (Except FSAuthenticatedInterleavedPrefixMiddle.Error
                (Partial body z) × Block) 0))
      prefixRun.halt = .returned (.ok middle, prefixDigest) ∧
      continuationRun.halt = .returned (.ok staged, finalDigest) ∧
      (run tape (factoredMiddleScript out gamma body z digest) fs).1 =
        some (.ok middle, prefixDigest) ∧
      StateAligned tape finiteTape prefixRun.oracle
        (run tape (factoredMiddleScript out gamma body z digest) fs).2 := by
  let middleNext :
      (Result out gamma body z × Block) →
        Script Bytes Block (Except FSAuthenticatedInterleavedPrefixMiddle.Error
          (Partial body z) × Block) 0 :=
    fun middleDraw =>
      .done (match middleDraw.1 with
        | .error e => (Except.error (.middle e), middleDraw.2)
        | .ok middle =>
            (Except.ok { out := out, gamma := gamma, middle := middle },
              middleDraw.2))
  have compiledFactor :
      compileScript (factoredMiddleContinuationAt body z out gamma digest) =
        bindOracleMachine
          (compileScript (factoredMiddleScript out gamma body z digest))
          (fun value => compileScript (middleNext value)) := by
    unfold factoredMiddleContinuationAt
    rw [FSV8CompileScriptAlgebra.compileScript_bind]
    rfl
  have bindSuccess :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (bindOracleMachine
          (compileScript (factoredMiddleScript out gamma body z digest))
          (fun value => compileScript (middleNext value)))).halt =
          .returned (.ok staged, finalDigest) := by
    rw [← compiledFactor]
    exact success
  obtain ⟨value, prefixReturned, continuationReturned, prefixFunctional,
      prefixAligned, _finalOracle, _totalSteps⟩ :=
    returned_bind_constructs_programmed_cut limits actor
      (factoredMiddleScript out gamma body z digest) middleNext
      v7 fs (.ok staged, finalDigest) aligned bindSuccess
  rcases value with ⟨outcome, prefixDigest⟩
  cases outcome with
  | error e =>
      simp [middleNext, compileScript, runMachine] at continuationReturned
  | ok middle =>
      exact ⟨middle, prefixDigest, prefixReturned, continuationReturned,
        prefixFunctional, prefixAligned⟩

#print axioms returned_factoredMiddleContinuationAt_constructs_middle_cut

end
end AspisV8Completion.FSV8ProgrammedMiddleContinuationCut
