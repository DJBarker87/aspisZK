import FSV8ProgrammedPrefixMiddleCut

/-!
# Successful factored whole verifier constructs its prefix-middle cut

This is the outermost source-shaped bind cut.  It retains the authenticated
suffix continuation and obtains its staged value from the same submitted
body's normally returned machine execution.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8ProgrammedWholePrefixCut

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

/-- Accepted factored whole execution constructs the successful prefix-middle
machine prefix, its aligned cut state, and the authenticated suffix run. -/
theorem returned_factoredWhole_constructs_prefixMiddle_cut
    {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (cuts : RootCuts) (body : Bytes) (digest : Block)
    (v7 : OracleState) (fs : State Bytes Block) (fuel : Nat)
    (record : Record body z) (finalDigest : Block)
    (aligned : StateAligned tape finiteTape v7 fs)
    (success :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (compileScript (factoredWholeStagedScript firstWork secondWork z cuts
          body digest))).halt = .returned (.ok record, finalDigest)) :
    ∃ staged middleDigest,
      let prefixRun := runMachine (controllerFromFreshAnswerTape finiteTape)
        limits actor fuel v7
        (compileScript
          (factoredPrefixMiddleScript firstWork secondWork z body digest))
      let continuationRun := runMachine
        (controllerFromFreshAnswerTape finiteTape) limits actor
        (fuel - prefixRun.steps) prefixRun.oracle
        (compileScript (suffixContinuation cuts body z middleDigest staged))
      prefixRun.halt = .returned (.ok staged, middleDigest) ∧
      continuationRun.halt = .returned (.ok record, finalDigest) ∧
      (run tape
        (factoredPrefixMiddleScript firstWork secondWork z body digest) fs).1 =
        some (.ok staged, middleDigest) ∧
      StateAligned tape finiteTape prefixRun.oracle
        (run tape
          (factoredPrefixMiddleScript firstWork secondWork z body digest) fs).2 := by
  let wholeNext :
      (Except FSAuthenticatedInterleavedPrefixMiddle.Error (Partial body z) ×
        Block) →
        Script Bytes Block
          (Except FSAuthenticatedInterleavedPrefixMiddle.Error (Record body z) ×
            Block) 1038 :=
    fun prefixDraw =>
      match prefixDraw.1 with
      | .error e => .done (Except.error e, prefixDraw.2)
      | .ok staged => suffixContinuation cuts body z prefixDraw.2 staged
  have compiledFactor :
      compileScript
          (factoredWholeStagedScript firstWork secondWork z cuts body digest) =
        bindOracleMachine
          (compileScript
            (factoredPrefixMiddleScript firstWork secondWork z body digest))
          (fun value => compileScript (wholeNext value)) := by
    unfold factoredWholeStagedScript
    rw [FSV8CompileScriptAlgebra.compileScript_bind]
    apply congrArg
      (bindOracleMachine (compileScript
        (factoredPrefixMiddleScript firstWork secondWork z body digest)))
    funext value
    rcases value with ⟨outcome, middleDigest⟩
    cases outcome <;> rfl
  have bindSuccess :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (bindOracleMachine
          (compileScript
            (factoredPrefixMiddleScript firstWork secondWork z body digest))
          (fun value => compileScript (wholeNext value)))).halt =
          .returned (.ok record, finalDigest) := by
    rw [← compiledFactor]
    exact success
  obtain ⟨value, prefixReturned, continuationReturned, prefixFunctional,
      prefixAligned, _finalOracle, _totalSteps⟩ :=
    returned_bind_constructs_programmed_cut limits actor
      (factoredPrefixMiddleScript firstWork secondWork z body digest) wholeNext
      v7 fs (.ok record, finalDigest) aligned bindSuccess
  rcases value with ⟨outcome, middleDigest⟩
  cases outcome with
  | error e =>
      simp [wholeNext, compileScript, runMachine] at continuationReturned
  | ok staged =>
      exact ⟨staged, middleDigest, prefixReturned, continuationReturned,
        prefixFunctional, prefixAligned⟩

#print axioms returned_factoredWhole_constructs_prefixMiddle_cut

end
end AspisV8Completion.FSV8ProgrammedWholePrefixCut
