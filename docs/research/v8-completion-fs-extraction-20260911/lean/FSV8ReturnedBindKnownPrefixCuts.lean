import FSV8ReturnedBindKnownPrefix
import FSV8ProgrammedWholePrefixCut
import FSV8ProgrammedPrefixMiddleCut
import FSV8ProgrammedMiddleContinuationCut
import FSV8ProgrammedMiddlePreAlphaCut

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8ReturnedBindKnownPrefixCuts

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73SharedOracleVerifierRunner
open FSV8V7OracleMachineBridge FSV8V7ProgrammedAlignment
open FSV8PostOODGammaScript FSLiveSourceFunctionalMiddle
open FSAuthenticatedInterleavedPrefixMiddle FSV8ExecutablePreAlphaFactorization
open FSV8ExecutableWholeFactorization
open FSV8ReturnedBindKnownPrefix
open FSV8ProgrammedWholePrefixCut FSV8ProgrammedPrefixMiddleCut
open FSV8ProgrammedMiddleContinuationCut FSV8ProgrammedMiddlePreAlphaCut

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

/- The wrappers below retain the existing cut witnesses and add only the
   final-oracle equality supplied by `runMachine_bind_final_oracle_eq...`. -/

theorem returned_factoredWhole_constructs_prefixMiddle_cut_with_final_oracle
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat} (firstWork : Point → Script Bytes Block Unit n)
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
          (factoredPrefixMiddleScript firstWork secondWork z body digest) fs).2 ∧
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (compileScript (factoredWholeStagedScript firstWork secondWork z cuts
          body digest))).oracle = continuationRun.oracle := by
  obtain ⟨staged, middleDigest, prefixReturned, continuationReturned,
      functional, prefixAligned⟩ :=
    returned_factoredWhole_constructs_prefixMiddle_cut limits actor firstWork
      secondWork z cuts body digest v7 fs fuel record finalDigest aligned success
  let wholeNext :
      (Except FSAuthenticatedInterleavedPrefixMiddle.Error (Partial body z) ×
        Block) → Script Bytes Block
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
  have wholeOracle := runMachine_bind_final_oracle_eq_of_known_prefix
    (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
      (compileScript
        (factoredPrefixMiddleScript firstWork secondWork z body digest))
      (fun value => compileScript (wholeNext value))
      (.ok staged, middleDigest) (.ok record, finalDigest)
      (by simpa [compiledFactor] using prefixReturned)
      (by simpa [compiledFactor] using success)
  refine ⟨staged, middleDigest, prefixReturned, continuationReturned,
    functional, prefixAligned, ?_⟩
  simpa [wholeNext, compiledFactor] using wholeOracle

theorem returned_factoredPrefixMiddle_constructs_source_cut_with_final_oracle
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat} (firstWork : Point → Script Bytes Block Unit n)
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
        (compileScript (factoredMiddleContinuationAt body z out gamma prefixDigest))
      prefixRun.halt = .returned (.ok (out, gamma), prefixDigest) ∧
      continuationRun.halt = .returned (.ok staged, finalDigest) ∧
      (run tape (sourceThenGammaScript firstWork secondWork body digest) fs).1 =
        some (.ok (out, gamma), prefixDigest) ∧
      StateAligned tape finiteTape prefixRun.oracle
        (run tape (sourceThenGammaScript firstWork secondWork body digest) fs).2 ∧
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (compileScript (factoredPrefixMiddleScript firstWork secondWork z body
          digest))).oracle = continuationRun.oracle := by
  obtain ⟨out, gamma, prefixDigest, prefixReturned, continuationReturned,
      functional, prefixAligned⟩ :=
    returned_factoredPrefixMiddle_constructs_source_cut limits actor firstWork
      secondWork z body digest v7 fs fuel staged finalDigest aligned success
  let sourceNext :
      (Except (Sum FSOODSampler.Error FSNonzeroQM31.Error)
        (FSV7OODBodyScript.Result × K) × Block) →
        Script Bytes Block
          (Except FSAuthenticatedInterleavedPrefixMiddle.Error
            (Partial body z) × Block) middleBudget :=
    fun prefixDraw =>
      match prefixDraw.1 with
      | .error e => .done (Except.error (.prefix e), prefixDraw.2)
      | .ok pair => factoredMiddleContinuationAt body z pair.1 pair.2 prefixDraw.2
  have compiledFactor :
      compileScript (factoredPrefixMiddleScript firstWork secondWork z body digest) =
        bindOracleMachine (compileScript (sourceThenGammaScript firstWork secondWork body digest))
          (fun value => compileScript (sourceNext value)) := by
    unfold factoredPrefixMiddleScript
    rw [FSV8CompileScriptAlgebra.compileScript_bind]
    apply congrArg (bindOracleMachine
      (compileScript (sourceThenGammaScript firstWork secondWork body digest)))
    funext value
    rcases value with ⟨outcome, returnedDigest⟩
    cases outcome with
    | error e => rfl
    | ok pair => rcases pair with ⟨out, gamma⟩; rfl
  have wholeOracle := runMachine_bind_final_oracle_eq_of_known_prefix
    (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
      (compileScript (sourceThenGammaScript firstWork secondWork body digest))
      (fun value => compileScript (sourceNext value))
      (.ok (out, gamma), prefixDigest) (.ok staged, finalDigest)
      (by simpa [compiledFactor] using prefixReturned)
      (by simpa [compiledFactor] using success)
  refine ⟨out, gamma, prefixDigest, prefixReturned, continuationReturned,
    functional, prefixAligned, ?_⟩
  simpa [sourceNext, compiledFactor] using wholeOracle

theorem returned_factoredMiddleContinuationAt_constructs_middle_cut_with_final_oracle
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
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
        (run tape (factoredMiddleScript out gamma body z digest) fs).2 ∧
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (compileScript
          (factoredMiddleContinuationAt body z out gamma digest))).oracle =
        continuationRun.oracle := by
  obtain ⟨middle, prefixDigest, prefixReturned, continuationReturned,
      functional, prefixAligned⟩ :=
    returned_factoredMiddleContinuationAt_constructs_middle_cut limits actor
      body z out gamma digest v7 fs fuel staged finalDigest aligned success
  let middleNext :
      (FSLiveSourceFunctionalMiddle.Result out gamma body z × Block) →
        Script Bytes Block
          (Except FSAuthenticatedInterleavedPrefixMiddle.Error
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
  have wholeOracle := runMachine_bind_final_oracle_eq_of_known_prefix
    (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
      (compileScript (factoredMiddleScript out gamma body z digest))
      (fun value => compileScript (middleNext value))
      (.ok middle, prefixDigest) (.ok staged, finalDigest)
      (by simpa [compiledFactor] using prefixReturned)
      (by simpa [compiledFactor] using success)
  refine ⟨middle, prefixDigest, prefixReturned, continuationReturned,
    functional, prefixAligned, ?_⟩
  simpa [middleNext, compiledFactor] using wholeOracle

theorem returned_factoredMiddle_constructs_preAlpha_cut_with_final_oracle
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor)
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (digest : Block) (v7 : OracleState) (fs : State Bytes Block)
    (fuel : Nat) (middle : Success out gamma body z) (finalDigest : Block)
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
        (run tape (preAlphaScript out gamma body z digest) fs).2 ∧
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
        (compileScript (factoredMiddleScript out gamma body z digest))).oracle =
        continuationRun.oracle := by
  obtain ⟨boundary, prefixDigest, prefixReturned, continuationReturned,
      functional, prefixAligned⟩ :=
    returned_factoredMiddle_constructs_preAlpha_cut limits actor out gamma body
      z digest v7 fs fuel middle finalDigest aligned success
  let middleNext :
      (Except FSLiveSourceFunctionalMiddle.Error (PreAlpha out gamma body z) ×
        FSV8ExecutablePreAlphaFactorization.Block) →
      Script (List UInt8) FSV8ExecutablePreAlphaFactorization.Block
        (FSLiveSourceFunctionalMiddle.Result out gamma body z ×
          FSV8ExecutablePreAlphaFactorization.Block) postAlphaBudget :=
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
    apply congrArg (bindOracleMachine
      (compileScript (preAlphaScript out gamma body z digest)))
    funext value
    rcases value with ⟨outcome, returnedDigest⟩
    cases outcome <;> rfl
  have wholeOracle := runMachine_bind_final_oracle_eq_of_known_prefix
    (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
      (compileScript (preAlphaScript out gamma body z digest))
      (fun value => compileScript (middleNext value))
      (.ok boundary, prefixDigest) (.ok middle, finalDigest)
      (by simpa [compiledFactor] using prefixReturned)
      (by simpa [compiledFactor] using success)
  refine ⟨boundary, prefixDigest, prefixReturned, continuationReturned,
    functional, prefixAligned, ?_⟩
  simpa [middleNext, compiledFactor] using wholeOracle

#print axioms returned_factoredWhole_constructs_prefixMiddle_cut_with_final_oracle
#print axioms returned_factoredPrefixMiddle_constructs_source_cut_with_final_oracle
#print axioms returned_factoredMiddleContinuationAt_constructs_middle_cut_with_final_oracle
#print axioms returned_factoredMiddle_constructs_preAlpha_cut_with_final_oracle

end
end AspisV8Completion.FSV8ReturnedBindKnownPrefixCuts
