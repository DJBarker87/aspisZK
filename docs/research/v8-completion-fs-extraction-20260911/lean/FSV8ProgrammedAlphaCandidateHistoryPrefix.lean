import FSV8ProgrammedPostAlphaHistoryPrefix
import FSV8ProgrammedAlphaCandidateDisposition

/-!
# The successful alpha candidate is inside the post-alpha run

The candidate run and the post-alpha run below are both derived from one
`ProgrammedAlphaCutWitness`.  The prefix is obtained by inverting the literal
compiled bind; no oracle-state equality or bind decomposition is supplied by
the caller.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 2600

namespace AspisV8Completion.FSV8ProgrammedAlphaCandidateHistoryPrefix

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73SharedOracleVerifierRunner
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge
open FSV8PostOODGammaScript FSLiveSourceFunctionalMiddle
open FSV8ExecutablePreAlphaFactorization
open FSV8ProgrammedAlphaCandidateDisposition
open FSV8ProgrammedAlphaCutWitness
open FSV8ReturnedBindKnownPrefix
open FSV8ReturnedBindMachineSplit

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

/-- One successful programmed cut constructs the exact candidate-machine
terminal and proves that its history is a prefix of the corresponding
post-alpha terminal. -/
theorem programmed_cut_constructs_candidate_history_prefix
    {steps : Nat} {tape : Tape}
    (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block)
    (v7 : OracleState) (fs : State Bytes Block) (fuel : Nat)
    (out : OODResult) (gamma : K) (sourceDigest : Block)
    (boundary : PreAlpha out gamma body z) (preDigest : Block)
    (before : FSV8BeforeAlphaMarkerFactorization.BeforeAlphaMarker
      out gamma body z)
    (middle : Success out gamma body z) (middleResultDigest : Block)
    (cutWitness : ProgrammedAlphaCutWitness (tape := tape) finiteTape limits
      actor firstWork secondWork z body digest v7 fs fuel out gamma sourceDigest
      boundary preDigest before middle middleResultDigest) :
    let sourceRun := sourceMachineRun finiteTape limits actor firstWork
      secondWork body digest v7 fuel
    let middleFuel := fuel - sourceRun.steps
    let preRun := preAlphaMachineRun finiteTape limits actor firstWork secondWork
      body digest v7 fuel out gamma z sourceDigest
    let candidateRun := alphaCandidateMachineRun finiteTape limits actor
      firstWork secondWork body digest v7 fuel out gamma z sourceDigest boundary
    let postAlphaRun := runMachine (controllerFromFreshAnswerTape finiteTape)
      limits actor (middleFuel - preRun.steps) preRun.oracle
      (compileScript (postAlphaScript out gamma body z boundary))
    ∃ alpha0 candidateDigest,
      candidateRun.halt = .returned (.ok alpha0, candidateDigest) ∧
      candidateRun.oracle.history <+: postAlphaRun.oracle.history := by
  let sourceRun := sourceMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel
  let middleFuel := fuel - sourceRun.steps
  let preRun := preAlphaMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel out gamma z sourceDigest
  let candidateRun := alphaCandidateMachineRun finiteTape limits actor
    firstWork secondWork body digest v7 fuel out gamma z sourceDigest boundary
  let postAlphaRun := runMachine (controllerFromFreshAnswerTape finiteTape)
    limits actor (middleFuel - preRun.steps) preRun.oracle
    (compileScript (postAlphaScript out gamma body z boundary))
  have cutCopy := cutWitness
  unfold ProgrammedAlphaCutWitness at cutCopy
  rcases cutCopy with
    ⟨_sourceReturned, _sourceFunctional, _preReturned, _markerReturned,
      _markerContinuationReturned, postAlphaReturned, _markerFunctional,
      _markerAligned, _markerContinuationFunctional, _afterMarkerAligned⟩
  let alphaNext :
      (Except FSNonzeroQM31.Error K × Block) →
        Script Bytes Block (Result out gamma body z × Block) 217 :=
    fun alphaDraw =>
      match alphaDraw.1 with
      | .error e => .done
          (Except.error (Error.alpha0 e), alphaDraw.2)
      | .ok alpha =>
          bind (m := 0) (FSLiveQueryRhoSuffix.queryRhoScript body
            alphaDraw.2) fun suffixDraw =>
            .done (match suffixDraw.1 with
              | .error e => (Except.error (Error.suffix e), suffixDraw.2)
              | .ok (queries, rho) =>
                let selectedMiddle := FSLiveSelectedMiddleQueryRho.Success.mk
                  boundary.kappa boundary.tau alpha queries rho
                let sourceSuccess : Success out gamma body z :=
                  { middle := selectedMiddle
                    functional := boundary.functional
                    functionalRun := boundary.functionalRun }
                (Except.ok sourceSuccess, suffixDraw.2))
  have compiledPostAlpha :
      compileScript (postAlphaScript out gamma body z boundary) =
        bindOracleMachine
          (compileScript (FSNonzeroQM31.candidateScript boundary.digest))
          (fun value => compileScript (alphaNext value)) := by
    unfold postAlphaScript
    rw [FSV8CompileScriptAlgebra.compileScript_bind]
    apply congrArg
      (bindOracleMachine
        (compileScript (FSNonzeroQM31.candidateScript boundary.digest)))
    funext value
    rcases value with ⟨outcome, returnedDigest⟩
    cases outcome <;> rfl
  have wholeAsBind :
      (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
        (middleFuel - preRun.steps) preRun.oracle
        (bindOracleMachine
          (compileScript (FSNonzeroQM31.candidateScript boundary.digest))
          (fun value => compileScript (alphaNext value)))).halt =
        .returned (.ok middle, middleResultDigest) := by
    rw [← compiledPostAlpha]
    simpa [sourceRun, middleFuel, preRun, sourceMachineRun,
      preAlphaMachineRun] using postAlphaReturned
  obtain ⟨candidateValue, candidateReturnedRaw, continuationReturned,
      finalOracleRaw, totalSteps⟩ :=
    runMachine_bind_returned_split
      (controllerFromFreshAnswerTape finiteTape) limits actor
      (middleFuel - preRun.steps) preRun.oracle
      (compileScript (FSNonzeroQM31.candidateScript boundary.digest))
      (fun value => compileScript (alphaNext value))
      (.ok middle, middleResultDigest) wholeAsBind
  rcases candidateValue with ⟨candidateOutcome, candidateDigest⟩
  cases candidateOutcome with
  | error error =>
      simp [alphaNext, compileScript, runMachine] at continuationReturned
  | ok alpha0 =>
      have candidateReturned : candidateRun.halt =
          .returned (.ok alpha0, candidateDigest) := by
        simpa only [candidateRun, alphaCandidateMachineRun, middleFuel, preRun,
          sourceRun] using candidateReturnedRaw
      have continuationPrefix := runMachine_entry_history_prefix_final
        (controllerFromFreshAnswerTape finiteTape) limits actor
        ((middleFuel - preRun.steps) -
          (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
            (middleFuel - preRun.steps) preRun.oracle
            (compileScript
              (FSNonzeroQM31.candidateScript boundary.digest))).steps)
        (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
          (middleFuel - preRun.steps) preRun.oracle
          (compileScript
            (FSNonzeroQM31.candidateScript boundary.digest))).oracle
        (compileScript (alphaNext (.ok alpha0, candidateDigest)))
      have explicitPrefix :
          (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
            (middleFuel - preRun.steps) preRun.oracle
            (compileScript
              (FSNonzeroQM31.candidateScript boundary.digest))).oracle.history <+:
            postAlphaRun.oracle.history := by
        calc
          (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
            (middleFuel - preRun.steps) preRun.oracle
            (compileScript
              (FSNonzeroQM31.candidateScript boundary.digest))).oracle.history <+:
            (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
              ((middleFuel - preRun.steps) -
                (runMachine (controllerFromFreshAnswerTape finiteTape) limits
                  actor (middleFuel - preRun.steps) preRun.oracle
                  (compileScript
                    (FSNonzeroQM31.candidateScript boundary.digest))).steps)
              (runMachine (controllerFromFreshAnswerTape finiteTape) limits actor
                (middleFuel - preRun.steps) preRun.oracle
                (compileScript
                  (FSNonzeroQM31.candidateScript boundary.digest))).oracle
              (compileScript
                (alphaNext (.ok alpha0, candidateDigest)))).oracle.history :=
            continuationPrefix
          _ = postAlphaRun.oracle.history := by
            have continuationToBind := congrArg (fun state => state.history)
              finalOracleRaw.symm
            rw [continuationToBind]
            simp only [postAlphaRun]
            rw [compiledPostAlpha]
      refine ⟨alpha0, candidateDigest, candidateReturned, ?_⟩
      simpa only [candidateRun, alphaCandidateMachineRun, middleFuel, preRun,
        sourceRun] using explicitPrefix

#print axioms programmed_cut_constructs_candidate_history_prefix

end
end AspisV8Completion.FSV8ProgrammedAlphaCandidateHistoryPrefix
