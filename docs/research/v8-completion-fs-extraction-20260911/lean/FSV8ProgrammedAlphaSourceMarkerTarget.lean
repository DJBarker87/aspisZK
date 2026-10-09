import FSV8ProgrammedAlphaCutWitness
import FSV8AlphaMarkerPriorCreatorTarget

/-!
# A source-created alpha coordinate is a target of the actual marker

This leaf instantiates the generic literal-prefix fact on one fixed successful
V8 alpha-cut witness.  A candidate coordinate created during the earlier
source/OOD/gamma segment is chronologically present before the real alpha
marker.  The successful one-query marker continuation returns the same
post-marker boundary whose digest prefixes that coordinate.

This establishes request-level target membership.  It does not yet transport
the hit into the exact-root target tree or assign probability.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000

namespace AspisV8Completion.FSV8ProgrammedAlphaSourceMarkerTarget

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73OperationalOracleExposure
open AspisK1.V7Tag73OperationalCausalInjection
open FSV8V7OracleMachineBridge
open FSV8PostOODGammaScript
open FSLiveSelectedMiddleQueryRho
open FSV8ExecutablePreAlphaFactorization
open FSV8BeforeAlphaMarkerFactorization
open FSV8ProgrammedAlphaCandidateDisposition
open FSV8ProgrammedAlphaCutWitness
open FSV8AlphaMarkerPriorCreatorTarget

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

/-- In a fixed successful alpha-cut witness, a source-segment creator of the
eventual first alpha candidate forces the actual marker answer into the
marker request's operational target set. -/
theorem source_creator_hits_actual_marker_request_target
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
    (middle : FSLiveSourceFunctionalMiddle.Success out gamma body z)
    (middleResultDigest : Block)
    (cutWitness : ProgrammedAlphaCutWitness (tape := tape) finiteTape limits
      actor firstWork secondWork z body digest v7 fs fuel out gamma
      sourceDigest boundary preDigest before middle middleResultDigest)
    (seen : Finset Digest256) (record : QueryRecord)
    (member :
      let sourceRun := sourceMachineRun finiteTape limits actor firstWork
        secondWork body digest v7 fuel
      record ∈ historySince v7 sourceRun.oracle)
    (inputExact : record.input = List.ofFn boundary.digest ++ [1]) :
    let sourceRun := sourceMachineRun finiteTape limits actor firstWork
      secondWork body digest v7 fuel
    let middleFuel := fuel - sourceRun.steps
    let markerRun := runMachine (controllerFromFreshAnswerTape finiteTape)
      limits actor middleFuel sourceRun.oracle
      (compileScript
        (beforeAlphaMarkerScript out gamma body z sourceDigest))
    let markerContinuation := runMachine
      (controllerFromFreshAnswerTape finiteTape) limits actor
      (middleFuel - markerRun.steps) markerRun.oracle
      (compileScript (alphaMarkerContinuation out gamma body z before))
    markerContinuation.halt = .returned (.ok boundary, preDigest) ∧
    boundary.digest ∈ operationalRequestTargets seen markerRun.oracle.history
      (List.ofFn before.digest ++ [0, 20] ++
        (0 :: alpha0NonceBytes body)) := by
  let sourceRun := sourceMachineRun finiteTape limits actor firstWork secondWork
    body digest v7 fuel
  let middleFuel := fuel - sourceRun.steps
  let markerRun := runMachine (controllerFromFreshAnswerTape finiteTape)
    limits actor middleFuel sourceRun.oracle
    (compileScript (beforeAlphaMarkerScript out gamma body z sourceDigest))
  let markerContinuation := runMachine
    (controllerFromFreshAnswerTape finiteTape) limits actor
    (middleFuel - markerRun.steps) markerRun.oracle
    (compileScript (alphaMarkerContinuation out gamma body z before))
  unfold ProgrammedAlphaCutWitness at cutWitness
  rcases cutWitness with
    ⟨_sourceReturned, _sourceFunctional, _preReturned, _markerReturned,
      markerContinuationReturned, _postAlphaReturned, _markerFunctional,
      _markerAligned, _markerContinuationFunctional, _afterMarkerAligned⟩
  have sourcePrefix :
      v7.history <+: sourceRun.oracle.history := by
    exact postfork_run_history_is_preserved
      (controllerFromFreshAnswerTape finiteTape) limits actor fuel v7
      (compileScript
        (sourceThenGammaScript firstWork secondWork body digest))
  have markerPrefix :
      sourceRun.oracle.history <+: markerRun.oracle.history := by
    exact postfork_run_history_is_preserved
      (controllerFromFreshAnswerTape finiteTape) limits actor middleFuel
      sourceRun.oracle
      (compileScript
        (beforeAlphaMarkerScript out gamma body z sourceDigest))
  have target :=
    earlier_segment_alpha_creator_hits_marker_request_target seen v7
      sourceRun.oracle markerRun.oracle
      (List.ofFn before.digest ++ [0, 20] ++ (0 :: alpha0NonceBytes body))
      boundary.digest record sourcePrefix markerPrefix member inputExact
  exact ⟨markerContinuationReturned, target⟩

#print axioms source_creator_hits_actual_marker_request_target

end
end AspisV8Completion.FSV8ProgrammedAlphaSourceMarkerTarget
