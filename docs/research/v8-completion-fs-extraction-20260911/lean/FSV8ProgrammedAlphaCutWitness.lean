import FSV8ProgrammedWholeAlphaCut

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 350000

namespace AspisV8Completion.FSV8ProgrammedAlphaCutWitness

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open AspisK1.V7FsAokExperiment AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73OperationalOracleExposure
open FSV8V7OracleMachineBridge
open FSV8V7ProgrammedAlignment
open FSV8PostOODGammaScript
open FSLiveSourceFunctionalMiddle
open FSAuthenticatedInterleavedPrefixMiddle
open FSV8ExecutablePreAlphaFactorization
open FSV8BeforeAlphaMarkerFactorization
open FSV8ExecutableWholeFactorization
open FSV8ProgrammedWholePrefixCut
open FSV8ProgrammedPrefixMiddleCut
open FSV8ProgrammedMiddleContinuationCut
open FSV8ProgrammedMiddlePreAlphaCut
open FSV8ProgrammedBeforeAlphaMarkerCut
open FSV8ProgrammedWholeAlphaCut

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

/-- The fixed-witness form of `ProgrammedAlphaCut`.  It exposes precisely the
    eight values and the conjunction already quantified by that predicate. -/
def ProgrammedAlphaCutWitness
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
    (boundary : FSV8ExecutablePreAlphaFactorization.PreAlpha out gamma body z)
    (preDigest : Block) (before : BeforeAlphaMarker out gamma body z)
    (middle : Success out gamma body z) (middleResultDigest : Block) : Prop :=
    let sourceRun := runMachine (controllerFromFreshAnswerTape finiteTape)
      limits actor fuel v7
      (compileScript (sourceThenGammaScript firstWork secondWork body digest))
    let middleFuel := fuel - sourceRun.steps
    let middleV7 := sourceRun.oracle
    let middleFS :=
      (run tape (sourceThenGammaScript firstWork secondWork body digest) fs).2
    let preRun := runMachine (controllerFromFreshAnswerTape finiteTape)
      limits actor middleFuel middleV7
      (compileScript (preAlphaScript out gamma body z sourceDigest))
    let markerRun := runMachine
      (controllerFromFreshAnswerTape finiteTape) limits actor middleFuel middleV7
      (compileScript (beforeAlphaMarkerScript out gamma body z sourceDigest))
    let markerContinuation := runMachine
      (controllerFromFreshAnswerTape finiteTape) limits actor
      (middleFuel - markerRun.steps) markerRun.oracle
      (compileScript (alphaMarkerContinuation out gamma body z before))
    let postAlphaRun := runMachine
      (controllerFromFreshAnswerTape finiteTape) limits actor
      (middleFuel - preRun.steps) preRun.oracle
      (compileScript (postAlphaScript out gamma body z boundary))
    sourceRun.halt = .returned (.ok (out, gamma), sourceDigest) ∧
    (run tape (sourceThenGammaScript firstWork secondWork body digest) fs).1 =
      some (.ok (out, gamma), sourceDigest) ∧
    preRun.halt = .returned (.ok boundary, preDigest) ∧
    markerRun.halt = .returned (.ok before, before.digest) ∧
    markerContinuation.halt = .returned (.ok boundary, preDigest) ∧
    postAlphaRun.halt = .returned (.ok middle, middleResultDigest) ∧
    (run tape
      (beforeAlphaMarkerScript out gamma body z sourceDigest) middleFS).1 =
      some (.ok before, before.digest) ∧
    StateAligned tape finiteTape markerRun.oracle
      (run tape
        (beforeAlphaMarkerScript out gamma body z sourceDigest) middleFS).2 ∧
    (run tape (alphaMarkerContinuation out gamma body z before)
      (run tape
        (beforeAlphaMarkerScript out gamma body z sourceDigest) middleFS).2).1 =
      some (.ok boundary, preDigest) ∧
    StateAligned tape finiteTape markerContinuation.oracle
      (run tape (alphaMarkerContinuation out gamma body z before)
        (run tape
          (beforeAlphaMarkerScript out gamma body z sourceDigest) middleFS).2).2

theorem programmed_alpha_cut_constructs_witness
    {steps : Nat} {tape : Tape}
    {finiteTape : FreshAnswerTape Block steps}
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block)
    (v7 : OracleState) (fs : State Bytes Block) (fuel : Nat)
    (cut : ProgrammedAlphaCut (tape := tape) finiteTape limits actor firstWork
      secondWork z body digest v7 fs fuel) :
    ∃ out gamma sourceDigest boundary preDigest before middle middleResultDigest,
      ProgrammedAlphaCutWitness (tape := tape) finiteTape limits actor
        firstWork secondWork z body digest v7 fs fuel out gamma sourceDigest
        boundary preDigest before middle middleResultDigest := by
  unfold ProgrammedAlphaCut at cut
  rcases cut with ⟨out, gamma, sourceDigest, boundary, preDigest, before,
    middle, middleResultDigest, witness⟩
  exact ⟨out, gamma, sourceDigest, boundary, preDigest, before, middle,
    middleResultDigest, witness⟩

#print axioms programmed_alpha_cut_constructs_witness

end
end AspisV8Completion.FSV8ProgrammedAlphaCutWitness
