import FSV8ProgrammedWholePrefixCut
import FSV8ProgrammedPrefixMiddleCut
import FSV8ProgrammedMiddleContinuationCut
import FSV8ProgrammedMiddlePreAlphaCut
import FSV8ProgrammedBeforeAlphaMarkerCut

/-!
# Accepted factored whole verifier constructs its programmed alpha cut

This composes the source-shaped operational cuts into one theorem.  The
source/OOD/gamma values, pre-alpha boundary and before-marker boundary are all
produced by the same normally returned compiled verifier execution.  The
conclusion retains the exact body, initial state, residual fuel and finite-tape
alignment needed by the alpha target/disposition analysis.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 2600

namespace AspisV8Completion.FSV8ProgrammedWholeAlphaCut

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

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev Point := FSV8PostOODGammaScript.Point
abbrev K := FSNonzeroQM31.K

/-- The source-shaped alpha cut exposed by one whole verifier execution.  All
states in the predicate are computed from the same entry state and body. -/
def ProgrammedAlphaCut
    {steps : Nat} {tape : Tape}
    (finiteTape : FreshAnswerTape Block steps)
    (limits : OracleLimits) (actor : QueryActor)
    {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (z : Fin 10 → K) (body : Bytes) (digest : Block)
    (v7 : OracleState) (fs : State Bytes Block) (fuel : Nat) : Prop :=
  ∃ out gamma sourceDigest boundary preDigest,
    ∃ before : BeforeAlphaMarker out gamma body z,
    ∃ middle : Success out gamma body z, ∃ middleResultDigest,
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

/-- A normally returned accepted factored verifier constructs the exact
programmed before-alpha marker cut on its own body and master tape. -/
theorem returned_factoredWhole_constructs_programmed_alpha_cut
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
    ProgrammedAlphaCut (tape := tape) finiteTape limits actor firstWork
      secondWork z body digest v7 fs fuel := by
  unfold ProgrammedAlphaCut
  obtain ⟨staged, middleDigest, wholePrefixReturned, _suffixReturned,
      _wholePrefixFunctional, _wholePrefixAligned⟩ :=
    returned_factoredWhole_constructs_prefixMiddle_cut limits actor firstWork
      secondWork z cuts body digest v7 fs fuel record finalDigest aligned success
  obtain ⟨out, gamma, sourceDigest, sourceReturned,
      middleContinuationReturned, sourceFunctional, sourceAligned⟩ :=
    returned_factoredPrefixMiddle_constructs_source_cut limits actor firstWork
      secondWork z body digest v7 fs fuel staged middleDigest aligned
      wholePrefixReturned
  let sourceRun := runMachine (controllerFromFreshAnswerTape finiteTape)
    limits actor fuel v7
    (compileScript (sourceThenGammaScript firstWork secondWork body digest))
  let middleFuel := fuel - sourceRun.steps
  let middleV7 := sourceRun.oracle
  let middleFS :=
    (run tape (sourceThenGammaScript firstWork secondWork body digest) fs).2
  obtain ⟨middle, middleResultDigest, middleReturned, _wrapperReturned,
      _middleFunctional, _middleAligned⟩ :=
    returned_factoredMiddleContinuationAt_constructs_middle_cut limits actor
      body z out gamma sourceDigest middleV7 middleFS middleFuel staged
      middleDigest sourceAligned middleContinuationReturned
  obtain ⟨boundary, preDigest, preReturned, postAlphaReturned,
      _preFunctional, _preAligned⟩ :=
    returned_factoredMiddle_constructs_preAlpha_cut limits actor out gamma body
      z sourceDigest middleV7 middleFS middleFuel middle middleResultDigest
      sourceAligned middleReturned
  obtain ⟨before, markerReturned, markerContinuationReturned,
      markerFunctional, markerAligned, markerContinuationFunctional,
      afterMarkerAligned⟩ :=
    returned_preAlpha_constructs_programmed_marker_cut limits actor out gamma
      body z sourceDigest middleV7 middleFS middleFuel boundary preDigest
      sourceAligned preReturned
  exact ⟨out, gamma, sourceDigest, boundary, preDigest, before, middle,
    middleResultDigest,
    sourceReturned, sourceFunctional, preReturned, markerReturned,
    markerContinuationReturned, postAlphaReturned, markerFunctional, markerAligned,
    markerContinuationFunctional, afterMarkerAligned⟩

#print axioms returned_factoredWhole_constructs_programmed_alpha_cut
#print axioms ProgrammedAlphaCut

end
end AspisV8Completion.FSV8ProgrammedWholeAlphaCut
