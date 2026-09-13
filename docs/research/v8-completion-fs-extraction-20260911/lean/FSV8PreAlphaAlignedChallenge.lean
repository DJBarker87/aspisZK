import FSV8PreAlphaSuccessDecomposition
import FSV8BeforeMarkerAlignedChallenge

/-!
# One successful pre-alpha execution continues into the live alpha challenge

This leaf removes the independently supplied before-marker boundary from the
aligned alpha theorem. The boundary, returned digest, post-marker oracle and
live challenge all come from the same preAlphaScript execution on the same
body. It assigns no probability and does not yet construct pre-alpha success
from the whole selected verifier root.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option maxRecDepth 2600

namespace AspisV8Completion.FSV8PreAlphaAlignedChallenge

open FSOracleExecution FSBoundedTranscript
open FSV8BeforeAlphaMarkerFactorization
open FSV8PreAlphaSuccessDecomposition
open FSV8BeforeMarkerAlignedChallenge
open FSV8ExecutablePreAlphaFactorization
open FSV8V7StateAlignment
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle

noncomputable section

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block
abbrev Tape := FSBoundedTranscript.Tape
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

/-- Success of the existing pre-alpha script and of the live challenge at its
actual final state constructs the complete aligned alpha run. The existential
boundary is recovered from that execution, and the full marker continuation is
retained to prevent a stale-oracle substitution. -/
theorem successful_preAlpha_then_alpha_constructs
    {steps : Nat} {tape : Tape} {finiteTape : FreshAnswerTape Block steps}
    {limits : OracleLimits} {initialV7 : OracleState}
    {initialFS : State Bytes Block}
    {out : OODResult} {gamma : K} {body : Bytes} {z : Fin 10 → K}
    {digest : Block} {boundary : PreAlpha out gamma body z}
    {finalDigest : Block} {values : List K} {limbs : List Nat}
    (initialAligned : StateAligned tape finiteTape initialV7 initialFS)
    (bodyParsed : AspisV8.SameBodyChunkParser.fields
      (body.map UInt8.toFin) = some values)
    (totalRoom : initialV7.totalCalls + beforeAlphaMarkerBudget + 9 ≤
      limits.totalCalls)
    (freshRoom : initialV7.freshCalls + beforeAlphaMarkerBudget + 9 ≤
      limits.freshCalls)
    (tapeRoom : initialFS.next + beforeAlphaMarkerBudget + 9 ≤ steps)
    (preSuccess :
      (run tape (preAlphaScript out gamma body z digest) initialFS).1 =
        some (Except.ok boundary, finalDigest))
    (liveSuccess :
      (FSLiveChallengeTrace.challenge tape
        { digest := finalDigest
          oracle :=
            (run tape (preAlphaScript out gamma body z digest) initialFS).2 }
      ).result = some limbs) :
    ∃ before : BeforeAlphaMarker out gamma body z,
      run tape (alphaMarkerContinuation out gamma body z before)
          (run tape
            (beforeAlphaMarkerScript out gamma body z digest) initialFS).2 =
        run tape (preAlphaScript out gamma body z digest) initialFS ∧
      ConstructedAlphaRun tape finiteTape limits initialV7 initialFS out gamma
        body z digest before limbs := by
  rcases preAlpha_success_constructs_before_marker_full out gamma body z digest
      tape initialFS boundary finalDigest preSuccess with
    ⟨before, prefixSuccess, continuationFull⟩
  let beforeTranscript : FSBoundedTranscript.Transcript :=
    { digest := before.digest
      oracle :=
        (run tape
          (beforeAlphaMarkerScript out gamma body z digest) initialFS).2 }
  let afterMarker := absorb tape beforeTranscript 20
    (0 :: FSLiveSelectedMiddleQueryRho.alpha0NonceBytes body)
  have markerRun := run_alphaMarkerContinuation out gamma body z before tape
    beforeTranscript.oracle
  have continuationResult :
      (run tape (alphaMarkerContinuation out gamma body z before)
        beforeTranscript.oracle).1 =
          some (Except.ok boundary, finalDigest) := by
    change
      (run tape (alphaMarkerContinuation out gamma body z before)
        (run tape
          (beforeAlphaMarkerScript out gamma body z digest) initialFS).2).1 =
            some (Except.ok boundary, finalDigest)
    rw [continuationFull]
    exact preSuccess
  have markerDigestEq : afterMarker.digest = finalDigest := by
    simp only [beforeTranscript] at markerRun
    rw [markerRun] at continuationResult
    exact congrArg Prod.snd (Option.some.inj continuationResult)
  have markerOracleEq :
      afterMarker.oracle =
        (run tape (preAlphaScript out gamma body z digest) initialFS).2 := by
    have stateEq := congrArg Prod.snd continuationFull
    simp only [beforeTranscript] at markerRun
    rw [markerRun] at stateEq
    exact stateEq
  have markerStateEq :
      afterMarker =
        ({ digest := finalDigest
           oracle :=
             (run tape (preAlphaScript out gamma body z digest) initialFS).2 } :
          FSBoundedTranscript.Transcript) := by
    rw [← markerDigestEq, ← markerOracleEq]
  have liveAtMarker :
      (FSLiveChallengeTrace.challenge tape afterMarker).result = some limbs := by
    rw [markerStateEq]
    exact liveSuccess
  have constructed := successful_before_marker_then_alpha_constructs
    initialAligned bodyParsed totalRoom freshRoom tapeRoom prefixSuccess
    (by simpa [afterMarker, beforeTranscript] using liveAtMarker)
  exact ⟨before, continuationFull, constructed⟩

#print axioms successful_preAlpha_then_alpha_constructs

end
end AspisV8Completion.FSV8PreAlphaAlignedChallenge
