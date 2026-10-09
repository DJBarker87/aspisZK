import FSV8SuccessfulMiddlePreAlphaInversion
import FSV8SuccessfulPostAlphaCandidate
import FSV8CandidateScriptLiveBridge
import FSV8PreAlphaReturnedDigest

/-!
# One successful middle run constructs its live alpha execution

This composes the forward source bind inversions with the literal candidate
trace. Boundary, limbs, assembled alpha, candidate final state and the
query/rho continuation are all constructed from one `middleScript` success.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000

namespace AspisV8Completion.FSV8SuccessfulMiddleLiveAlpha

open FSOracleExecution FSBoundedTranscript
open FSNonzeroQM31 FSV7OODSampler
open FSLiveQueryRhoSuffix
open FSLiveSourceFunctionalMiddle
open FSV8ExecutablePreAlphaFactorization
open FSV8SuccessfulMiddlePreAlphaInversion
open FSV8SuccessfulPostAlphaCandidate
open FSV8CandidateScriptLiveBridge
open FSV8PreAlphaReturnedDigest

noncomputable section

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Block := FSBoundedTranscript.Block
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

/-- All source facts at the alpha seam of one middle execution.  This is a
proposition constructed by the theorem below, never an acceptance premise. -/
def LiveAlphaExecution
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (digest : Block) (tape : Tape) (oracle : Oracle)
    (middle : Success out gamma body z) (finalDigest : Block) : Prop :=
  ∃ boundary : PreAlpha out gamma body z, ∃ limbs candidateDigest,
    (run tape (preAlphaScript out gamma body z digest) oracle).1 =
        some (.ok boundary, boundary.digest) ∧
    (run tape (postAlphaScript out gamma body z boundary)
      (run tape (preAlphaScript out gamma body z digest) oracle).2).1 =
        some (.ok middle, finalDigest) ∧
    (run tape (candidateScript boundary.digest)
      (run tape (preAlphaScript out gamma body z digest) oracle).2).1 =
        some (.ok middle.middle.alpha0, candidateDigest) ∧
    (FSLiveChallengeTrace.challenge tape
      { digest := boundary.digest
        oracle :=
          (run tape (preAlphaScript out gamma body z digest) oracle).2 }
    ).result = some limbs ∧
    assemble limbs = some middle.middle.alpha0 ∧
    (FSLiveChallengeTrace.challenge tape
      { digest := boundary.digest
        oracle :=
          (run tape (preAlphaScript out gamma body z digest) oracle).2 }
    ).final =
      { digest := candidateDigest
        oracle :=
          (run tape (candidateScript boundary.digest)
            (run tape (preAlphaScript out gamma body z digest) oracle).2).2 } ∧
    (run tape (queryRhoScript body candidateDigest)
      (run tape (candidateScript boundary.digest)
        (run tape (preAlphaScript out gamma body z digest) oracle).2).2).1 =
        some (.ok (middle.middle.queries, middle.middle.rho), finalDigest)

/-- The live alpha limbs and value arise from the exact candidate sampler in
the post-alpha continuation of the same successful middle execution. -/
theorem successful_middle_constructs_live_alpha
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (digest : Block) (tape : Tape) (oracle : Oracle)
    (middle : Success out gamma body z) (finalDigest : Block)
    (success :
      (run tape (middleScript out gamma body z digest) oracle).1 =
        some (.ok middle, finalDigest)) :
    LiveAlphaExecution out gamma body z digest tape oracle middle finalDigest := by
  rcases successful_middle_constructs_preAlpha out gamma body z digest tape
      oracle middle finalDigest success with
    ⟨boundary, prefixDigest, preSuccess, postSuccess⟩
  have prefixDigestEq : prefixDigest = boundary.digest :=
    successful_preAlpha_returned_digest out gamma body z digest tape oracle
      boundary prefixDigest preSuccess
  have preSuccess' :
      (run tape (preAlphaScript out gamma body z digest) oracle).1 =
        some (.ok boundary, boundary.digest) := by
    simpa [prefixDigestEq] using preSuccess
  rcases successful_postAlpha_constructs_candidate out gamma body z boundary
      tape (run tape (preAlphaScript out gamma body z digest) oracle).2 middle
      finalDigest postSuccess with
    ⟨candidateDigest, candidateSuccess, suffixSuccess⟩
  let start : FSBoundedTranscript.Transcript :=
    { digest := boundary.digest
      oracle :=
        (run tape (preAlphaScript out gamma body z digest) oracle).2 }
  rcases successful_candidateScript_constructs_live tape start
      middle.middle.alpha0 candidateDigest
      (by simpa [start] using candidateSuccess) with
    ⟨limbs, liveSuccess, assembled, finalState⟩
  unfold LiveAlphaExecution
  exact ⟨boundary, limbs, candidateDigest, preSuccess', postSuccess,
    candidateSuccess, by simpa [start] using liveSuccess, assembled,
    by simpa [start] using finalState, suffixSuccess⟩

#print axioms successful_middle_constructs_live_alpha

end
end AspisV8Completion.FSV8SuccessfulMiddleLiveAlpha
