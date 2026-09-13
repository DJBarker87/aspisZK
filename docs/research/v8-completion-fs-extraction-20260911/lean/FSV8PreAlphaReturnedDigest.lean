import FSV8PreAlphaSuccessDecomposition

/-!
# Successful pre-alpha execution returns its constructed boundary digest

The result pair and the boundary field are not independent.  This leaf makes
that source invariant explicit through the already-proved exact marker
factorization, avoiding any caller-supplied digest coherence premise.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000

namespace AspisV8Completion.FSV8PreAlphaReturnedDigest

open FSOracleExecution FSBoundedTranscript
open FSV8ExecutablePreAlphaFactorization
open FSV8BeforeAlphaMarkerFactorization
open FSV8PreAlphaSuccessDecomposition

noncomputable section

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Block := FSBoundedTranscript.Block
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

/-- The digest returned alongside a successful pre-alpha boundary is exactly
the digest stored in that boundary. -/
theorem successful_preAlpha_returned_digest
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (digest : Block) (tape : Tape) (oracle : Oracle)
    (boundary : PreAlpha out gamma body z) (returnedDigest : Block)
    (success :
      (run tape (preAlphaScript out gamma body z digest) oracle).1 =
        some (.ok boundary, returnedDigest)) :
    returnedDigest = boundary.digest := by
  rcases preAlpha_success_constructs_before_marker_full out gamma body z digest
      tape oracle boundary returnedDigest success with
    ⟨before, _prefixSuccess, continuationFull⟩
  let beforeTranscript : Transcript :=
    { digest := before.digest
      oracle :=
        (run tape (beforeAlphaMarkerScript out gamma body z digest) oracle).2 }
  let afterMarker := absorb tape beforeTranscript 20
    (0 :: FSLiveSelectedMiddleQueryRho.alpha0NonceBytes body)
  have markerRun := run_alphaMarkerContinuation out gamma body z before tape
    beforeTranscript.oracle
  have resultEq := congrArg Prod.fst continuationFull
  simp only [beforeTranscript] at markerRun
  rw [markerRun, success] at resultEq
  have pairEq := Option.some.inj resultEq
  have boundaryEq := Except.ok.inj (congrArg Prod.fst pairEq)
  have digestEq : afterMarker.digest = returnedDigest := by
    exact congrArg Prod.snd pairEq
  have boundaryDigestEq : afterMarker.digest = boundary.digest := by
    exact congrArg PreAlpha.digest boundaryEq
  exact digestEq.symm.trans boundaryDigestEq

#print axioms successful_preAlpha_returned_digest

end
end AspisV8Completion.FSV8PreAlphaReturnedDigest
