import FSV8BeforeAlphaMarkerFactorization

/-!
# Successful existing pre-alpha execution exposes the before-marker cut

The one-query-earlier factorization is useful only if success of the existing
`preAlphaScript` constructs success of its prefix.  This leaf performs that
bind inversion.  It retains the exact same body and the exact oracle state
returned by the prefix; no boundary is supplied independently.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

namespace AspisV8Completion.FSV8PreAlphaSuccessDecomposition

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8BeforeAlphaMarkerFactorization
open FSV8ExecutablePreAlphaFactorization

noncomputable section

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Block := FSBoundedTranscript.Block
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

/-- Success of the existing prefix constructs the exact successful
before-marker execution and the exact one-query marker continuation. -/
theorem preAlpha_success_constructs_before_marker
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (digest : Block) (tape : Tape) (oracle : Oracle)
    (boundary : PreAlpha out gamma body z) (finalDigest : Block)
    (success :
      (run tape (preAlphaScript out gamma body z digest) oracle).1 =
        some (Except.ok boundary, finalDigest)) :
    ∃ before : BeforeAlphaMarker out gamma body z,
      (run tape (beforeAlphaMarkerScript out gamma body z digest) oracle).1 =
          some (Except.ok before, before.digest) ∧
        (run tape (alphaMarkerContinuation out gamma body z before)
          (run tape (beforeAlphaMarkerScript out gamma body z digest) oracle).2).1 =
            some (Except.ok boundary, finalDigest) := by
  have factored :
      (run tape (factoredPreAlphaScript out gamma body z digest) oracle).1 =
        some (Except.ok boundary, finalDigest) := by
    rw [run_factoredPreAlphaScript_eq_preAlphaScript]
    exact success
  unfold factoredPreAlphaScript at factored
  rw [run_bind] at factored
  cases prefixResult :
      (run tape (beforeAlphaMarkerScript out gamma body z digest) oracle).1 with
  | none => simp [prefixResult] at factored
  | some value =>
      rcases value with ⟨result, returnedDigest⟩
      cases result with
      | error e => simp [prefixResult, FSOracleExecution.run] at factored
      | ok before =>
          have returnedDigestEq : returnedDigest = before.digest :=
            successful_beforeAlphaMarker_digest out gamma body z digest tape
              oracle before returnedDigest prefixResult
          subst returnedDigest
          refine ⟨before, ?_, ?_⟩
          · rfl
          · simpa [prefixResult] using factored

/-- The same decomposition retains the complete post-marker interpreter
state, not only its returned value.  This is the continuity fact needed to
start the live alpha challenge from the very same successful execution. -/
theorem preAlpha_success_constructs_before_marker_full
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (digest : Block) (tape : Tape) (oracle : Oracle)
    (boundary : PreAlpha out gamma body z) (finalDigest : Block)
    (success :
      (run tape (preAlphaScript out gamma body z digest) oracle).1 =
        some (Except.ok boundary, finalDigest)) :
    ∃ before : BeforeAlphaMarker out gamma body z,
      (run tape (beforeAlphaMarkerScript out gamma body z digest) oracle).1 =
          some (Except.ok before, before.digest) ∧
        run tape (alphaMarkerContinuation out gamma body z before)
            (run tape
              (beforeAlphaMarkerScript out gamma body z digest) oracle).2 =
          run tape (preAlphaScript out gamma body z digest) oracle := by
  rcases preAlpha_success_constructs_before_marker out gamma body z digest
      tape oracle boundary finalDigest success with
    ⟨before, prefixSuccess, continuationSuccess⟩
  have fullFactor :=
    run_factoredPreAlphaScript_eq_preAlphaScript out gamma body z digest tape
      oracle
  unfold factoredPreAlphaScript at fullFactor
  rw [run_bind] at fullFactor
  simp only [prefixSuccess] at fullFactor
  exact ⟨before, prefixSuccess, fullFactor⟩

#print axioms preAlpha_success_constructs_before_marker
#print axioms preAlpha_success_constructs_before_marker_full

end
end AspisV8Completion.FSV8PreAlphaSuccessDecomposition
