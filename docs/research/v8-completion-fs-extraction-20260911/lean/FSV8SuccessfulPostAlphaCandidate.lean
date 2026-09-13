import FSV8ExecutablePreAlphaFactorization

/-!
# Successful post-alpha execution exposes the actual alpha candidate

This is a deterministic bind inversion.  It does not add freshness or a
probability law: a successful source continuation must have obtained its
recorded `alpha0` from the literal candidate sampler at the boundary digest
and entry oracle used by that same continuation.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000

namespace AspisV8Completion.FSV8SuccessfulPostAlphaCandidate

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSNonzeroQM31
open FSLiveQueryRhoSuffix
open FSLiveSelectedMiddleQueryRho
open FSLiveSourceFunctionalMiddle
open FSV8ExecutablePreAlphaFactorization

noncomputable section

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Block := FSBoundedTranscript.Block
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

/-- Invert the first bind of the real post-alpha continuation.  The candidate
result is constructed from the same run; `alpha0` is identified by equality
of the returned source-success record, not supplied independently. -/
theorem successful_postAlpha_constructs_candidate
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (boundary : PreAlpha out gamma body z) (tape : Tape) (oracle : Oracle)
    (middle : Success out gamma body z) (finalDigest : Block)
    (success :
      (run tape (postAlphaScript out gamma body z boundary) oracle).1 =
        some (.ok middle, finalDigest)) :
    ∃ candidateDigest,
      (run tape (candidateScript boundary.digest) oracle).1 =
        some (.ok middle.middle.alpha0, candidateDigest) ∧
      (run tape (queryRhoScript body candidateDigest)
        (run tape (candidateScript boundary.digest) oracle).2).1 =
        some (.ok (middle.middle.queries, middle.middle.rho), finalDigest) := by
  unfold postAlphaScript at success
  rw [run_bind] at success
  cases candidateRun : (run tape (candidateScript boundary.digest) oracle).1 with
  | none => simp [candidateRun] at success
  | some candidateValue =>
      rcases candidateValue with ⟨candidateResult, candidateDigest⟩
      cases candidateResult with
      | error error => simp [candidateRun, run] at success
      | ok alpha0 =>
          simp only [candidateRun] at success
          rw [run_bind] at success
          cases suffixRun :
              (run tape (queryRhoScript body candidateDigest)
                (run tape (candidateScript boundary.digest) oracle).2).1 with
          | none => simp [suffixRun] at success
          | some suffixValue =>
              rcases suffixValue with ⟨suffixResult, suffixDigest⟩
              cases suffixResult with
              | error error => simp [suffixRun, run] at success
              | ok pair =>
                  rcases pair with ⟨queries, rho⟩
                  simp only [suffixRun, run] at success
                  have same := Option.some.inj success
                  have sourceSame := Except.ok.inj (congrArg Prod.fst same)
                  have alphaSame : alpha0 = middle.middle.alpha0 := by
                    exact congrArg
                      (fun s : Success out gamma body z => s.middle.alpha0)
                      sourceSame
                  have queriesSame : queries = middle.middle.queries := by
                    exact congrArg
                      (fun s : Success out gamma body z => s.middle.queries)
                      sourceSame
                  have rhoSame : rho = middle.middle.rho := by
                    exact congrArg
                      (fun s : Success out gamma body z => s.middle.rho)
                      sourceSame
                  have digestSame : suffixDigest = finalDigest := by
                    exact congrArg Prod.snd same
                  refine ⟨candidateDigest, ?_, ?_⟩
                  · simpa [alphaSame] using candidateRun
                  · simpa [queriesSame, rhoSame, digestSame] using suffixRun

#print axioms successful_postAlpha_constructs_candidate

end
end AspisV8Completion.FSV8SuccessfulPostAlphaCandidate
