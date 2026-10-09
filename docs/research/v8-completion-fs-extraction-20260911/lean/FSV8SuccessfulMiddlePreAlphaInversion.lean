import FSV8ExecutablePreAlphaFactorization

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000

namespace AspisV8Completion.FSV8SuccessfulMiddlePreAlphaInversion
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8ExecutablePreAlphaFactorization
open FSLiveSourceFunctionalMiddle

noncomputable section

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Block := FSBoundedTranscript.Block
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

/-- A successful original middle run is first transported to the structurally
   equal factored run, then inverted at its explicit pre-alpha bind.  The
   returned boundary and the continuation state are both retained. -/
theorem successful_middle_constructs_preAlpha
    (out : OODResult) (gamma : K) (body : Bytes) (z : Fin 10 → K)
    (digest : Block) (tape : Tape) (oracle : Oracle)
    (middle : Success out gamma body z) (finalDigest : Block)
    (success :
      (run tape (middleScript out gamma body z digest) oracle).1 =
        some (.ok middle, finalDigest)) :
    ∃ boundary : PreAlpha out gamma body z, ∃ prefixDigest,
      (run tape (preAlphaScript out gamma body z digest) oracle).1 =
          some (.ok boundary, prefixDigest) ∧
      (run tape (postAlphaScript out gamma body z boundary)
        (run tape (preAlphaScript out gamma body z digest) oracle).2).1 =
          some (.ok middle, finalDigest) := by
  have factored :
      (run tape (factoredMiddleScript out gamma body z digest) oracle).1 =
        some (.ok middle, finalDigest) := by
    rw [run_factoredMiddleScript_eq_middleScript]
    exact success
  unfold factoredMiddleScript at factored
  rw [run_bind] at factored
  cases prefixRun :
      (run tape (preAlphaScript out gamma body z digest) oracle) with
  | mk result prefixOracle =>
      cases result with
      | none => simp [prefixRun] at factored
      | some value =>
          rcases value with ⟨prefixResult, prefixDigest⟩
          cases prefixResult with
          | error e => simp [prefixRun, run] at factored
          | ok boundary =>
              refine ⟨boundary, prefixDigest, ?_, ?_⟩
              · simpa [prefixRun]
              · simpa [prefixRun] using factored

end
end AspisV8Completion.FSV8SuccessfulMiddlePreAlphaInversion
