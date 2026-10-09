import FSLiveChallengeTrace
import FSNonzeroQM31

/-!
# Successful candidate script exposes the live challenge

This leaf connects one successful execution of the actual
`FSNonzeroQM31.candidateScript` to the instrumented live challenge on the same
tape and starting transcript.  It is deterministic: cache hits and the exact
final oracle are retained, and no freshness or probability claim is made.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSV8CandidateScriptLiveBridge

open FSOracleExecution FSBoundedTranscript FSLiveChallengeTrace
open FSNonzeroQM31 FSV7OODSampler

abbrev Tape := FSBoundedTranscript.Tape
abbrev K := FSNonzeroQM31.K

/-- A successful candidate script was produced by concrete limbs of the live
challenge, assembled to exactly the returned field element.  Its recorded
final transcript is exactly the script's returned digest and final oracle. -/
theorem successful_candidateScript_constructs_live
    (tape : Tape) (start : Transcript) (value : K) (finalDigest : Block)
    (success :
      (run tape (candidateScript start.digest) start.oracle).1 =
        some (.ok value, finalDigest)) :
    exists limbs,
      (FSLiveChallengeTrace.challenge tape start).result = some limbs /\
      assemble limbs = some value /\
      (FSLiveChallengeTrace.challenge tape start).final =
        { digest := finalDigest
          oracle := (run tape
            (candidateScript start.digest) start.oracle).2 } := by
  have sourceSuccess :
      (candidate tape start).1 = .ok value /\
        (candidate tape start).2.digest = finalDigest := by
    rw [run_candidate] at success
    simpa using Option.some.inj success
  have finalOracle :
      (run tape (candidateScript start.digest) start.oracle).2 =
        (candidate tape start).2.oracle := by
    exact congrArg Prod.snd (run_candidate tape start)
  have erased := FSLiveChallengeTrace.challenge_erase tape start
  simp only [candidate] at sourceSuccess
  cases sampled : (FSBoundedTranscript.challenge tape start).1 with
  | none => simp [sampled] at sourceSuccess
  | some limbs =>
      cases assembled : assemble limbs with
      | none => simp [sampled, assembled] at sourceSuccess
      | some assembledValue =>
          have valueEq : assembledValue = value := by
            simpa [sampled, assembled] using sourceSuccess.1
          subst assembledValue
          refine ⟨limbs, ?_, assembled, ?_⟩
          · rw [erased.1, sampled]
          · have digestEq :
                (FSLiveChallengeTrace.challenge tape start).final.digest =
                  finalDigest := by
              rw [erased.2]
              simpa [sampled, assembled] using sourceSuccess.2
            have oracleEq :
                (FSLiveChallengeTrace.challenge tape start).final.oracle =
                  (run tape
                    (candidateScript start.digest) start.oracle).2 := by
              rw [erased.2, finalOracle]
              simp [candidate, sampled, assembled]
            cases traced : (FSLiveChallengeTrace.challenge tape start).final with
            | mk digest oracle =>
                simp only [traced] at digestEq oracleEq
                subst digest
                subst oracle
                rfl

#print axioms successful_candidateScript_constructs_live

end AspisV8Completion.FSV8CandidateScriptLiveBridge
