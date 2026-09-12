import FSV8AlphaChallengeInputBridge
import FSLiveSourceFunctionalMiddle

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 250000

namespace AspisV8Completion.FSLiveAlphaBoundary

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSNonzeroQM31 FSLiveNonzeroV7Decode
open FSLiveQueryRhoSuffix FSLiveSelectedMiddleQueryRho
open SameBodyFunctionalProducerSource
open FSLiveSourceFunctionalMiddle
open FSV8AlphaChallengeInputBridge

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Block := FSBoundedTranscript.Block
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

noncomputable section

def alphaBoundary (out : OODResult) (gamma : K) (body : Bytes)
    (z : Fin 10 → K) (digest : Block) (tape : Tape) (oracle : Oracle)
    (success : Success out gamma body z) : FSBoundedTranscript.Transcript :=
  let afterInactive := absorb tape ⟨digest, oracle⟩ 50 (inactiveClaimBytes body)
  let kappaDraw := nonzero tape 3 afterInactive
  let afterDescription :=
    absorb tape kappaDraw.2 1 success.functional.description
  let afterClaim := absorb tape afterDescription 6 success.functional.claim
  let afterImageProfile :=
    absorb tape afterClaim 1 compactFunctionalProfile
  let tauDraw := nonzero tape 3 afterImageProfile
  let afterResponse0 :=
    absorb tape tauDraw.2 52 (0 :: response0Bytes body)
  absorb tape afterResponse0 20 (0 :: alpha0NonceBytes body)

theorem successful_alpha_boundary (out : OODResult) (gamma : K) (body : Bytes)
    (z : Fin 10 → K) (digest : Block) (tape : Tape) (oracle : Oracle)
    (success : Success out gamma body z) (finalDigest : Block)
    (accepted :
      (run tape (middleScript out gamma body z digest) oracle).1 =
        some (Except.ok success, finalDigest)) :
    (run tape (candidateScript
      (alphaBoundary out gamma body z digest tape oracle success).digest)
      (alphaBoundary out gamma body z digest tape oracle success).oracle).1 =
        some (.ok success.middle.alpha0,
          (candidate tape (alphaBoundary out gamma body z digest tape oracle success)).2.digest) ∧
      (run tape (candidateScript
        (alphaBoundary out gamma body z digest tape oracle success).digest)
        (alphaBoundary out gamma body z digest tape oracle success).oracle).2 =
          (candidate tape (alphaBoundary out gamma body z digest tape oracle success)).2.oracle ∧
      ∃ event,
        event.input = alphaCandidateInput
          (alphaBoundary out gamma body z digest tape oracle success) ∧
        event ∈ (run tape (candidateScript
          (alphaBoundary out gamma body z digest tape oracle success).digest)
          (alphaBoundary out gamma body z digest tape oracle success).oracle).2.log := by
  unfold middleScript at accepted
  rw [run_bind] at accepted
  have initialAbsorb := run_absorb tape
    ({ digest := digest, oracle := oracle } : FSBoundedTranscript.Transcript)
    50 (inactiveClaimBytes body)
  rw [initialAbsorb] at accepted
  simp only [Prod.fst, Prod.snd] at accepted
  rw [run_bind, run_nonzero] at accepted
  simp only [Prod.fst, Prod.snd] at accepted
  split at accepted
  · simp [run] at accepted
  · split at accepted
    · simp [run] at accepted
    · unfold afterFunctionalScript at accepted
      rw [run_bind, run_absorb] at accepted
      simp only [Prod.fst, Prod.snd] at accepted
      rw [run_bind, run_absorb] at accepted
      simp only [Prod.fst, Prod.snd] at accepted
      rw [run_bind, run_absorb] at accepted
      simp only [Prod.fst, Prod.snd] at accepted
      rw [run_bind, run_nonzero] at accepted
      simp only [Prod.fst, Prod.snd] at accepted
      split at accepted
      · simp [run] at accepted
      · rw [run_bind, run_absorb] at accepted
        simp only [Prod.fst, Prod.snd] at accepted
        rw [run_bind, run_absorb] at accepted
        simp only [Prod.fst, Prod.snd] at accepted
        let boundary := alphaBoundary out gamma body z digest tape oracle success
        generalize boundaryStateEq : absorb tape _ 20
          (0 :: alpha0NonceBytes body) = afterAlphaNonce at accepted
        rw [run_bind, run_candidate] at accepted
        simp only [Prod.fst, Prod.snd] at accepted
        cases alphaResultEq : (candidate tape afterAlphaNonce).1 with
        | error e =>
            rw [alphaResultEq] at accepted
            simp [run] at accepted
        | ok alpha0 =>
            rw [alphaResultEq] at accepted
            rw [run_bind] at accepted
            cases suffixRun :
                (run tape (queryRhoScript body (candidate tape afterAlphaNonce).2.digest)
                  (candidate tape afterAlphaNonce).2.oracle).1 with
            | none => simp [suffixRun] at accepted
            | some suffixValue =>
              rcases suffixValue with ⟨suffixResult, suffixDigest⟩
              cases suffixResult with
              | error e => simp [suffixRun, run] at accepted
              | ok pair =>
                rcases pair with ⟨queries, rho⟩
                simp only [suffixRun, run] at accepted
                have same := Option.some.inj accepted
                have resultSame := congrArg Prod.fst same
                have sourceSame := Except.ok.inj resultSame
                have alphaSame : alpha0 = success.middle.alpha0 := by
                  exact congrArg
                    (fun s : Success out gamma body z => s.middle.alpha0)
                    sourceSame
                have functionalSame := congrArg
                  (fun s : Success out gamma body z => s.functional)
                  sourceSame
                simp only at functionalSame
                have boundaryState : afterAlphaNonce = boundary := by
                  dsimp [boundary, alphaBoundary]
                  rw [← boundaryStateEq]
                  rw [functionalSame]
                have boundaryDef : boundary =
                    alphaBoundary out gamma body z digest tape oracle success := rfl
                rw [← boundaryDef]
                rw [← boundaryState]
                constructor
                · rw [run_candidate]
                  simp [alphaResultEq, alphaSame]
                constructor
                · exact congrArg Prod.snd (run_candidate tape afterAlphaNonce)
                · exact alpha_candidate_query_mem tape afterAlphaNonce

#print axioms successful_alpha_boundary

end
end AspisV8Completion.FSLiveAlphaBoundary
