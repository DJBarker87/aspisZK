import FSLiveChallengeV7Decode
import FSNonzeroQM31

/-!
# The live nonzero-QM31 retry run routes through the V7 ordinary decoder

This file instruments the actual `FSNonzeroQM31.nonzero` control flow with
the exact lazy challenge traces proved in `FSLiveChallengeTrace`.  The total
function retains limb exhaustion, assembly failure, zero exhaustion, and
zero retries.  The success theorem exposes a chronological list consisting
of zero candidates followed by one nonzero candidate, and proves that every
candidate in that list is decoded by the V7 ordinary prefix decoder from its
actual one-to-four squeeze blocks.

No freshness, independence, distribution, or probability claim is made.
-/

set_option autoImplicit false

namespace AspisV8Completion.FSLiveNonzeroV7Decode

open AspisV8Completion.FSLiveChallengeTrace
open AspisV8Completion.FSNonzeroQM31
open AspisV8Completion.FSV7OODSampler
open AspisK1.V7Tag73SamplerDecoder

abbrev Tape := AspisV8Completion.FSBoundedTranscript.Tape
abbrev Transcript := AspisV8Completion.FSBoundedTranscript.Transcript

structure CandidateTrace where
  challenge : ChallengeTrace
  result : Except FSNonzeroQM31.Error FSNonzeroQM31.K

def candidateTrace (tape : Tape) (start : Transcript) : CandidateTrace :=
  let traced := FSLiveChallengeTrace.challenge tape start
  let result := match traced.result with
    | none => Except.error FSNonzeroQM31.Error.limbExhausted
    | some valuesList => match assemble valuesList with
      | none => Except.error FSNonzeroQM31.Error.assemblyFailure
      | some value => Except.ok value
  ⟨traced, result⟩

structure NonzeroTrace where
  result : Except FSNonzeroQM31.Error FSNonzeroQM31.K
  final : Transcript
  attempts : List CandidateTrace

/-- Total source-shaped retry instrumentation.  A failed candidate aborts;
only an assembled zero proceeds to the next outer attempt. -/
def nonzeroTrace (tape : Tape) : Nat → Transcript → NonzeroTrace
  | 0, start => ⟨Except.error FSNonzeroQM31.Error.zeroExhausted, start, []⟩
  | n + 1, start =>
      let first := candidateTrace tape start
      match first.result with
      | .error error => ⟨Except.error error, first.challenge.final, [first]⟩
      | .ok value =>
          if value = 0 then
            let rest := nonzeroTrace tape n
              ⟨first.challenge.final.digest, first.challenge.final.oracle⟩
            ⟨rest.result, rest.final, first :: rest.attempts⟩
          else ⟨Except.ok value,
            ⟨first.challenge.final.digest, first.challenge.final.oracle⟩, [first]⟩

theorem candidateTrace_exact (tape : Tape) (start : Transcript) :
    (candidateTrace tape start).result = (FSNonzeroQM31.candidate tape start).1 ∧
      (candidateTrace tape start).challenge.final =
        (FSNonzeroQM31.candidate tape start).2 := by
  have erased := FSLiveChallengeTrace.challenge_erase tape start
  constructor
  · simp only [candidateTrace, FSNonzeroQM31.candidate]
    rw [erased.1]
    cases sampled : (AspisV8Completion.FSBoundedTranscript.challenge tape start).1 with
    | none => simp [sampled]
    | some valuesList =>
        cases assembled : assemble valuesList <;> simp [sampled, assembled]
  · simp only [candidateTrace, FSNonzeroQM31.candidate]
    rw [erased.2]
    cases sampled : (AspisV8Completion.FSBoundedTranscript.challenge tape start).1 with
    | none => simp [sampled]
    | some valuesList =>
        cases assembled : assemble valuesList <;> simp [sampled, assembled]

/-- Erasing all attempt records gives the exact existing total nonzero run,
including every failure and early stop. -/
theorem nonzeroTrace_exact (tape : Tape) : ∀ n start,
    (nonzeroTrace tape n start).result =
        (FSNonzeroQM31.nonzero tape n start).1 ∧
      (nonzeroTrace tape n start).final =
        (FSNonzeroQM31.nonzero tape n start).2 := by
  intro n
  induction n with
  | zero => intro start; exact ⟨rfl, rfl⟩
  | succ n ih =>
      intro start
      have firstExact := candidateTrace_exact tape start
      simp only [nonzeroTrace, FSNonzeroQM31.nonzero]
      rw [← firstExact.1, ← firstExact.2]
      cases (candidateTrace tape start).result with
      | error error =>
          simp
      | ok value =>
          by_cases zero : value = 0
          · simp only [if_pos zero]
            simpa using ih (candidateTrace tape start).challenge.final
          · simp [zero]

/-- The instrumented total trace is the actual `nonzeroScript` interpreter
result, including its final digest, cache/log state, and every abort branch. -/
theorem run_nonzeroScript_trace (tape : Tape) (n : Nat)
    (start : Transcript) :
    AspisV8Completion.FSOracleExecution.run tape
        (FSNonzeroQM31.nonzeroScript n start.digest) start.oracle =
      (some ((nonzeroTrace tape n start).result,
        (nonzeroTrace tape n start).final.digest),
        (nonzeroTrace tape n start).final.oracle) := by
  rw [FSNonzeroQM31.run_nonzero]
  obtain ⟨resultEq, finalEq⟩ := nonzeroTrace_exact tape n start
  rw [resultEq, finalEq]

inductive SuccessfulAttempts (gamma : FSNonzeroQM31.K) :
    List CandidateTrace → Prop
  | final (attempt : CandidateTrace)
      (result : attempt.result = Except.ok gamma)
      (nonzero : gamma ≠ 0) : SuccessfulAttempts gamma [attempt]
  | retry (attempt : CandidateTrace) (rest : List CandidateTrace)
      (zero : attempt.result = Except.ok 0)
      (tail : SuccessfulAttempts gamma rest) :
      SuccessfulAttempts gamma (attempt :: rest)

inductive ChronologicalAttempts (tape : Tape) :
    Transcript → List CandidateTrace → Transcript → Prop
  | nil (start : Transcript) : ChronologicalAttempts tape start [] start
  | cons (start : Transcript) (attempt : CandidateTrace)
      (rest : List CandidateTrace) (final : Transcript)
      (actual : attempt = candidateTrace tape start)
      (tail : ChronologicalAttempts tape
        ⟨attempt.challenge.final.digest, attempt.challenge.final.oracle⟩
        rest final) :
      ChronologicalAttempts tape start (attempt :: rest) final

theorem nonzeroTrace_chronological (tape : Tape) : ∀ n start,
    ChronologicalAttempts tape start (nonzeroTrace tape n start).attempts
      (nonzeroTrace tape n start).final := by
  intro n
  induction n with
  | zero => intro start; exact ChronologicalAttempts.nil start
  | succ n ih =>
      intro start
      simp only [nonzeroTrace]
      cases firstResult : (candidateTrace tape start).result with
      | error error =>
          simp only
          exact ChronologicalAttempts.cons start (candidateTrace tape start) []
            _ rfl (ChronologicalAttempts.nil _)
      | ok value =>
          simp only
          by_cases zero : value = 0
          · simp only [if_pos zero]
            exact ChronologicalAttempts.cons start (candidateTrace tape start)
              _ _ rfl (ih _)
          · simp only [if_neg zero]
            exact ChronologicalAttempts.cons start (candidateTrace tape start) []
              _ rfl (ChronologicalAttempts.nil _)

theorem nonzeroTrace_successfulAttempts (tape : Tape) : ∀ n start gamma,
    (nonzeroTrace tape n start).result = Except.ok gamma →
      SuccessfulAttempts gamma (nonzeroTrace tape n start).attempts := by
  intro n
  induction n with
  | zero => intro start gamma success; cases success
  | succ n ih =>
      intro start gamma success
      simp only [nonzeroTrace] at success ⊢
      cases firstResult : (candidateTrace tape start).result with
      | error error =>
          simp [firstResult] at success
      | ok value =>
          by_cases zero : value = 0
          · simp [firstResult, zero] at success ⊢
            exact SuccessfulAttempts.retry _ _ (firstResult.trans (by rw [zero]))
              (ih _ gamma success)
          · simp [firstResult, zero] at success ⊢
            have valueEq : value = gamma := success
            subst value
            exact SuccessfulAttempts.final _ firstResult zero

def V7DecodedAttempt (attempt : CandidateTrace) : Prop :=
  ∃ limbs value,
    attempt.challenge.result = some limbs ∧
      assemble limbs = some value ∧
      attempt.result = Except.ok value ∧
      decodeOrdinaryPrefix attempt.challenge.blocks =
        some { value := encodeQm31Limbs limbs
               limbs := limbs
               wordsUsed := attempt.challenge.draws
               blocksUsed := attempt.challenge.blocks.length
               remainingBlocks := [] }

theorem candidateTrace_ok_v7Decoded (tape : Tape) (start : Transcript)
    (value : FSNonzeroQM31.K)
    (success : (candidateTrace tape start).result = Except.ok value) :
    V7DecodedAttempt (candidateTrace tape start) := by
  simp only [candidateTrace] at success ⊢
  cases sampled : (FSLiveChallengeTrace.challenge tape start).result with
  | none =>
      simp only [sampled] at success
      cases success
  | some valuesList =>
      simp only [sampled] at success ⊢
      cases assembled : assemble valuesList with
      | none =>
          simp only [assembled] at success
          cases success
      | some assembledValue =>
          simp only [assembled, Except.ok.injEq] at success
          subst assembledValue
          refine ⟨valuesList, value, sampled, assembled, rfl, ?_⟩
          exact AspisV8Completion.FSLiveChallengeV7Decode.challenge_decodeOrdinaryPrefix
            tape start valuesList sampled

theorem successful_chronological_all_v7Decoded (tape : Tape)
    {start final : Transcript} {gamma : FSNonzeroQM31.K}
    {attempts : List CandidateTrace}
    (chronological : ChronologicalAttempts tape start attempts final)
    (successful : SuccessfulAttempts gamma attempts) :
    ∀ attempt ∈ attempts, V7DecodedAttempt attempt := by
  induction chronological with
  | nil current => cases successful
  | cons current first rest final actual tail ih =>
      subst first
      cases successful with
      | final attempt result nonzero =>
          intro queried member
          simp only [List.mem_singleton] at member
          subst queried
          exact candidateTrace_ok_v7Decoded tape current gamma result
      | retry attempt remaining zero successfulTail =>
          intro queried member
          simp only [List.mem_cons] at member
          cases member with
          | inl head =>
              subst queried
              exact candidateTrace_ok_v7Decoded tape current 0 zero
          | inr later => exact ih successfulTail queried later

/- The final all-attempt decoder theorem is stated with the chronological
producer, so no caller-supplied attempt is accepted merely from list
membership. -/
theorem successful_nonzero_live_v7 (tape : Tape) (n : Nat)
    (start : Transcript) (gamma : FSNonzeroQM31.K)
    (success : (nonzeroTrace tape n start).result = Except.ok gamma) :
    SuccessfulAttempts gamma (nonzeroTrace tape n start).attempts ∧
      ChronologicalAttempts tape start (nonzeroTrace tape n start).attempts
        (nonzeroTrace tape n start).final :=
  ⟨nonzeroTrace_successfulAttempts tape n start gamma success,
    nonzeroTrace_chronological tape n start⟩

theorem successful_nonzero_all_attempts_v7Decoded (tape : Tape) (n : Nat)
    (start : Transcript) (gamma : FSNonzeroQM31.K)
    (success : (nonzeroTrace tape n start).result = Except.ok gamma) :
    ∀ attempt ∈ (nonzeroTrace tape n start).attempts,
      V7DecodedAttempt attempt := by
  exact successful_chronological_all_v7Decoded tape
    (nonzeroTrace_chronological tape n start)
    (nonzeroTrace_successfulAttempts tape n start gamma success)

/-- A successful actual script execution therefore has the exact live
zero-retry/nonzero-final trace, and every attempt routes through the V7
ordinary decoder. -/
theorem successful_nonzeroScript_all_attempts_v7Decoded (tape : Tape)
    (n : Nat) (start : Transcript) (gamma : FSNonzeroQM31.K)
    (finalDigest : AspisV8Completion.FSBoundedTranscript.Block)
    (success : (AspisV8Completion.FSOracleExecution.run tape
      (FSNonzeroQM31.nonzeroScript n start.digest) start.oracle).1 =
        some (Except.ok gamma, finalDigest)) :
    (nonzeroTrace tape n start).result = Except.ok gamma ∧
      (nonzeroTrace tape n start).final.digest = finalDigest ∧
      ∀ attempt ∈ (nonzeroTrace tape n start).attempts,
        V7DecodedAttempt attempt := by
  have exactRun := congrArg Prod.fst (run_nonzeroScript_trace tape n start)
  rw [success] at exactRun
  have pairEq := Option.some.inj exactRun.symm
  have gammaEq : (nonzeroTrace tape n start).result = Except.ok gamma :=
    congrArg Prod.fst pairEq
  have digestEq : (nonzeroTrace tape n start).final.digest = finalDigest :=
    congrArg Prod.snd pairEq
  exact ⟨gammaEq, digestEq,
    successful_nonzero_all_attempts_v7Decoded tape n start gamma gammaEq⟩

#print axioms candidateTrace_exact
#print axioms nonzeroTrace_exact
#print axioms run_nonzeroScript_trace
#print axioms nonzeroTrace_chronological
#print axioms nonzeroTrace_successfulAttempts
#print axioms candidateTrace_ok_v7Decoded
#print axioms successful_nonzero_live_v7
#print axioms successful_nonzero_all_attempts_v7Decoded
#print axioms successful_nonzeroScript_all_attempts_v7Decoded

end AspisV8Completion.FSLiveNonzeroV7Decode
