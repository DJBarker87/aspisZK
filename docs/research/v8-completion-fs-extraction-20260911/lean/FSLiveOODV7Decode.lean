import FSLiveChallengeV7Decode
import FSV7OODSampler

/-!
# Live V8 OOD retries route through the V7 ordinary decoder

Deterministic instrumentation of the actual first-point `circleScript` and
distinct-second-point `distinctScript`.  Limb exhaustion, parameter rejection,
equal-point rejection, both exhaustion modes, cache/log state, and exact final
transcripts are retained.  No uniformity or freshness claim is made.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSLiveOODV7Decode

open AspisV8Completion.FSLiveChallengeTrace
open AspisV8Completion.FSOODSampler
open AspisV8Completion.FSV7OODSampler
open AspisK1.V7Tag73SamplerDecoder

abbrev Tape := AspisV8Completion.FSBoundedTranscript.Tape
abbrev Transcript := AspisV8Completion.FSBoundedTranscript.Transcript
abbrev Point := AspisK1.V7Tag73DeterministicRefinement.SecureCirclePointBytes

structure CircleAttempt where
  challenge : ChallengeTrace
  decoded : Option Point

def circleAttempt (tape : Tape) (start : Transcript) : CircleAttempt :=
  let traced := FSLiveChallengeTrace.challenge tape start
  ⟨traced, traced.result.bind decodePoint⟩

structure CircleTrace where
  result : Except FSOODSampler.Error Point
  final : Transcript
  attempts : List CircleAttempt

def circleTrace (tape : Tape) : Nat → Transcript → CircleTrace
  | 0, start => ⟨.error .parameterExhausted, start, []⟩
  | n + 1, start =>
      let first := circleAttempt tape start
      match first.challenge.result with
      | none => ⟨.error .limbExhausted, first.challenge.final, [first]⟩
      | some _ => match first.decoded with
        | none =>
            let rest := circleTrace tape n first.challenge.final
            ⟨rest.result, rest.final, first :: rest.attempts⟩
        | some point => ⟨.ok point, first.challenge.final, [first]⟩

theorem circleAttempt_decoded (tape : Tape) (start : Transcript) :
    (circleAttempt tape start).decoded =
      (circleAttempt tape start).challenge.result.bind decodePoint := rfl

theorem circleTrace_exact (tape : Tape) : ∀ n start,
    (circleTrace tape n start).result =
        (FSOODSampler.circle decodePoint tape n start).1 ∧
      (circleTrace tape n start).final =
        (FSOODSampler.circle decodePoint tape n start).2 := by
  intro n
  induction n with
  | zero => intro start; exact ⟨rfl, rfl⟩
  | succ n ih =>
      intro start
      have erased := FSLiveChallengeTrace.challenge_erase tape start
      simp only [circleTrace, circleAttempt, FSOODSampler.circle]
      rw [erased.1, erased.2]
      cases sampled : (AspisV8Completion.FSBoundedTranscript.challenge tape start).1 with
      | none => simp [sampled]
      | some values =>
          cases decoded : decodePoint values with
          | none =>
              simp [sampled, decoded]
              simpa using ih (AspisV8Completion.FSBoundedTranscript.challenge tape start).2
          | some point => simp [sampled, decoded]

theorem run_circleScript_trace (tape : Tape) (n : Nat) (start : Transcript) :
    AspisV8Completion.FSOracleExecution.run tape
        (FSOODSampler.circleScript decodePoint n start.digest) start.oracle =
      (some ((circleTrace tape n start).result,
        (circleTrace tape n start).final.digest),
        (circleTrace tape n start).final.oracle) := by
  rw [FSOODSampler.run_circle]
  obtain ⟨resultEq, finalEq⟩ := circleTrace_exact tape n start
  rw [resultEq, finalEq]

inductive SuccessfulCircle (point : Point) : List CircleAttempt → Prop
  | final (attempt : CircleAttempt) (values : List Nat)
      (sampled : attempt.challenge.result = some values)
      (decoded : decodePoint values = some point) :
      SuccessfulCircle point [attempt]
  | retry (attempt : CircleAttempt) (values : List Nat)
      (rest : List CircleAttempt)
      (sampled : attempt.challenge.result = some values)
      (rejected : decodePoint values = none)
      (tail : SuccessfulCircle point rest) :
      SuccessfulCircle point (attempt :: rest)

theorem circleTrace_successful (tape : Tape) : ∀ n start point,
    (circleTrace tape n start).result = .ok point →
      SuccessfulCircle point (circleTrace tape n start).attempts := by
  intro n
  induction n with
  | zero => intro start point success; cases success
  | succ n ih =>
      intro start point success
      simp only [circleTrace] at success ⊢
      cases sampled : (circleAttempt tape start).challenge.result with
      | none => simp [sampled] at success
      | some values =>
          cases decoded : (circleAttempt tape start).decoded with
          | none =>
              simp [sampled, decoded] at success ⊢
              have rejected : decodePoint values = none := by
                have h := decoded
                rw [circleAttempt_decoded, sampled] at h
                exact h
              exact SuccessfulCircle.retry _ values _ sampled
                rejected
                (ih _ point success)
          | some candidate =>
              simp [sampled, decoded] at success ⊢
              subst candidate
              have accepted : decodePoint values = some point := by
                have h := decoded
                rw [circleAttempt_decoded, sampled] at h
                exact h
              exact SuccessfulCircle.final _ values sampled
                accepted

def V7DecodedCircleAttempt (attempt : CircleAttempt) : Prop :=
  ∃ values,
    attempt.challenge.result = some values ∧
      attempt.decoded = decodePoint values ∧
      decodeOrdinaryPrefix attempt.challenge.blocks =
        some { value := encodeQm31Limbs values
               limbs := values
               wordsUsed := attempt.challenge.draws
               blocksUsed := attempt.challenge.blocks.length
               remainingBlocks := [] }

theorem circleAttempt_success_v7 (tape : Tape) (start : Transcript)
    (values : List Nat)
    (sampled : (circleAttempt tape start).challenge.result = some values) :
    V7DecodedCircleAttempt (circleAttempt tape start) := by
  refine ⟨values, sampled, ?_, ?_⟩
  · rw [circleAttempt_decoded, sampled]
    rfl
  · exact AspisV8Completion.FSLiveChallengeV7Decode.challenge_decodeOrdinaryPrefix
      tape start values (by simpa [circleAttempt] using sampled)

inductive ChronologicalCircle (tape : Tape) :
    Transcript → List CircleAttempt → Transcript → Prop
  | nil (start : Transcript) : ChronologicalCircle tape start [] start
  | cons (start : Transcript) (attempt : CircleAttempt)
      (rest : List CircleAttempt) (final : Transcript)
      (actual : attempt = circleAttempt tape start)
      (tail : ChronologicalCircle tape attempt.challenge.final rest final) :
      ChronologicalCircle tape start (attempt :: rest) final

theorem circleTrace_chronological (tape : Tape) : ∀ n start,
    ChronologicalCircle tape start (circleTrace tape n start).attempts
      (circleTrace tape n start).final := by
  intro n
  induction n with
  | zero => intro start; exact .nil start
  | succ n ih =>
      intro start
      simp only [circleTrace]
      cases sampled : (circleAttempt tape start).challenge.result with
      | none =>
          simp only
          exact .cons start _ [] _ rfl (.nil _)
      | some values =>
          cases decoded : (circleAttempt tape start).decoded with
          | none =>
              simp only
              exact .cons start _ _ _ rfl (ih _)
          | some point =>
              simp only
              exact .cons start _ [] _ rfl (.nil _)

theorem successfulCircle_all_v7 (tape : Tape)
    {start final : Transcript} {point : Point} {attempts : List CircleAttempt}
    (chron : ChronologicalCircle tape start attempts final)
    (successful : SuccessfulCircle point attempts) :
    ∀ attempt ∈ attempts, V7DecodedCircleAttempt attempt := by
  induction chron with
  | nil current => cases successful
  | cons current first rest final actual tail ih =>
      subst first
      cases successful with
      | final attempt values sampled decoded =>
          intro queried member
          simp only [List.mem_singleton] at member
          subst queried
          exact circleAttempt_success_v7 tape current values sampled
      | retry attempt values remaining sampled rejected successfulTail =>
          intro queried member
          simp only [List.mem_cons] at member
          cases member with
          | inl head =>
              subst queried
              exact circleAttempt_success_v7 tape current values sampled
          | inr later => exact ih successfulTail queried later

theorem successful_firstScript_live_v7 (tape : Tape) (start : Transcript)
    (point : Point) (finalDigest : AspisV8Completion.FSBoundedTranscript.Block)
    (success : (AspisV8Completion.FSOracleExecution.run tape
      (FSV7OODSampler.firstScript start.digest) start.oracle).1 =
        some (.ok point, finalDigest)) :
    (circleTrace tape 3 start).result = .ok point ∧
      (circleTrace tape 3 start).final.digest = finalDigest ∧
      SuccessfulCircle point (circleTrace tape 3 start).attempts ∧
      ChronologicalCircle tape start (circleTrace tape 3 start).attempts
        (circleTrace tape 3 start).final ∧
      ∀ attempt ∈ (circleTrace tape 3 start).attempts,
        V7DecodedCircleAttempt attempt := by
  have exactRun := congrArg Prod.fst (run_circleScript_trace tape 3 start)
  have sourceSuccess :
      (AspisV8Completion.FSOracleExecution.run tape
        (FSOODSampler.circleScript decodePoint 3 start.digest) start.oracle).1 =
          some (.ok point, finalDigest) := by
    simpa [FSV7OODSampler.firstScript] using success
  rw [sourceSuccess] at exactRun
  have pairEq := Option.some.inj exactRun.symm
  have resultEq : (circleTrace tape 3 start).result = .ok point :=
    congrArg Prod.fst pairEq
  have digestEq : (circleTrace tape 3 start).final.digest = finalDigest :=
    congrArg Prod.snd pairEq
  have shape := circleTrace_successful tape 3 start point resultEq
  have chron := circleTrace_chronological tape 3 start
  exact ⟨resultEq, digestEq, shape, chron,
    successfulCircle_all_v7 tape chron shape⟩

structure DistinctTrace where
  result : Except FSOODSampler.Error Point
  final : Transcript
  rounds : List CircleTrace

noncomputable section
local instance : DecidableEq Point := Classical.decEq _

def distinctTrace (excluded : Point) (tape : Tape) :
    Nat → Transcript → DistinctTrace
  | 0, start => ⟨.error .distinctExhausted, start, []⟩
  | n + 1, start =>
      let first := circleTrace tape 3 start
      match first.result with
      | .error error => ⟨.error error, first.final, [first]⟩
      | .ok point => if point = excluded then
          let rest := distinctTrace excluded tape n first.final
          ⟨rest.result, rest.final, first :: rest.rounds⟩
        else ⟨.ok point, first.final, [first]⟩

theorem distinctTrace_exact (excluded : Point) (tape : Tape) : ∀ n start,
    (distinctTrace excluded tape n start).result =
        (FSOODSampler.distinct decodePoint excluded tape n start).1 ∧
      (distinctTrace excluded tape n start).final =
        (FSOODSampler.distinct decodePoint excluded tape n start).2 := by
  intro n
  induction n with
  | zero => intro start; exact ⟨rfl, rfl⟩
  | succ n ih =>
      intro start
      obtain ⟨resultEq, finalEq⟩ := circleTrace_exact tape 3 start
      simp only [distinctTrace, FSOODSampler.distinct]
      rw [← resultEq, ← finalEq]
      cases (circleTrace tape 3 start).result with
      | error error => simp
      | ok point =>
          by_cases equal : point = excluded
          · simp only [if_pos equal]
            simpa using ih (circleTrace tape 3 start).final
          · simp [equal]

theorem run_distinctScript_trace (excluded : Point) (tape : Tape)
    (n : Nat) (start : Transcript) :
    AspisV8Completion.FSOracleExecution.run tape
        (FSOODSampler.distinctScript decodePoint excluded n start.digest)
        start.oracle =
      (some ((distinctTrace excluded tape n start).result,
        (distinctTrace excluded tape n start).final.digest),
        (distinctTrace excluded tape n start).final.oracle) := by
  rw [FSOODSampler.run_distinct]
  obtain ⟨resultEq, finalEq⟩ := distinctTrace_exact excluded tape n start
  rw [resultEq, finalEq]

inductive SuccessfulDistinct (excluded result : Point) :
    List CircleTrace → Prop
  | final (round : CircleTrace)
      (success : round.result = .ok result) (different : result ≠ excluded) :
      SuccessfulDistinct excluded result [round]
  | retry (round : CircleTrace) (rest : List CircleTrace)
      (equal : round.result = .ok excluded)
      (tail : SuccessfulDistinct excluded result rest) :
      SuccessfulDistinct excluded result (round :: rest)

theorem distinctTrace_successful (excluded : Point) (tape : Tape) :
    ∀ n start result,
    (distinctTrace excluded tape n start).result = .ok result →
      SuccessfulDistinct excluded result
        (distinctTrace excluded tape n start).rounds := by
  intro n
  induction n with
  | zero => intro start result success; cases success
  | succ n ih =>
      intro start result success
      simp only [distinctTrace] at success ⊢
      cases roundResult : (circleTrace tape 3 start).result with
      | error error => simp [roundResult] at success
      | ok point =>
          by_cases equal : point = excluded
          · simp [roundResult, equal] at success ⊢
            exact .retry _ _ (roundResult.trans (by rw [equal]))
              (ih _ result success)
          · simp [roundResult, equal] at success ⊢
            subst point
            exact .final _ roundResult equal

inductive ChronologicalDistinct (tape : Tape) :
    Transcript → List CircleTrace → Transcript → Prop
  | nil (start : Transcript) : ChronologicalDistinct tape start [] start
  | cons (start : Transcript) (round : CircleTrace)
      (rest : List CircleTrace) (final : Transcript)
      (actual : round = circleTrace tape 3 start)
      (tail : ChronologicalDistinct tape round.final rest final) :
      ChronologicalDistinct tape start (round :: rest) final

theorem distinctTrace_chronological (excluded : Point) (tape : Tape) :
    ∀ n start,
    ChronologicalDistinct tape start (distinctTrace excluded tape n start).rounds
      (distinctTrace excluded tape n start).final := by
  intro n
  induction n with
  | zero => intro start; exact .nil start
  | succ n ih =>
      intro start
      simp only [distinctTrace]
      cases roundResult : (circleTrace tape 3 start).result with
      | error error =>
          simp only
          exact .cons start _ [] _ rfl (.nil _)
      | ok point =>
          by_cases equal : point = excluded
          · simp only [if_pos equal]
            exact .cons start _ _ _ rfl (ih _)
          · simp only [if_neg equal]
            exact .cons start _ [] _ rfl (.nil _)

theorem successfulDistinct_all_inner_v7 (excluded result : Point)
    (tape : Tape) {start final : Transcript} {rounds : List CircleTrace}
    (chron : ChronologicalDistinct tape start rounds final)
    (successful : SuccessfulDistinct excluded result rounds) :
    ∀ round ∈ rounds,
      ∀ attempt ∈ round.attempts, V7DecodedCircleAttempt attempt := by
  induction chron with
  | nil current => cases successful
  | cons current first rest final actual tail ih =>
      subst first
      cases successful with
      | final round roundSuccess different =>
          intro queried member
          simp only [List.mem_singleton] at member
          subst queried
          exact successfulCircle_all_v7 tape
            (circleTrace_chronological tape 3 current)
            (circleTrace_successful tape 3 current result roundSuccess)
      | retry round remaining equal successfulTail =>
          intro queried member
          simp only [List.mem_cons] at member
          cases member with
          | inl head =>
              subst queried
              exact successfulCircle_all_v7 tape
                (circleTrace_chronological tape 3 current)
                (circleTrace_successful tape 3 current excluded equal)
          | inr later => exact ih successfulTail queried later

theorem successful_distinct_all_inner_v7 (excluded : Point) (tape : Tape)
    (n : Nat) (start : Transcript) (result : Point)
    (success : (distinctTrace excluded tape n start).result = .ok result) :
    ∀ round ∈ (distinctTrace excluded tape n start).rounds,
      ∀ attempt ∈ round.attempts, V7DecodedCircleAttempt attempt := by
  exact successfulDistinct_all_inner_v7 excluded result tape
    (distinctTrace_chronological excluded tape n start)
    (distinctTrace_successful excluded tape n start result success)

theorem successful_secondScript_live_v7 (excluded : Point) (tape : Tape)
    (start : Transcript) (result : Point)
    (finalDigest : AspisV8Completion.FSBoundedTranscript.Block)
    (success : (AspisV8Completion.FSOracleExecution.run tape
      (FSV7OODSampler.secondScript excluded start.digest) start.oracle).1 =
        some (.ok result, finalDigest)) :
    (distinctTrace excluded tape 3 start).result = .ok result ∧
      (distinctTrace excluded tape 3 start).final.digest = finalDigest ∧
      SuccessfulDistinct excluded result
        (distinctTrace excluded tape 3 start).rounds ∧
      ChronologicalDistinct tape start
        (distinctTrace excluded tape 3 start).rounds
        (distinctTrace excluded tape 3 start).final ∧
      result ≠ excluded ∧
      ∀ round ∈ (distinctTrace excluded tape 3 start).rounds,
        ∀ attempt ∈ round.attempts, V7DecodedCircleAttempt attempt := by
  have exactRun := congrArg Prod.fst
    (run_distinctScript_trace excluded tape 3 start)
  have sourceSuccess :
      (AspisV8Completion.FSOracleExecution.run tape
        (FSOODSampler.distinctScript decodePoint excluded 3 start.digest)
          start.oracle).1 = some (.ok result, finalDigest) := by
    simpa [FSV7OODSampler.secondScript] using success
  rw [sourceSuccess] at exactRun
  have pairEq := Option.some.inj exactRun.symm
  have resultEq : (distinctTrace excluded tape 3 start).result = .ok result :=
    congrArg Prod.fst pairEq
  have digestEq : (distinctTrace excluded tape 3 start).final.digest =
      finalDigest := congrArg Prod.snd pairEq
  have shape := distinctTrace_successful excluded tape 3 start result resultEq
  have chron := distinctTrace_chronological excluded tape 3 start
  have different : result ≠ excluded := by
    have sourceResult :
        (FSV7OODSampler.second excluded tape start).1 = .ok result := by
      have exactSource := FSV7OODSampler.second_script_exact excluded tape start
      have firstEq := congrArg Prod.fst exactSource
      rw [success] at firstEq
      exact congrArg Prod.fst (Option.some.inj firstEq.symm)
    exact FSV7OODSampler.second_success_distinct excluded result tape start sourceResult
  exact ⟨resultEq, digestEq, shape, chron, different,
    successful_distinct_all_inner_v7 excluded tape 3 start result resultEq⟩

#print axioms circleTrace_exact
#print axioms run_circleScript_trace
#print axioms circleTrace_successful
#print axioms successfulCircle_all_v7
#print axioms successful_firstScript_live_v7
#print axioms distinctTrace_exact
#print axioms run_distinctScript_trace
#print axioms distinctTrace_successful
#print axioms distinctTrace_chronological
#print axioms successful_distinct_all_inner_v7
#print axioms successful_secondScript_live_v7

end
end AspisV8Completion.FSLiveOODV7Decode
