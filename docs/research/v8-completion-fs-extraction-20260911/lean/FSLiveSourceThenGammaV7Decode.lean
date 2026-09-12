import FSLiveOODV7Decode
import FSLiveNonzeroV7Decode
import FSV8PostOODGammaScript

/-!
# One chronological live OOD-to-gamma trace

This is deterministic instrumentation of the selected source slice.  It
retains the canonical-body abort, both work-script aborts, all first-point and
distinct-second-point retry/failure cases, the two answer absorptions, nonce
absorption, and all nonzero-gamma retry/failure cases.  Erasing the trace is
the actual `sourceThenGammaScript` run, including its final digest, cache,
fresh-tape cursor, and log.

Successful traces expose the already-proved V7 ordinary decoding facts for
every completed OOD and gamma attempt.  There is deliberately no freshness,
uniformity, independence, or adversarial-source coupling claim here.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSLiveSourceThenGammaV7Decode

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSOODSampler FSV8OODBodyScript FSV7OODBodyScript
open FSV8PostOODGammaScript
open FSLiveOODV7Decode FSLiveNonzeroV7Decode

abbrev Bytes := List UInt8
abbrev Point := FSV7OODBodyScript.Point
abbrev OODResult := FSV7OODBodyScript.Result
abbrev Gamma := FSNonzeroQM31.K
abbrev CombinedError := Sum FSOODSampler.Error FSNonzeroQM31.Error
abbrev CombinedResult := Except CombinedError (OODResult × Gamma)
abbrev Tape := FSBoundedTranscript.Tape
abbrev Transcript := FSBoundedTranscript.Transcript
abbrev Block := FSBoundedTranscript.Block

noncomputable section
local instance : DecidableEq Point := Classical.decEq _

/-- Optional phase records are `none` exactly when that phase was never
reached.  `outcome = none` records a genuine script abort, while `final`
always retains the transcript state at the abort or returned result. -/
structure SourceGammaTrace where
  outcome : Option CombinedResult
  final : Transcript
  first : Option CircleTrace := none
  afterFirstAnswer : Option Transcript := none
  second : Option DistinctTrace := none
  afterSecondAnswer : Option Transcript := none
  afterNonce : Option Transcript := none
  gamma : Option NonzeroTrace := none

private def returned (result : CombinedResult) (final : Transcript)
    (first : Option CircleTrace := none)
    (afterFirstAnswer : Option Transcript := none)
    (second : Option DistinctTrace := none)
    (afterSecondAnswer : Option Transcript := none)
    (afterNonce : Option Transcript := none)
    (gamma : Option NonzeroTrace := none) : SourceGammaTrace :=
  ⟨some result, final, first, afterFirstAnswer, second,
    afterSecondAnswer, afterNonce, gamma⟩

private def aborted (final : Transcript)
    (first : Option CircleTrace := none)
    (afterFirstAnswer : Option Transcript := none)
    (second : Option DistinctTrace := none) : SourceGammaTrace :=
  ⟨none, final, first, afterFirstAnswer, second, none, none, none⟩

/-- Direct, phase-visible execution of the selected script. -/
def sourceGammaTrace {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (tape : Tape) (start : Transcript) : SourceGammaTrace :=
  if canonical : CanonicalOODFields body then
    let first := circleTrace tape 3 start
    match first.result with
    | .error e => returned (.error (.inl e)) first.final (some first)
    | .ok firstPoint =>
      let firstRun := run tape (firstWork firstPoint) first.final.oracle
      match firstRun.1 with
      | none => aborted ⟨first.final.digest, firstRun.2⟩ (some first)
      | some _ =>
        let beforeFirst := ⟨first.final.digest, firstRun.2⟩
        let afterFirst := absorb tape beforeFirst 62 (0 :: answerBytes body 0)
        let second := distinctTrace firstPoint tape 3 afterFirst
        match second.result with
        | .error e => returned (.error (.inl e)) second.final (some first)
            (some afterFirst) (some second)
        | .ok secondPoint =>
          let secondRun := run tape (secondWork firstPoint secondPoint)
            second.final.oracle
          match secondRun.1 with
          | none => aborted ⟨second.final.digest, secondRun.2⟩ (some first)
              (some afterFirst) (some second)
          | some _ =>
            let beforeSecond := ⟨second.final.digest, secondRun.2⟩
            let afterSecond := absorb tape beforeSecond 62 (1 :: answerBytes body 1)
            let out : OODResult := ⟨firstPoint, secondPoint,
              afterFirst.digest, afterSecond.digest⟩
            let afterNonce := absorb tape afterSecond 28 (batchNonceBytes body)
            let gamma := nonzeroTrace tape 3 afterNonce
            match gamma.result with
            | .error e => returned (.error (.inr e)) gamma.final (some first)
                (some afterFirst) (some second) (some afterSecond)
                (some afterNonce) (some gamma)
            | .ok value => returned (.ok (out, value)) gamma.final (some first)
                (some afterFirst) (some second) (some afterSecond)
                (some afterNonce) (some gamma)
  else aborted start

/-- Erasing the phase records is exactly the selected source execution. -/
theorem sourceGammaTrace_exact {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (tape : Tape) (start : Transcript) :
    run tape (sourceThenGammaScript firstWork secondWork body start.digest)
        start.oracle =
      ((sourceGammaTrace firstWork secondWork body tape start).outcome.map
          (fun result => (result,
            (sourceGammaTrace firstWork secondWork body tape start).final.digest)),
        (sourceGammaTrace firstWork secondWork body tape start).final.oracle) := by
  unfold sourceThenGammaScript FSV7OODBodyScript.sourceScript
    checkedBodyPairScript bodyPairScript sourceGammaTrace
  split <;> rename_i canonical
  · rw [run_bind, run_bind, run_circleScript_trace]
    simp only [Prod.fst, Prod.snd]
    cases firstResult : (circleTrace tape 3 start).result with
    | error e => simp [firstResult, returned, run]
    | ok firstPoint =>
      simp only [firstResult, run_bind, run_answerScript]
      cases firstWorkResult :
          (run tape (firstWork firstPoint)
            (circleTrace tape 3 start).final.oracle).1 with
      | none => simp [firstWorkResult, aborted]
      | some unit =>
        simp only [firstWorkResult, Option.map_some, run_bind]
        have firstAbsorbExact := run_absorb tape
          ({ digest := (circleTrace tape 3 start).final.digest,
             oracle := (run tape (firstWork firstPoint)
               (circleTrace tape 3 start).final.oracle).2 } : Transcript)
          62 (0 :: answerBytes body 0)
        rw [firstAbsorbExact]
        simp only [Prod.fst, Prod.snd, run_bind, run_distinctScript_trace]
        let afterFirst := absorb tape
          { digest := (circleTrace tape 3 start).final.digest,
            oracle := (run tape (firstWork firstPoint)
              (circleTrace tape 3 start).final.oracle).2 }
          62 (0 :: answerBytes body 0)
        change _ = _
        cases secondResult : (distinctTrace firstPoint tape 3 afterFirst).result with
        | error e => simp [afterFirst, secondResult, afterSecond, returned, run]
        | ok secondPoint =>
          simp only [afterFirst, secondResult, afterSecond, run_bind,
            run_answerScript]
          cases secondWorkResult :
              (run tape (secondWork firstPoint secondPoint)
                (distinctTrace firstPoint tape 3 afterFirst).final.oracle).1 with
          | none => simp [afterFirst, secondWorkResult, aborted]
          | some unit =>
            simp only [secondWorkResult, Option.map_some, run_bind]
            have secondAbsorbExact := run_absorb tape
              ({ digest := (distinctTrace firstPoint tape 3 afterFirst).final.digest,
                 oracle := (run tape (secondWork firstPoint secondPoint)
                   (distinctTrace firstPoint tape 3 afterFirst).final.oracle).2 } : Transcript)
              62 (1 :: answerBytes body 1)
            rw [secondAbsorbExact]
            simp only [Prod.fst, Prod.snd, run_bind, run]
            have nonceAbsorbExact := run_absorb tape
              (absorb tape
                ({ digest := (distinctTrace firstPoint tape 3 afterFirst).final.digest,
                   oracle := (run tape (secondWork firstPoint secondPoint)
                     (distinctTrace firstPoint tape 3 afterFirst).final.oracle).2 } : Transcript)
                62 (1 :: answerBytes body 1))
              28 (batchNonceBytes body)
            rw [nonceAbsorbExact]
            simp only [Prod.fst, Prod.snd, run_bind, run_nonzeroScript_trace]
            cases gammaResult :
                (nonzeroTrace tape 3
                  (absorb tape
                    (absorb tape
                      { digest := (distinctTrace firstPoint tape 3 afterFirst).final.digest,
                        oracle := (run tape (secondWork firstPoint secondPoint)
                          (distinctTrace firstPoint tape 3 afterFirst).final.oracle).2 }
                      62 (1 :: answerBytes body 1))
                    28 (batchNonceBytes body))).result with
            | error e => simp [afterFirst, gammaResult, returned, run]
            | ok gamma => simp [afterFirst, gammaResult, returned, run]
  · rw [run_bind]
    rfl

/-- Decoder content required of every OOD attempt in a successfully decoded
circle retry trace. -/
def CircleAllV7 (trace : CircleTrace) : Prop :=
  ∀ point, trace.result = .ok point →
    ∀ attempt ∈ trace.attempts, V7DecodedCircleAttempt attempt

/-- Decoder content required of every inner circle attempt in a successfully
decoded distinct-point retry trace. -/
def DistinctAllV7 (trace : DistinctTrace) : Prop :=
  ∀ point, trace.result = .ok point →
    ∀ round ∈ trace.rounds, ∀ attempt ∈ round.attempts,
      V7DecodedCircleAttempt attempt

/-- Decoder content required of every candidate in a successful nonzero
retry trace. -/
def GammaAllV7 (trace : NonzeroTrace) : Prop :=
  ∀ gamma, trace.result = .ok gamma →
    ∀ attempt ∈ trace.attempts, V7DecodedAttempt attempt

theorem circleTrace_all_v7 (tape : Tape) (n : Nat) (start : Transcript) :
    CircleAllV7 (circleTrace tape n start) := by
  intro point success
  exact successfulCircle_all_v7 tape
    (circleTrace_chronological tape n start)
    (circleTrace_successful tape n start point success)

theorem distinctTrace_all_v7 (excluded : Point) (tape : Tape)
    (n : Nat) (start : Transcript) :
    DistinctAllV7 (distinctTrace excluded tape n start) := by
  intro point success
  exact successfulDistinct_all_inner_v7 excluded point tape
    (distinctTrace_chronological excluded tape n start)
    (distinctTrace_successful excluded tape n start point success)

theorem nonzeroTrace_all_v7 (tape : Tape) (n : Nat) (start : Transcript) :
    GammaAllV7 (nonzeroTrace tape n start) := by
  intro gamma success
  exact successful_chronological_all_v7Decoded tape
    (nonzeroTrace_chronological tape n start)
    (nonzeroTrace_successfulAttempts tape n start gamma success)

/-- This property ranges over every phase that the total trace actually
reached.  It is intentionally conditional only on that phase having returned
a decoded value: a limb-exhausted final attempt has no ordinary decoding
witness to expose. -/
def EveryReachedAttemptV7 (trace : SourceGammaTrace) : Prop :=
  (∀ first, trace.first = some first → CircleAllV7 first) ∧
  (∀ second, trace.second = some second → DistinctAllV7 second) ∧
  (∀ gamma, trace.gamma = some gamma → GammaAllV7 gamma)

/-- All completed successful sampler phases in the exact selected chronology
route through the V7 ordinary decoder.  This theorem covers traces that later
fail or abort as well as globally successful traces. -/
theorem sourceGammaTrace_every_reached_v7 {n m : Nat}
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (tape : Tape) (start : Transcript) :
    EveryReachedAttemptV7
      (sourceGammaTrace firstWork secondWork body tape start) := by
  unfold EveryReachedAttemptV7 sourceGammaTrace
  split
  · cases firstResult : (circleTrace tape 3 start).result with
    | error e =>
        simp [firstResult, returned, circleTrace_all_v7]
    | ok firstPoint =>
      cases firstWorkResult :
          (run tape (firstWork firstPoint)
            (circleTrace tape 3 start).final.oracle).1 with
      | none => simp [firstResult, firstWorkResult, aborted, circleTrace_all_v7]
      | some firstUnit =>
        let afterFirst := absorb tape
          { digest := (circleTrace tape 3 start).final.digest,
            oracle := (run tape (firstWork firstPoint)
              (circleTrace tape 3 start).final.oracle).2 }
          62 (0 :: answerBytes body 0)
        cases secondResult : (distinctTrace firstPoint tape 3 afterFirst).result with
        | error e =>
            simp [firstResult, firstWorkResult, afterFirst, secondResult,
              returned, circleTrace_all_v7, distinctTrace_all_v7]
        | ok secondPoint =>
          cases secondWorkResult :
              (run tape (secondWork firstPoint secondPoint)
                (distinctTrace firstPoint tape 3 afterFirst).final.oracle).1 with
          | none =>
              simp [firstResult, firstWorkResult, afterFirst, secondResult,
                secondWorkResult, aborted, circleTrace_all_v7,
                distinctTrace_all_v7]
          | some secondUnit =>
            cases gammaResult :
                (nonzeroTrace tape 3
                  (absorb tape
                    (absorb tape
                      { digest := (distinctTrace firstPoint tape 3 afterFirst).final.digest,
                        oracle := (run tape (secondWork firstPoint secondPoint)
                          (distinctTrace firstPoint tape 3 afterFirst).final.oracle).2 }
                      62 (1 :: answerBytes body 1))
                    28 (batchNonceBytes body))).result <;>
              simp [firstResult, firstWorkResult, afterFirst, secondResult,
                secondWorkResult, gammaResult, returned, circleTrace_all_v7,
                distinctTrace_all_v7, nonzeroTrace_all_v7]
  · simp [aborted]

#print axioms sourceGammaTrace_exact
#print axioms sourceGammaTrace_every_reached_v7

end
end AspisV8Completion.FSLiveSourceThenGammaV7Decode
