import FSLiveQ22V7WordBridge
import FSLiveNonzeroV7Decode

/-!
# Exact final256/query/rho suffix

This file supplies the minimal source-shaped `Script` absent from the earlier
pure `sampledRhoBody` model.  It uses the pinned selected byte grammar:

* absorb body fields 441..696 under label 53 (`V6_FINAL256`),
* absorb nonce2 at byte offset 11220 under label 5 (`GRIND_NONCE`),
* run the exact q22/64-draw query sampler,
* absorb literal `AV8/query-batch/v1` under label 1 (`PROFILE`), and
* run the exact three-attempt nonzero rho sampler.

The theorem is deterministic.  It preserves cache hits, duplicate candidates,
the query detection block, every failure and exact final transcript state.  It
does not claim freshness, uniformity, or literal Rust refinement.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSLiveQueryRhoSuffix

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSQuerySampler FSQuerySchedule FSNonzeroQM31
open FSLiveQ22V7WordBridge FSLiveNonzeroV7Decode

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Transcript := FSBoundedTranscript.Transcript
abbrev Block := FSBoundedTranscript.Block
abbrev K := FSNonzeroQM31.K

inductive Error where
  | queryExhausted
  | rho (error : FSNonzeroQM31.Error)
  deriving DecidableEq

abbrev Result := Except Error (List Nat × K)

def final256Bytes (body : Bytes) : Bytes := (body.drop 7056).take 4096
def queryNonceBytes (body : Bytes) : Bytes := (body.drop 11220).take 8
/-- Literal ASCII bytes of `AV8/query-batch/v1`; source label `PROFILE = 1`. -/
def queryBatchProfile : Bytes :=
  [65,86,56,47,113,117,101,114,121,45,98,97,116,99,104,47,118,49]

/-- Literal chronological suffix. Static padding in `bind` performs no dummy
oracle calls. -/
def queryRhoScript (body : Bytes) (digest : Block) :
    Script Bytes Block (Result × Block) (198 + 1 + 2*8 + 1 + 1) :=
  bind (m := 198 + 1 + 2*8 + 1)
      (absorbScript digest 53 (final256Bytes body)) fun afterFinal =>
    bind (m := 198 + 1 + 2*8)
        (absorbScript afterFinal 5 (queryNonceBytes body)) fun afterNonce =>
      bind (m := 198 + 1)
          (queryScript 8 afterNonce [] 0) fun sampled =>
        match sampled.1 with
        | none => .done (Except.error .queryExhausted, sampled.2)
        | some returned =>
          bind (m := 198) (absorbScript sampled.2 1 queryBatchProfile)
              fun afterProfile =>
            bind (m := 0) (nonzeroScript 3 afterProfile) fun rho =>
              .done (match rho.1 with
                | .error e => (Except.error (Error.rho e), rho.2)
                | .ok value => (Except.ok (returned, value), rho.2))

structure Trace where
  afterFinal : Transcript
  afterNonce : Transcript
  query : QueryTrace
  afterProfile : Option Transcript
  rho : Option NonzeroTrace
  result : Result
  final : Transcript

def trace (body : Bytes) (tape : Tape) (start : Transcript) : Trace :=
  let afterFinal := absorb tape start 53 (final256Bytes body)
  let afterNonce := absorb tape afterFinal 5 (queryNonceBytes body)
  let query := queryTrace tape 8 afterNonce [] 0
  match query.result with
  | none => ⟨afterFinal, afterNonce, query, none, none,
      .error .queryExhausted, query.final⟩
  | some returned =>
    let afterProfile := absorb tape query.final 1 queryBatchProfile
    let rho := nonzeroTrace tape 3 afterProfile
    match rho.result with
    | .error e => ⟨afterFinal, afterNonce, query, some afterProfile, some rho,
        .error (.rho e), rho.final⟩
    | .ok value => ⟨afterFinal, afterNonce, query, some afterProfile, some rho,
        .ok (returned, value), rho.final⟩

theorem trace_exact (body : Bytes) (tape : Tape) (start : Transcript) :
    run tape (queryRhoScript body start.digest) start.oracle =
      (some ((trace body tape start).result, (trace body tape start).final.digest),
        (trace body tape start).final.oracle) := by
  unfold queryRhoScript trace
  rw [run_bind, run_absorb]
  simp only [Prod.fst, Prod.snd, run_bind]
  rw [run_absorb]
  simp only [Prod.fst, Prod.snd, run_bind, run_queryScript_trace]
  cases queryResult :
      (queryTrace tape 8
        (absorb tape (absorb tape start 53 (final256Bytes body))
          5 (queryNonceBytes body)) [] 0).result with
  | none => simp [queryResult, run]
  | some returned =>
    simp only [queryResult, run_bind]
    rw [run_absorb]
    simp only [Prod.fst, Prod.snd, run_bind, run_nonzeroScript_trace]
    cases rhoResult :
        (nonzeroTrace tape 3
          (absorb tape
            (queryTrace tape 8
              (absorb tape (absorb tape start 53 (final256Bytes body))
                5 (queryNonceBytes body)) [] 0).final
            1 queryBatchProfile)).result <;>
      simp [queryResult, rhoResult, run]

/-- The trace's query start is exactly the two literal source-shaped public
absorptions, preventing a stale final256/nonce prefix. -/
theorem afterNonce_literal (body : Bytes) (tape : Tape)
    (start : Transcript) :
    (trace body tape start).afterNonce =
      absorb tape (absorb tape start 53 ((body.drop 7056).take 4096))
        5 ((body.drop 11220).take 8) := by
  unfold trace final256Bytes queryNonceBytes
  cases queryResult : (queryTrace tape 8
    (absorb tape (absorb tape start 53 ((body.drop 7056).take 4096))
      5 ((body.drop 11220).take 8)) [] 0).result with
  | none => simp [queryResult]
  | some returned =>
    cases rhoResult : (nonzeroTrace tape 3
      (absorb tape
        (queryTrace tape 8
          (absorb tape (absorb tape start 53 ((body.drop 7056).take 4096))
            5 ((body.drop 11220).take 8)) [] 0).final
        1 queryBatchProfile)).result <;>
      simp [queryResult, rhoResult]

theorem query_literal (body : Bytes) (tape : Tape) (start : Transcript) :
    (trace body tape start).query =
      queryTrace tape 8
        (absorb tape (absorb tape start 53 (final256Bytes body))
          5 (queryNonceBytes body)) [] 0 := by
  unfold trace
  cases queryResult : (queryTrace tape 8
    (absorb tape (absorb tape start 53 (final256Bytes body))
      5 (queryNonceBytes body)) [] 0).result with
  | none => simp [queryResult]
  | some returned =>
    cases rhoResult : (nonzeroTrace tape 3
      (absorb tape
        (queryTrace tape 8
          (absorb tape (absorb tape start 53 (final256Bytes body))
            5 (queryNonceBytes body)) [] 0).final
        1 queryBatchProfile)).result <;>
      simp [queryResult, rhoResult]

/-- Every actual q22 squeeze block is V7-word routed and is chronologically
linked from the fixed final256/nonce prefix. -/
theorem trace_query_chronological_v7 (body : Bytes) (tape : Tape)
    (start : Transcript) :
    ChronologicalSteps tape (trace body tape start).afterNonce
        (trace body tape start).query.steps (trace body tape start).query.final ∧
      ∀ step ∈ (trace body tape start).query.steps, V7WordRoutedStep step := by
  rw [afterNonce_literal, query_literal]
  exact ⟨queryTrace_chronological tape 8 _ [] 0,
    queryTrace_all_steps_v7_words tape 8 _ [] 0⟩

def RhoAllV7 (rhoTrace : NonzeroTrace) : Prop :=
  ∀ rho, rhoTrace.result = .ok rho →
    ∀ attempt ∈ rhoTrace.attempts, V7DecodedAttempt attempt

theorem nonzeroTrace_all_v7 (tape : Tape) (n : Nat) (start : Transcript) :
    RhoAllV7 (nonzeroTrace tape n start) := by
  intro rho success
  exact successful_chronological_all_v7Decoded tape
    (nonzeroTrace_chronological tape n start)
    (nonzeroTrace_successfulAttempts tape n start rho success)

/-- Whenever rho was reached, every successful candidate attempt uses the V7
ordinary decoder. Failure attempts and zero retries remain in the trace. -/
theorem trace_reached_rho_v7 (body : Bytes) (tape : Tape)
    (start : Transcript) :
    ∀ rhoTrace, (trace body tape start).rho = some rhoTrace →
      RhoAllV7 rhoTrace := by
  intro rhoTrace reached
  unfold trace at reached
  cases queryResult :
      (queryTrace tape 8
        (absorb tape (absorb tape start 53 (final256Bytes body))
          5 (queryNonceBytes body)) [] 0).result with
  | none => simp [queryResult] at reached
  | some returned =>
    simp only [queryResult] at reached
    cases rhoResult :
        (nonzeroTrace tape 3
          (absorb tape
            (queryTrace tape 8
              (absorb tape (absorb tape start 53 (final256Bytes body))
                5 (queryNonceBytes body)) [] 0).final
            1 queryBatchProfile)).result <;>
      simp [rhoResult] at reached
    · subst rhoTrace
      exact nonzeroTrace_all_v7 tape 3 _
    · subst rhoTrace
      exact nonzeroTrace_all_v7 tape 3 _

/-- Success fixes the selected q22 schedule before the live nonzero rho and
establishes both schedule invariants and nonzeroness without a distribution
claim. -/
theorem trace_success (body : Bytes) (tape : Tape) (start : Transcript)
    (returned : List Nat) (rho : K)
    (success : (trace body tape start).result = .ok (returned, rho)) :
    ValidAccepted returned ∧ returned.length = 22 ∧ rho ≠ 0 := by
  unfold trace at success
  cases queryResult :
      (queryTrace tape 8
        (absorb tape (absorb tape start 53 (final256Bytes body))
          5 (queryNonceBytes body)) [] 0).result with
  | none => simp [queryResult] at success
  | some actual =>
    simp only [queryResult] at success
    let afterProfile := absorb tape
      (queryTrace tape 8
        (absorb tape (absorb tape start 53 (final256Bytes body))
          5 (queryNonceBytes body)) [] 0).final 1 queryBatchProfile
    cases rhoResult : (nonzeroTrace tape 3 afterProfile).result with
    | error e => simp [afterProfile, rhoResult] at success
    | ok actualRho =>
      simp [afterProfile, rhoResult] at success
      rcases success with ⟨rfl, rfl⟩
      have scheduleFacts := successful_queryTrace_schedule tape
        (absorb tape (absorb tape start 53 (final256Bytes body))
          5 (queryNonceBytes body)) actual queryResult
      exact ⟨scheduleFacts.1, scheduleFacts.2,
        nonzero_success_ne tape 3 afterProfile actualRho
          (by
            have erased := (nonzeroTrace_exact tape 3 afterProfile).1
            simpa [rhoResult] using erased.symm)⟩

#print axioms trace_exact
#print axioms afterNonce_literal
#print axioms trace_query_chronological_v7
#print axioms trace_reached_rho_v7
#print axioms trace_success

end AspisV8Completion.FSLiveQueryRhoSuffix
