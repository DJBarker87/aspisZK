import FSLiveSelectedMiddleQueryRho

/-!
# Live response1--response3 relation suffix

Exact deterministic transcript order after rho in the selected structured
research callback.  The verifier-derived query increment remains an explicit
source producer.  All three later alphas are sampled here; none is supplied
as an environment coin.

The Rust terminal arithmetic has no transcript call and is not yet represented
by a source-shaped Lean evaluator.  This leaf therefore ends with the complete
terminal input, not an assumed terminal-success bit.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSLiveLaterRelationSuffix

open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSNonzeroQM31
open FSV8PostOODGammaScript FSLiveSelectedMiddleQueryRho

abbrev Bytes := List UInt8
abbrev Tape := FSBoundedTranscript.Tape
abbrev Transcript := FSBoundedTranscript.Transcript
abbrev Block := FSBoundedTranscript.Block
abbrev K := FSNonzeroQM31.K
abbrev OODResult := FSV7OODBodyScript.Result

/-- Rust computes the query-injection scalar from authenticated openings after
rho.  The source arithmetic producing these canonical 16 bytes remains open;
the dependency type prevents it from being chosen before the rho record. -/
structure IncrementProducer where
  bytes : OODResult -> K -> FSLiveSelectedMiddleQueryRho.Success -> Bytes -> Bytes

def responseBytes (body : Bytes) (round : Nat) : Bytes :=
  (body.drop ((417 + 6*round)*16)).take 96

inductive Error where
  | alpha1 (error : FSNonzeroQM31.Error)
  | alpha2 (error : FSNonzeroQM31.Error)
  | alpha3 (error : FSNonzeroQM31.Error)
  deriving DecidableEq

structure Success where
  alpha1 : K
  alpha2 : K
  alpha3 : K

/-- Exact `Fin 3` coin vector expected by the algebraic relation consumer,
constructed solely from sequential live challenge results. -/
def Success.coins (success : Success) : Fin 3 -> K
  | ⟨0, _⟩ => success.alpha1
  | ⟨1, _⟩ => success.alpha2
  | ⟨2, _⟩ => success.alpha3

theorem Success.coins_literal (success : Success) :
    success.coins 0 = success.alpha1 /\
    success.coins 1 = success.alpha2 /\
    success.coins 2 = success.alpha3 := by
  exact ⟨rfl, rfl, rfl⟩

abbrev Result := Except Error Success

/-- Literal selected suffix: query increment, then each response before its
own ordinary (zero-permitted) alpha. -/
def laterScript (increment : IncrementProducer) (out : OODResult) (gamma : K)
    (middle : FSLiveSelectedMiddleQueryRho.Success) (body : Bytes)
    (digest : Block) :=
  bind (absorbScript digest 1 (increment.bytes out gamma middle body))
      fun afterIncrement =>
    bind (absorbScript afterIncrement 52 (1 :: responseBytes body 1))
        fun afterResponse1 =>
      bind (candidateScript afterResponse1) fun alpha1Draw =>
        match alpha1Draw.1 with
        | .error e => .done (Except.error (Error.alpha1 e), alpha1Draw.2)
        | .ok alpha1 =>
          bind (absorbScript alpha1Draw.2 52 (2 :: responseBytes body 2))
              fun afterResponse2 =>
            bind (candidateScript afterResponse2) fun alpha2Draw =>
              match alpha2Draw.1 with
              | .error e => .done (Except.error (Error.alpha2 e), alpha2Draw.2)
              | .ok alpha2 =>
                bind (absorbScript alpha2Draw.2 52 (3 :: responseBytes body 3))
                    fun afterResponse3 =>
                  bind (m := 0) (candidateScript afterResponse3) fun alpha3Draw =>
                    .done (match alpha3Draw.1 with
                      | .error e =>
                        (Except.error (Error.alpha3 e), alpha3Draw.2)
                      | .ok alpha3 =>
                        (Except.ok (Success.mk alpha1 alpha2 alpha3),
                          alpha3Draw.2))

structure Trace where
  afterIncrement : Transcript
  afterResponse1 : Transcript
  alpha1 : Except FSNonzeroQM31.Error K × Transcript
  afterResponse2 : Option Transcript
  alpha2 : Option (Except FSNonzeroQM31.Error K × Transcript)
  afterResponse3 : Option Transcript
  alpha3 : Option (Except FSNonzeroQM31.Error K × Transcript)
  result : Result
  final : Transcript

noncomputable def trace (increment : IncrementProducer) (out : OODResult)
    (gamma : K) (middle : FSLiveSelectedMiddleQueryRho.Success) (body : Bytes)
    (tape : Tape) (start : Transcript) : Trace :=
  let afterIncrement := absorb tape start 1 (increment.bytes out gamma middle body)
  let afterResponse1 := absorb tape afterIncrement 52 (1 :: responseBytes body 1)
  let a1 := candidate tape afterResponse1
  match a1.1 with
  | .error e => ⟨afterIncrement, afterResponse1, a1, none, none, none, none,
      .error (.alpha1 e), a1.2⟩
  | .ok alpha1 =>
    let afterResponse2 := absorb tape a1.2 52 (2 :: responseBytes body 2)
    let a2 := candidate tape afterResponse2
    match a2.1 with
    | .error e => ⟨afterIncrement, afterResponse1, a1, some afterResponse2,
        some a2, none, none, .error (.alpha2 e), a2.2⟩
    | .ok alpha2 =>
      let afterResponse3 := absorb tape a2.2 52 (3 :: responseBytes body 3)
      let a3 := candidate tape afterResponse3
      match a3.1 with
      | .error e => ⟨afterIncrement, afterResponse1, a1, some afterResponse2,
          some a2, some afterResponse3, some a3, .error (.alpha3 e), a3.2⟩
      | .ok alpha3 => ⟨afterIncrement, afterResponse1, a1,
          some afterResponse2, some a2, some afterResponse3, some a3,
          .ok (Success.mk alpha1 alpha2 alpha3), a3.2⟩

theorem trace_exact (increment : IncrementProducer) (out : OODResult)
    (gamma : K) (middle : FSLiveSelectedMiddleQueryRho.Success) (body : Bytes)
    (tape : Tape) (start : Transcript) :
    run tape (laterScript increment out gamma middle body start.digest) start.oracle =
      (some ((trace increment out gamma middle body tape start).result,
        (trace increment out gamma middle body tape start).final.digest),
       (trace increment out gamma middle body tape start).final.oracle) := by
  unfold laterScript trace
  rw [run_bind, run_absorb]
  simp only [Prod.fst, Prod.snd, run_bind]
  rw [run_absorb]
  simp only [Prod.fst, Prod.snd, run_bind, run_candidate]
  cases a1Result : (candidate tape
      (absorb tape (absorb tape start 1 (increment.bytes out gamma middle body))
        52 (1 :: responseBytes body 1))).1 with
  | error e => simp [a1Result, run]
  | ok alpha1 =>
    simp only [a1Result, run_bind]
    rw [run_absorb]
    simp only [Prod.fst, Prod.snd, run_bind, run_candidate]
    cases a2Result : (candidate tape
        (absorb tape
          (candidate tape
            (absorb tape
              (absorb tape start 1 (increment.bytes out gamma middle body))
              52 (1 :: responseBytes body 1))).2
          52 (2 :: responseBytes body 2))).1 with
    | error e => simp [a1Result, a2Result, run]
    | ok alpha2 =>
      simp only [a2Result, run_bind]
      rw [run_absorb]
      simp only [Prod.fst, Prod.snd, run_bind, run_candidate]
      cases a3Result : (candidate tape
          (absorb tape
            (candidate tape
              (absorb tape
                (candidate tape
                  (absorb tape
                    (absorb tape start 1 (increment.bytes out gamma middle body))
                    52 (1 :: responseBytes body 1))).2
                52 (2 :: responseBytes body 2))).2
            52 (3 :: responseBytes body 3))).1 <;>
        simp [a1Result, a2Result, a3Result, run]

theorem literal_response_ranges (body : Bytes) :
    responseBytes body 1 = (body.drop 6768).take 96 /\
    responseBytes body 2 = (body.drop 6864).take 96 /\
    responseBytes body 3 = (body.drop 6960).take 96 := by
  simp [responseBytes]

#print axioms trace_exact
#print axioms literal_response_ranges
#print axioms Success.coins_literal

end AspisV8Completion.FSLiveLaterRelationSuffix
