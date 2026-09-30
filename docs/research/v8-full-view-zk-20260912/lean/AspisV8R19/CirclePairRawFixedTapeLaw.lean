import AspisV8R19.CirclePairRawIndependentLaw
import AspisV8R19.IndependentMeanFixedTapeCircle

/-! Fixed-tape presentation of the raw-word circle-pair law.

The only semantic premise is the explicit `FreshFrom` hypothesis inherited
from the cached-history law.  The fixed tape retains unused suffix entries and
the complete error/result/state view.
-/
set_option autoImplicit false
namespace AspisV8R19.CirclePairRawFixedTapeLaw

open Aeneas Aeneas.Std Result AspisR72Sampler
open DuplexFrames SourceDuplexStep
open MemoizedProgramLaw OracleFiniteSupport OracleResampling
open AdaptiveFirstReadLaw
open CirclePairPrefixProgram CirclePairHistoryLaw
open IndependentAnswerTransport
open SamplerRawStateRepresentation
open IndependentMeanFixedTape
open AspisV8R19.IndependentMeanFixedTapeCircle
open AspisV8R19.QM31SamplerProgram
open SamplerObservation SqueezeOracleBridge

def recodeWithin {I A B O : Type} (e : A ≃ B) :
    {p : Program I A O} → {n : Nat} → Within p n →
      Within (recodeAnswers e p) n
  | _, _, .done o n => .done o n
  | _, _, .ask i next n h =>
      Within.ask i (fun b => recodeAnswers e (next (e.symm b))) n
        (fun b => recodeWithin e (h (e.symm b)))

def circlePairRawWithin
    (hc : ∀ s : State, Within (challengeProgram s) 66)
    (vectorLabel : DuplexFrames.Byte) (vector0 vector1 : Bytes) (s : State) :
    Within
      (recodeAnswers stateRawEquiv
        (program vectorLabel vector0 vector1 s)) 794 :=
  recodeWithin stateRawEquiv
    (circlePair_within hc vectorLabel vector0 vector1 s)

def rawTapeObservation
    (history : Trace)
    (test : Result (View Bytes State CirclePairPrefixProgram.PairResult) → ℚ)
    (view : View Bytes (Fin 8 → RawWord) CirclePairPrefixProgram.PairResult) : ℚ :=
  let decoded := decodeView stateRawEquiv view
  test (.ok (decodeTrace history ++ decoded.1, decoded.2))

theorem mean_circlePairRawTape_eq_independentMean
    (hc : ∀ s : State, Within (challengeProgram s) 66)
    (vectorLabel : DuplexFrames.Byte) (vector0 vector1 : Bytes)
    (s : State) (history : Trace)
    (test : Result (View Bytes State CirclePairPrefixProgram.PairResult) → ℚ) :
    mean (fun tape : Fin 794 → (Fin 8 → RawWord) =>
      rawTapeObservation history test
        (evalTape (circlePairRawWithin hc vectorLabel vector0 vector1 s) tape)) =
      independentMean
        (recodeAnswers stateRawEquiv
          (program vectorLabel vector0 vector1 s))
        (rawTapeObservation history test) :=
  mean_evalTape_eq_independentMean
    (recodeAnswers stateRawEquiv (program vectorLabel vector0 vector1 s))
    794
    (circlePairRawWithin hc vectorLabel vector0 vector1 s)
    (rawTapeObservation history test)

theorem cached_oracle_history_eq_raw_fixed_tape
    (hc : ∀ s : State, Within (challengeProgram s) 66)
    (vectorLabel : DuplexFrames.Byte) (vector0 vector1 : Bytes)
    (s : State) (history : Trace)
    (t : AspisV8PairedCommitment.Table Bytes State)
    (fallback : State)
    (fresh : FreshFrom (program vectorLabel vector0 vector1 s) t)
    (test : Result (View Bytes State CirclePairPrefixProgram.PairResult) → ℚ) :
    mean (fun H :
      {i // i ∈ support (program vectorLabel vector0 vector1 s)} → State =>
      test (observe
        (complete t (extend (support (program vectorLabel vector0 vector1 s)) H fallback))
        vectorLabel vector0 vector1 s history)) =
      mean (fun tape : Fin 794 → (Fin 8 → RawWord) =>
        rawTapeObservation history test
          (evalTape
            (circlePairRawWithin hc vectorLabel vector0 vector1 s) tape)) := by
  rw [CirclePairRawIndependentLaw.cached_oracle_history_eq_raw_independentMean
    vectorLabel vector0 vector1 s history t fallback fresh test]
  symm
  have hobs : rawTapeObservation history test =
      (((fun view => test (.ok (decodeTrace history ++ view.1, view.2))) ∘
        decodeView stateRawEquiv)) := by
    funext view
    cases view
    rfl
  rw [← hobs]
  exact mean_circlePairRawTape_eq_independentMean hc vectorLabel vector0 vector1 s
    history test

#print axioms cached_oracle_history_eq_raw_fixed_tape
end AspisV8R19.CirclePairRawFixedTapeLaw
