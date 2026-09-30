import AspisV8R19.CirclePairPrefixProgram
import AspisV8R19.AdaptiveFirstReadLaw

/-! Memoized observer laws for the exact OOD pair prefix.

The supplied history is preserved in the visible view and all pair-prefix
errors/results/states remain in the program outcome.  The freshness premise in
the second theorem is explicit; this file proves no freshness or callback
equivalence. -/
set_option autoImplicit false
namespace AspisV8R19.CirclePairHistoryLaw
open Aeneas Aeneas.Std Result AspisR72Sampler
open SamplerObservation DuplexFrames SourceDuplexStep SqueezeOracleBridge
open CirclePairPrefixProgram MemoizedProgramLaw
open OracleFiniteSupport OracleResampling AdaptiveFirstReadLaw
open AspisV8R15.ExactTowerBase
noncomputable section

def observe (H : Bytes → State) (vectorLabel : DuplexFrames.Byte)
    (vector0 vector1 : Bytes) (s : State) (history : Trace) :
    Result (View Bytes State CirclePairPrefixProgram.PairResult) :=
  .ok (decodeTrace history ++
      (eval H (program vectorLabel vector0 vector1 s)).1,
    (eval H (program vectorLabel vector0 vector1 s)).2)

theorem program_exact (H : Bytes → State) (vectorLabel : DuplexFrames.Byte)
    (vector0 vector1 : Bytes) (s : State) :
    eval H (program vectorLabel vector0 vector1 s) =
      CirclePairPrefixProgram.run H vectorLabel vector0 vector1 s :=
  CirclePairPrefixProgram.eval_run H vectorLabel vector0 vector1 s

theorem observe_program (H : Bytes → State) (vectorLabel : DuplexFrames.Byte)
    (vector0 vector1 : Bytes) (s : State) (history : Trace) :
    observe H vectorLabel vector0 vector1 s history =
      .ok (decodeTrace history ++
        (eval H (program vectorLabel vector0 vector1 s)).1,
        (eval H (program vectorLabel vector0 vector1 s)).2) := by
  rfl

theorem cached_oracle_history_law
    (vectorLabel : DuplexFrames.Byte) (vector0 vector1 : Bytes)
    (s : State) (history : Trace)
    (t : AspisV8PairedCommitment.Table Bytes State)
    (fallback : State)
    (test : Result (View Bytes State CirclePairPrefixProgram.PairResult) → ℚ) :
    mean (fun H :
      {i // i ∈ support (program vectorLabel vector0 vector1 s)} → State =>
      test (observe
        (complete t (extend (support (program vectorLabel vector0 vector1 s)) H fallback))
        vectorLabel vector0 vector1 s history)) =
      lazyMean (program vectorLabel vector0 vector1 s) t
        (fun view => test (.ok (decodeTrace history ++ view.1, view.2))) := by
  simp only [observe]
  exact CachedFiniteSupport.own_support_law
    (I := Bytes) (A := State) (O := CirclePairPrefixProgram.PairResult)
    (program vectorLabel vector0 vector1 s) t fallback
    (fun view => test (.ok (decodeTrace history ++ view.1, view.2)))

theorem cached_oracle_history_eq_independentMean
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
      independentMean (program vectorLabel vector0 vector1 s)
        (fun view => test (.ok (decodeTrace history ++ view.1, view.2))) := by
  rw [cached_oracle_history_law]
  exact lazyMean_eq_independentMean
    (program vectorLabel vector0 vector1 s) t fresh _

#print axioms program_exact
#print axioms observe_program
#print axioms cached_oracle_history_law
#print axioms cached_oracle_history_eq_independentMean
end
end AspisV8R19.CirclePairHistoryLaw
