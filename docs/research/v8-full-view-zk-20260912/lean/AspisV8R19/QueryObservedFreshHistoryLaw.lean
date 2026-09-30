import AspisV8R19.QueryObservedHistoryLaw
import AspisV8R19.AdaptiveFirstReadLaw

/-! The selected q22 observer law after an arbitrary visible prefix, under the
single source premise that every reached q22 oracle address is fresh from the
prior memo table.  This is deliberately conditional: connecting the callback's
actual pre-q22 execution to `history`, `t`, and this freshness premise remains
the next source-specific obligation. -/
set_option autoImplicit false
namespace AspisV8R19.QueryObservedFreshHistoryLaw
open Aeneas Aeneas.Std Result AspisR86Query
open SamplerObservation DuplexFrames SourceDuplexStep SqueezeOracleBridge
open QueryObservedProgram QueryObservedHistoryLaw
open MemoizedProgramLaw OracleFiniteSupport OracleResampling
open AdaptiveFirstReadLaw
noncomputable section

theorem cached_oracle_history_eq_independentMean
    (s : State) (history : Trace)
    (t : AspisV8PairedCommitment.Table Bytes State)
    (fallback : State)
    (fresh : FreshFrom (Q22SamplerProgram.challengeProgram s) t)
    (test : Result (View Bytes State Q22SamplerProgram.Result) → ℚ) :
    mean (fun H :
      {i // i ∈ support (Q22SamplerProgram.challengeProgram s)} → State =>
      test (observe
        (complete t
          (extend (support (Q22SamplerProgram.challengeProgram s)) H fallback))
        s history)) =
      independentMean (Q22SamplerProgram.challengeProgram s)
        (fun view => test (.ok (decodeTrace history ++ view.1, view.2))) := by
  rw [cached_oracle_history_law]
  exact lazyMean_eq_independentMean
    (Q22SamplerProgram.challengeProgram s) t fresh _

#print axioms cached_oracle_history_eq_independentMean
end
end AspisV8R19.QueryObservedFreshHistoryLaw
