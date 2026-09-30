import AspisV8R19.QueryObservedProgram

/-! Memoized q22 observation with an arbitrary prior visible history.  The
history and memo table are intentionally independent parameters: this is a
local observer law, not a source-prefix consistency theorem. -/
set_option autoImplicit false
namespace AspisV8R19.QueryObservedHistoryLaw
open Aeneas Aeneas.Std Result AspisR86Query
open SamplerObservation DuplexFrames SourceDuplexStep SqueezeOracleBridge
open QueryObservedProgram MemoizedProgramLaw OracleFiniteSupport OracleResampling
noncomputable section

theorem cached_oracle_history_law
    (s : State) (history : Trace)
    (t : AspisV8PairedCommitment.Table Bytes State)
    (fallback : State)
    (test : Result (View Bytes State Q22SamplerProgram.Result) → ℚ) :
    mean (fun H :
      {i // i ∈ support (Q22SamplerProgram.challengeProgram s)} → State =>
      test (observe
        (complete t (extend (support (Q22SamplerProgram.challengeProgram s)) H fallback))
        s history)) =
      lazyMean (Q22SamplerProgram.challengeProgram s) t
        (fun view => test (.ok (decodeTrace history ++ view.1, view.2))) := by
  simp only [public_view, ← Q22SamplerProgram.challenge_exact]
  exact CachedFiniteSupport.own_support_law
    (I := Bytes) (A := State) (O := Q22SamplerProgram.Result)
    (Q22SamplerProgram.challengeProgram s) t fallback
    (fun view => test (.ok (decodeTrace history ++ view.1, view.2)))

#print axioms cached_oracle_history_law
end
end AspisV8R19.QueryObservedHistoryLaw
