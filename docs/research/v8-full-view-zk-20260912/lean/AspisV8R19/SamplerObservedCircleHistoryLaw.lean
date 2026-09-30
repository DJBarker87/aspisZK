import AspisV8R19.SamplerObservedCircleProgram
import AspisV8R19.AdaptiveFirstReadLaw

/-! The complete observed secure-circle sampler after an arbitrary visible
prefix.  The second theorem reduces its memoized law to sequential independent
answers under the explicit `FreshFrom` premise.  It does not yet identify that
independent-answer interpreter with a uniform accepted OOD parameter. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerObservedCircleHistoryLaw
open Aeneas Aeneas.Std Result AspisR72Sampler
open SamplerObservation DuplexFrames SourceDuplexStep SqueezeOracleBridge
open SamplerObservedCircleProgram MemoizedProgramLaw
open OracleFiniteSupport OracleResampling AdaptiveFirstReadLaw
open AspisV8R15.ExactTowerBase
noncomputable section

theorem program_exact (H : Bytes → State) (s : State) :
    eval H (program s) = SamplerCircleBridge.modelRun H 3 s := by
  exact BoundedSamplerWrapper.exact_run SamplerCirclePolicy.accept
    transcript.CirclePointSampleError.ChallengeSampleExhausted
    transcript.CirclePointSampleError.ParameterSampleExhausted H 3 s

theorem observe_program (H : Bytes → State) (s : State) (history : Trace) :
    observe H s history =
      .ok (decodeTrace history ++ (eval H (program s)).1,
        (eval H (program s)).2) := by
  rw [public_view, program_exact]

theorem cached_oracle_history_law
    (s : State) (history : Trace)
    (t : AspisV8PairedCommitment.Table Bytes State)
    (fallback : State)
    (test : Result (View Bytes State
      (Except transcript.CirclePointSampleError (QM31Exact × QM31Exact) × State)) → ℚ) :
    mean (fun H : {i // i ∈ support (program s)} → State =>
      test (observe
        (complete t (extend (support (program s)) H fallback)) s history)) =
      lazyMean (program s) t
        (fun view => test (.ok (decodeTrace history ++ view.1, view.2))) := by
  simp only [observe_program]
  exact CachedFiniteSupport.own_support_law
    (I := Bytes) (A := State)
    (O := Except transcript.CirclePointSampleError
      (QM31Exact × QM31Exact) × State)
    (program s) t fallback
    (fun view => test (.ok (decodeTrace history ++ view.1, view.2)))

theorem cached_oracle_history_eq_independentMean
    (s : State) (history : Trace)
    (t : AspisV8PairedCommitment.Table Bytes State)
    (fallback : State)
    (fresh : FreshFrom (program s) t)
    (test : Result (View Bytes State
      (Except transcript.CirclePointSampleError (QM31Exact × QM31Exact) × State)) → ℚ) :
    mean (fun H : {i // i ∈ support (program s)} → State =>
      test (observe
        (complete t (extend (support (program s)) H fallback)) s history)) =
      independentMean (program s)
        (fun view => test (.ok (decodeTrace history ++ view.1, view.2))) := by
  rw [cached_oracle_history_law]
  exact lazyMean_eq_independentMean (program s) t fresh _

#print axioms program_exact
#print axioms observe_program
#print axioms cached_oracle_history_law
#print axioms cached_oracle_history_eq_independentMean
end
end AspisV8R19.SamplerObservedCircleHistoryLaw
