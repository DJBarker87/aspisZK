import AspisV8R19.AdaptiveFirstReadSource
import AspisV8R19.UniformStateFirstHit

/-! One-step loss boundary for the adaptive first-read source bridge.

The dichotomy is pathwise: a prior trace either leaves both addresses of the
next squeeze fresh, or the state is in the explicit `BadState` event.  The
fraction theorem below is only the independently uniform-state counting bound
for that one prior read-address list; it is not a whole-run union bound,
coupling statement, or source-state uniformity assumption. -/
set_option autoImplicit false
namespace AspisV8R19.AdaptiveFirstReadLoss
open AspisV8R19.AdaptiveFirstReadSource
open AspisV8R19.UniformStateFirstHit
open AspisV8PairedCommitment
open DuplexFrames SourceDuplexStep SourceOraclePrograms
open AdaptiveFirstReadLaw
noncomputable section

theorem fresh_or_bad_state (tr : List (Bytes × State)) (s : State) :
    FreshFrom (squeezeProgram s) (traceCache (fun _ => none) tr) ∨
      BadState (tr.map Prod.fst) (bytes s) := by
  by_cases fresh : Fresh (tr.map Prod.fst) (bytes s)
  · exact Or.inl (squeezeProgram_fresh_after_trace tr s fresh)
  · right
    by_contra bad_absent
    exact fresh ((fresh_iff (tr.map Prod.fst) (bytes s)).mpr bad_absent)

theorem uniform_bad_fraction_bound_for_trace (tr : List (Bytes × State)) :
    uniformBadFraction (tr.map Prod.fst) ≤
      ((tr.map Prod.fst).length : ℚ) / (256 ^ 32 : ℚ) := by
  exact uniform_bad_bound (tr.map Prod.fst)

#print axioms fresh_or_bad_state
#print axioms uniform_bad_fraction_bound_for_trace
end
end AspisV8R19.AdaptiveFirstReadLoss
