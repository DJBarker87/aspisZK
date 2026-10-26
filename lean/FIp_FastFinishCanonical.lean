import FIo_FromLimbs
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_FastFinishCanonical
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

theorem finish (s : FIo_Native.fast_pairing.EbyKDot) (out : NE)
    (run : FIo_Native.fast_pairing.EbyKDot.finish s=ok out) : FIo_WideValues.Canon out := by
  unfold FIo_Native.fast_pairing.EbyKDot.finish at run
  repeat' first
  | (solve | cases run)
  | uncase_result
  | head_reduce run
  | split at run
  all_goals
    have same := Result.ok.inj run
    cases same
    exact FIo_FromLimbs.canonical _ _ (by assumption)

#print axioms finish
end AspisR1.FIp_FastFinishCanonical
end
