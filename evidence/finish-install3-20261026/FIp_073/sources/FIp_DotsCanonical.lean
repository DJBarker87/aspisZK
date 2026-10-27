import FIp_NativeDots
import FIp_FastFinishCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_DotsCanonical
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NE)

theorem helper (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize) (out : NE)
    (run : FIp_NativeDots.fast_dots.four_dots_one q g slot=ok out) : FIo_WideValues.Canon out := by
  unfold FIp_NativeDots.fast_dots.four_dots_one at run
  repeat' first
  | (solve | cases run)
  | uncase_result
  | head_reduce run
  | split at run
  all_goals
    apply (FIo_WideValues.add _ _ out ?_ ?_ run).1
    · exact FIo_FromLimbs.canonical _ _ (by assumption)
    · exact FIp_FastFinishCanonical.finish _ _ (by assumption)

#print axioms helper
end AspisR1.FIp_DotsCanonical
end
