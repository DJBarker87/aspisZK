import PCD_LaneRef.Funs
set_option autoImplicit false
namespace PCD_Checked
open Aeneas Aeneas.Std PCD_LaneRef
/-- Exact Option test used by the frozen first guard. No successful-addition
premise restricts the domain: overflow/none and both equality arms are covered. -/
theorem reference_exact (old next : U64) :
    checked_next old next = .ok (decide (U64.checked_add old 1#u64 = some next)) := by
  unfold checked_next
  cases h : U64.checked_add old 1#u64 with
  | none => simp [lift, bind_tc_ok]
  | some sum => simp [lift, bind_tc_ok]
#print axioms reference_exact
end PCD_Checked
