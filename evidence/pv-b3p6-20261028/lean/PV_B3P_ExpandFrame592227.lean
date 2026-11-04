import PV_B3P_ExpandEvents592227
namespace PV_B3P_ExpandFrame592227
open Aeneas Aeneas.Std PV_B3P_CountdownEvents592227 PV_B3P_ExpandEvents592227
set_option autoImplicit false
/-- Actual guarded Usize countdown equals truncated subtraction after any
number of completed private-loop steps, including exhausted stutters. -/
theorem countdown_value (initial : Usize) (n : Nat) :
    (counter initial n).val = initial.val-n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (step (counter initial n)).val = initial.val-(n+1)
    by_cases active : 0 < (counter initial n).val
    · simp only [step,if_pos active]
      rw [PV_B3P_Offset226V3.sub_value _ _ (by change 1 ≤ (counter initial n).val; omega)]
      change (counter initial n).val-1 = initial.val-(n+1)
      omega
    · simp only [step,if_neg active]
      omega

/-- Closed-form coordinate and width updates correspond to the actual scalar
stores. The caller's fixed count bounds the active doubling before capacity. -/
theorem coordinate_step (start count n : Nat) (active : depth count n < count) :
    start+depth count (n+1) = start+depth count n+1 := by
  rw [depth_step,if_pos active]
  omega

theorem width_value_step (count n : Nat) (active : depth count n < count) :
    2^(depth count (n+1)) = 2^(depth count n)*2 := by
  rw [depth_step,if_pos active,Nat.pow_succ]

#print axioms countdown_value
#print axioms coordinate_step
#print axioms width_value_step
end PV_B3P_ExpandFrame592227
