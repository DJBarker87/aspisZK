import PV_B3P_UsizeLoop9227
import PV_B3P_ReverseLoop9227
import PV_B3P_Ordered227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem result_right {α : Type} (r : Result α) : (r >>= Result.ok) = r := by
  cases r <;> rfl
#print axioms result_right

theorem forward_nine {α : Type} (step : α → Usize → Result α) (initial : α) :
    usize_plan step 9 1#usize initial = (do
    let s0 ← step initial 1#usize
    let s1 ← step s0 2#usize
    let s2 ← step s1 3#usize
    let s3 ← step s2 4#usize
    let s4 ← step s3 5#usize
    let s5 ← step s4 6#usize
    let s6 ← step s5 7#usize
    let s7 ← step s6 8#usize
    step s7 9#usize) := by
  simp only [usize_plan,lift,bind_tc_ok,result_right]
#print axioms forward_nine

theorem reverse_nine {α : Type} (step : α → Usize → Result α) (initial : α) :
    reverse_plan step 9 9#usize initial = (do
    let s0 ← step initial 8#usize
    let s1 ← step s0 7#usize
    let s2 ← step s1 6#usize
    let s3 ← step s2 5#usize
    let s4 ← step s3 4#usize
    let s5 ← step s4 3#usize
    let s6 ← step s5 2#usize
    let s7 ← step s6 1#usize
    step s7 0#usize) := by
  simp only [reverse_plan,lift,bind_tc_ok,result_right]
#print axioms reverse_nine

end PV_B3P_Binding9227
