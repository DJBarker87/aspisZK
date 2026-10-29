import PV_B3P_IndexSteps9227
import PV_B3P_UsizeLoop9227
import PV_B3P_ReverseLoop9227
import PV_B3P_Ordered227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem result_right {α : Type} (r : Result α) : (r >>= Result.ok) = r := by
  cases r <;> rfl
#print axioms result_right

theorem next_1 : Usize.wrapping_add 1#usize 1#usize = 2#usize := next_exact _ _ rfl
#print axioms next_1

theorem previous_1 : Usize.wrapping_sub 1#usize 1#usize = 0#usize := previous_exact _ _ rfl
#print axioms previous_1

theorem next_2 : Usize.wrapping_add 2#usize 1#usize = 3#usize := next_exact _ _ rfl
#print axioms next_2

theorem previous_2 : Usize.wrapping_sub 2#usize 1#usize = 1#usize := previous_exact _ _ rfl
#print axioms previous_2

theorem next_3 : Usize.wrapping_add 3#usize 1#usize = 4#usize := next_exact _ _ rfl
#print axioms next_3

theorem previous_3 : Usize.wrapping_sub 3#usize 1#usize = 2#usize := previous_exact _ _ rfl
#print axioms previous_3

theorem next_4 : Usize.wrapping_add 4#usize 1#usize = 5#usize := next_exact _ _ rfl
#print axioms next_4

theorem previous_4 : Usize.wrapping_sub 4#usize 1#usize = 3#usize := previous_exact _ _ rfl
#print axioms previous_4

theorem next_5 : Usize.wrapping_add 5#usize 1#usize = 6#usize := next_exact _ _ rfl
#print axioms next_5

theorem previous_5 : Usize.wrapping_sub 5#usize 1#usize = 4#usize := previous_exact _ _ rfl
#print axioms previous_5

theorem next_6 : Usize.wrapping_add 6#usize 1#usize = 7#usize := next_exact _ _ rfl
#print axioms next_6

theorem previous_6 : Usize.wrapping_sub 6#usize 1#usize = 5#usize := previous_exact _ _ rfl
#print axioms previous_6

theorem next_7 : Usize.wrapping_add 7#usize 1#usize = 8#usize := next_exact _ _ rfl
#print axioms next_7

theorem previous_7 : Usize.wrapping_sub 7#usize 1#usize = 6#usize := previous_exact _ _ rfl
#print axioms previous_7

theorem next_8 : Usize.wrapping_add 8#usize 1#usize = 9#usize := next_exact _ _ rfl
#print axioms next_8

theorem previous_8 : Usize.wrapping_sub 8#usize 1#usize = 7#usize := previous_exact _ _ rfl
#print axioms previous_8

theorem next_9 : Usize.wrapping_add 9#usize 1#usize = 10#usize := next_exact _ _ rfl
#print axioms next_9

theorem previous_9 : Usize.wrapping_sub 9#usize 1#usize = 8#usize := previous_exact _ _ rfl
#print axioms previous_9

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
  simp only [usize_plan,lift,bind_tc_ok,result_right,next_1,next_2,next_3,next_4,next_5,next_6,next_7,next_8,next_9]
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
  simp only [reverse_plan,lift,bind_tc_ok,result_right,previous_1,previous_2,previous_3,previous_4,previous_5,previous_6,previous_7,previous_8,previous_9]
#print axioms reverse_nine

end PV_B3P_Binding9227
