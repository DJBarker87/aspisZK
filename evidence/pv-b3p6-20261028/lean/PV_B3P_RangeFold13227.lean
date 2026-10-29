import PV_B3P_RangeBinding13227
import PV_B3P_Indices2011227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_Binding9227 PV_B3P_Binding11227
set_option autoImplicit false

theorem range_as_fold13 {α : Type} (step : α → Usize → Result α)
    (start stop : Usize) (n : Nat) (state : α) (bound : start.val+n=stop.val) :
    range_loop13 step start stop state =
      PV_B3P_Ordered227.fold step (usize_indices11 n start) state :=
  (range_plan13 step start stop n state bound).trans (plan_as_fold11 step n start state)

theorem indices_sixteen13 : usize_indices11 16 0#usize =
    [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,
      8#usize,9#usize,10#usize,11#usize,12#usize,13#usize,14#usize,15#usize] := by
  simp only [usize_indices11,next11_20_0,next11_20_1,next11_20_2,next11_20_3,
    next11_20_4,next11_20_5,next11_20_6,next11_20_7,next11_20_8,next11_20_9,
    next11_20_10,next11_20_11,next11_20_12,next11_20_13,next11_20_14,next11_20_15]

theorem range_sixteen13 {α : Type} (step : α → Usize → Result α) (state : α) :
    range_loop13 step 0#usize 16#usize state =
      PV_B3P_Ordered227.fold step
        [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,
          8#usize,9#usize,10#usize,11#usize,12#usize,13#usize,14#usize,15#usize] state := by
  rw [range_as_fold13 step 0#usize 16#usize 16 state (by rfl),indices_sixteen13]
#print axioms range_as_fold13
#print axioms indices_sixteen13
#print axioms range_sixteen13
end PV_B3P_Binding13227
