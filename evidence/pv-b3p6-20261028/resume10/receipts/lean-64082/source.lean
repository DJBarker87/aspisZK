import PV_B3P_DigitRead10227
import PV_B3P_NineUnroll9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

theorem next_zero10 : Usize.wrapping_add 0#usize 1#usize = 1#usize := next_exact _ _ rfl
#print axioms next_zero10

theorem digit_loop_ten10 (values : Array aspis_core.field.QM31 16#usize)
    (offset : Option Usize) (range : DigitRange10) :
    loop (usize_body (digit_source_step10 values offset) 10#usize) (range,0#usize) =
      PV_B3P_Ordered227.fold (digit_source_step10 values offset)
        [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize,9#usize] range := by
  rw [usize_loop_plan (digit_source_step10 values offset) 10#usize 0#usize 10 range rfl]
  simp only [usize_plan,next_zero10,next_1,next_2,next_3,next_4,next_5,next_6,next_7,next_8,next_9,PV_B3P_Ordered227.fold]
#print axioms digit_loop_ten10
end PV_B3P_Binding10227
