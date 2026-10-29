import PV_B3P_InternalBinding12227
import PV_B3P_RangeFold13227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Binding12227 PV_B3P_Binding13227 Result
set_option autoImplicit false

theorem internal_indices15 : usize_indices11 15 1#usize =
    [1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize,
      9#usize,10#usize,11#usize,12#usize,13#usize,14#usize,15#usize] := by
  simp only [usize_indices11,next11_20_1,next11_20_2,next11_20_3,next11_20_4,
    next11_20_5,next11_20_6,next11_20_7,next11_20_8,next11_20_9,next11_20_10,
    next11_20_11,next11_20_12,next11_20_13,next11_20_14,next11_20_15]

def native_internal_sum15 (state : InternalState12) (sum : InternalSum12) : Result InternalSum12 :=
  loop (usize_body (internal_sum_step12 state) 16#usize) (sum,1#usize)

theorem native_internal_sum_binding15 (state : InternalState12) (sum : InternalSum12) :
    native_internal_sum15 state sum = internal_sum_sequence12 state sum := by
  unfold native_internal_sum15
  rw [loop_as_fold11 _ 16#usize 1#usize 15 sum (by rfl),internal_indices15]
  exact (internal_sum_sequence_fold12 state sum).symm
#print axioms internal_indices15
#print axioms native_internal_sum_binding15
end PV_B3P_Native15227
