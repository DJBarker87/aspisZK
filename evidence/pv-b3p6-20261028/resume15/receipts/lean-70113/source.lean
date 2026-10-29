import PV_B3P_NativeInternalSum15227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227 PV_B3P_Binding11227 PV_B3P_Binding12227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def native_internal_finish15 (state : InternalState12) (old_zero : Array U32 4#usize)
    (part_sum : InternalSum12) : Result InternalState12 := do
  let full_sum ← reference_poseidon.internal_full_sum227 part_sum old_zero
  let first ← reference_poseidon.internal_zero227 part_sum old_zero
  let state1 ← Array.update state 0#usize first
  range_loop13 (internal_output_step12 full_sum) 1#usize 16#usize state1

theorem native_internal_finish_binding15 (state : InternalState12)
    (old_zero : Array U32 4#usize) (part_sum : InternalSum12) :
    native_internal_finish15 state old_zero part_sum = internal_finish12 state old_zero part_sum := by
  unfold native_internal_finish15 internal_finish12
  apply bind_equal9
  intro full_sum
  apply bind_equal9
  intro first
  apply bind_equal9
  intro state1
  rw [range_as_fold13 _ 1#usize 16#usize 15 state1 (by rfl),internal_indices15]
  exact (internal_output_fold12_01 full_sum state1).symm
#print axioms native_internal_finish_binding15
end PV_B3P_Native15227
