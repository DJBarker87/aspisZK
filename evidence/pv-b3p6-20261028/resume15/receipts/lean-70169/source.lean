import PV_B3P_InterpolationCell15_00227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def native_interpolation15 (weights : Array aspis_core.field.QM31 3#usize) (column0 column1 column2 : Array U32 16#usize) : Result (Array aspis_core.field.QM31 16#usize) :=
  range_loop13 (interpolation_step15 weights column0 column1 column2) 0#usize 16#usize
    (Array.repeat 16#usize aspis_core.field.QM31.ZERO)

theorem native_interpolation_binding15 (weights : Array aspis_core.field.QM31 3#usize) (column0 column1 column2 : Array U32 16#usize) :
    native_interpolation15 weights column0 column1 column2 = reference_poseidon.interpolate_three_constant_columns weights column0 column1 column2 := by
  unfold native_interpolation15
  rw [range_sixteen13]
  exact (interpolation_fold15_00 weights column0 column1 column2 _).symm
#print axioms native_interpolation_binding15
end PV_B3P_Native15227
