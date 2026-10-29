import PV_B3P_NativeInterpolation15227
import PV_B3P_InterpolationNativeReads15227
import PV_B3P_BoundedFold15227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def interpolation_source_step15 (weights : Array aspis_core.field.QM31 3#usize) (column0 column1 column2 : Array U32 16#usize) (state : Array aspis_core.field.QM31 16#usize) (lane : Usize) : Result (Array aspis_core.field.QM31 16#usize) := do
  let value ← interpolation_native_value15 weights column0 column1 column2 lane
  Array.update state lane value

theorem interpolation_source_step_binding15 (weights : Array aspis_core.field.QM31 3#usize) (column0 column1 column2 : Array U32 16#usize) (state : Array aspis_core.field.QM31 16#usize)
    (lane : Usize) (bound : lane.val < 16) :
    interpolation_source_step15 weights column0 column1 column2 state lane = interpolation_step15 weights column0 column1 column2 state lane := by
  unfold interpolation_source_step15 interpolation_step15
  rw [interpolation_native_value_binding15 weights column0 column1 column2 lane bound]
  simp only [PV_B3P_Ordered227.bind_assoc]

def interpolation_source15 (weights : Array aspis_core.field.QM31 3#usize) (column0 column1 column2 : Array U32 16#usize) : Result (Array aspis_core.field.QM31 16#usize) :=
  loop (usize_body (interpolation_source_step15 weights column0 column1 column2) 16#usize)
    (Array.repeat 16#usize aspis_core.field.QM31.ZERO,0#usize)

theorem interpolation_source_binding15 (weights : Array aspis_core.field.QM31 3#usize) (column0 column1 column2 : Array U32 16#usize) :
    interpolation_source15 weights column0 column1 column2 = reference_poseidon.interpolate_three_constant_columns weights column0 column1 column2 := by
  rw [←native_interpolation_binding15]
  unfold interpolation_source15 native_interpolation15
  rw [loop_as_fold11 _ 16#usize 0#usize 16 _ (by rfl),
    range_as_fold13 _ 0#usize 16#usize 16 _ (by rfl)]
  apply fold_pointwise15
  intro index member state
  exact interpolation_source_step_binding15 weights column0 column1 column2 state index (indices_bound_sixteen15 index member)
#print axioms interpolation_source_step_binding15
#print axioms interpolation_source_binding15
end PV_B3P_Native15227
