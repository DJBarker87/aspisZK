import PV_B3P_InterpolationStep15227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def interpolation_tail15_15 (weights : Array aspis_core.field.QM31 3#usize) (column0 column1 column2 : Array U32 16#usize) (state : Array aspis_core.field.QM31 16#usize) : Result (Array aspis_core.field.QM31 16#usize) := do
  let i45 ← Array.index_usize column0 15#usize
  let i46 ← Array.index_usize column1 15#usize
  let i47 ← Array.index_usize column2 15#usize
  let q15 ← reference_poseidon.interpolate_column227 weights i45 i46 i47
  Array.update state 15#usize q15
attribute [local irreducible] Array.index_usize Array.update reference_terminal.read227 reference_terminal.absorption_lane227 reference_poseidon.interpolate_column227 interpolation_step15
theorem interpolation_cell15_15 (weights : Array aspis_core.field.QM31 3#usize) (column0 column1 column2 : Array U32 16#usize) (state : Array aspis_core.field.QM31 16#usize) :
    interpolation_tail15_15 weights column0 column1 column2 state =
      (interpolation_step15 weights column0 column1 column2 state 15#usize >>= Result.ok) := by
  unfold interpolation_tail15_15
  conv_rhs => simp only [interpolation_step15,PV_B3P_Ordered227.bind_assoc]
  apply bind_equal9
  intro v0
  apply bind_equal9
  intro v1
  apply bind_equal9
  intro v2
  apply bind_equal9
  intro v3
  exact (PV_B3P_Binding9227.result_right _).symm
theorem interpolation_fold15_15 (weights : Array aspis_core.field.QM31 3#usize) (column0 column1 column2 : Array U32 16#usize) (state : Array aspis_core.field.QM31 16#usize) :
    interpolation_tail15_15 weights column0 column1 column2 state =
      PV_B3P_Ordered227.fold (interpolation_step15 weights column0 column1 column2) [15#usize] state := by
  rw [interpolation_cell15_15]
  simp only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc]
  rfl
#print axioms interpolation_cell15_15
#print axioms interpolation_fold15_15
end PV_B3P_Native15227
