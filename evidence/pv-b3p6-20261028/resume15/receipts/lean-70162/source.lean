import PV_B3P_InterpolationCell15_07227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def interpolation_tail15_06 (weights : Array aspis_core.field.QM31 3#usize) (column0 column1 column2 : Array U32 16#usize) (state : Array aspis_core.field.QM31 16#usize) : Result (Array aspis_core.field.QM31 16#usize) := do
  let i18 ← Array.index_usize column0 6#usize
  let i19 ← Array.index_usize column1 6#usize
  let i20 ← Array.index_usize column2 6#usize
  let q6 ← reference_poseidon.interpolate_column227 weights i18 i19 i20
  let output7 ← Array.update state 6#usize q6
  let i21 ← Array.index_usize column0 7#usize
  let i22 ← Array.index_usize column1 7#usize
  let i23 ← Array.index_usize column2 7#usize
  let q7 ← reference_poseidon.interpolate_column227 weights i21 i22 i23
  let output8 ← Array.update output7 7#usize q7
  let i24 ← Array.index_usize column0 8#usize
  let i25 ← Array.index_usize column1 8#usize
  let i26 ← Array.index_usize column2 8#usize
  let q8 ← reference_poseidon.interpolate_column227 weights i24 i25 i26
  let output9 ← Array.update output8 8#usize q8
  let i27 ← Array.index_usize column0 9#usize
  let i28 ← Array.index_usize column1 9#usize
  let i29 ← Array.index_usize column2 9#usize
  let q9 ← reference_poseidon.interpolate_column227 weights i27 i28 i29
  let output10 ← Array.update output9 9#usize q9
  let i30 ← Array.index_usize column0 10#usize
  let i31 ← Array.index_usize column1 10#usize
  let i32 ← Array.index_usize column2 10#usize
  let q10 ← reference_poseidon.interpolate_column227 weights i30 i31 i32
  let output11 ← Array.update output10 10#usize q10
  let i33 ← Array.index_usize column0 11#usize
  let i34 ← Array.index_usize column1 11#usize
  let i35 ← Array.index_usize column2 11#usize
  let q11 ← reference_poseidon.interpolate_column227 weights i33 i34 i35
  let output12 ← Array.update output11 11#usize q11
  let i36 ← Array.index_usize column0 12#usize
  let i37 ← Array.index_usize column1 12#usize
  let i38 ← Array.index_usize column2 12#usize
  let q12 ← reference_poseidon.interpolate_column227 weights i36 i37 i38
  let output13 ← Array.update output12 12#usize q12
  let i39 ← Array.index_usize column0 13#usize
  let i40 ← Array.index_usize column1 13#usize
  let i41 ← Array.index_usize column2 13#usize
  let q13 ← reference_poseidon.interpolate_column227 weights i39 i40 i41
  let output14 ← Array.update output13 13#usize q13
  let i42 ← Array.index_usize column0 14#usize
  let i43 ← Array.index_usize column1 14#usize
  let i44 ← Array.index_usize column2 14#usize
  let q14 ← reference_poseidon.interpolate_column227 weights i42 i43 i44
  let output15 ← Array.update output14 14#usize q14
  let i45 ← Array.index_usize column0 15#usize
  let i46 ← Array.index_usize column1 15#usize
  let i47 ← Array.index_usize column2 15#usize
  let q15 ← reference_poseidon.interpolate_column227 weights i45 i46 i47
  Array.update output15 15#usize q15
attribute [local irreducible] Array.index_usize Array.update reference_terminal.read227 reference_terminal.absorption_lane227 reference_poseidon.interpolate_column227 interpolation_step15 interpolation_tail15_07
theorem interpolation_cell15_06 (weights : Array aspis_core.field.QM31 3#usize) (column0 column1 column2 : Array U32 16#usize) (state : Array aspis_core.field.QM31 16#usize) :
    interpolation_tail15_06 weights column0 column1 column2 state =
      (interpolation_step15 weights column0 column1 column2 state 6#usize >>= interpolation_tail15_07 weights column0 column1 column2) := by
  unfold interpolation_tail15_06
  conv_rhs => simp only [interpolation_step15,PV_B3P_Ordered227.bind_assoc]
  apply bind_equal9
  intro v0
  apply bind_equal9
  intro v1
  apply bind_equal9
  intro v2
  apply bind_equal9
  intro v3
  apply bind_equal9
  intro next
  unfold interpolation_tail15_07
  rfl
theorem interpolation_fold15_06 (weights : Array aspis_core.field.QM31 3#usize) (column0 column1 column2 : Array U32 16#usize) (state : Array aspis_core.field.QM31 16#usize) :
    interpolation_tail15_06 weights column0 column1 column2 state =
      PV_B3P_Ordered227.fold (interpolation_step15 weights column0 column1 column2) [6#usize,7#usize,8#usize,9#usize,10#usize,11#usize,12#usize,13#usize,14#usize,15#usize] state := by
  rw [interpolation_cell15_06]
  simp only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc]
  apply congrArg (fun k => interpolation_step15 weights column0 column1 column2 state 6#usize >>= k)
  funext next
  exact interpolation_fold15_07 weights column0 column1 column2 next
#print axioms interpolation_cell15_06
#print axioms interpolation_fold15_06
end PV_B3P_Native15227
