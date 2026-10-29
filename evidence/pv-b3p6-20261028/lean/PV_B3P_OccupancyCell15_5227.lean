import PV_B3P_OccupancyCell15_6227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def occupancy_tail15_5 (input_occupancy output_occupancy : aspis_core.field.QM31) (expected_output : aspis_core.field.M31) (opened : Array aspis_core.field.QM31 16#usize) (occupied inverse one_minus both : aspis_core.field.QM31) (state : OccupancyState15) : Result OccupancyState15 := do
  let i10 ← lift (Std.Usize.wrapping_add 2#usize 5#usize)
  let q24 ← Array.index_usize opened i10
  let q25 ← aspis_core.field.QM31.mul one_minus q24
  let q26 ← aspis_core.field.QM31.mul both q25
  let i11 ← lift (Std.Usize.wrapping_add 3#usize 5#usize)
  let occupancy9 ← Array.update state i11 q26
  let i12 ← lift (Std.Usize.wrapping_add 2#usize 6#usize)
  let q27 ← Array.index_usize opened i12
  let q28 ← aspis_core.field.QM31.mul one_minus q27
  let q29 ← aspis_core.field.QM31.mul both q28
  let i13 ← lift (Std.Usize.wrapping_add 3#usize 6#usize)
  let occupancy10 ← Array.update occupancy9 i13 q29
  let i14 ← lift (Std.Usize.wrapping_add 2#usize 7#usize)
  let q30 ← Array.index_usize opened i14
  let q31 ← aspis_core.field.QM31.mul one_minus q30
  let q32 ← aspis_core.field.QM31.mul both q31
  let i15 ← lift (Std.Usize.wrapping_add 3#usize 7#usize)
  let occupancy11 ← Array.update occupancy10 i15 q32
  let q33 ← Array.index_usize opened 10#usize
  let q34 ← aspis_core.field.QM31.mul q33 one_minus
  let q35 ← aspis_core.field.QM31.mul input_occupancy q34
  let q36 ← reference_terminal.lift_m31 expected_output
  let q37 ← aspis_core.field.QM31.sub occupied q36
  let q38 ← aspis_core.field.QM31.mul output_occupancy q37
  let q39 ← aspis_core.field.QM31.add q35 q38
  Array.update occupancy11 11#usize q39
attribute [local irreducible] Array.index_usize Array.update aspis_core.field.QM31.mul aspis_core.field.QM31.add aspis_core.field.QM31.sub reference_terminal.lift_m31 occupancy_step15 occupancy_finish15 occupancy_tail15_6
theorem occupancy_cell15_5 (input_occupancy output_occupancy : aspis_core.field.QM31) (expected_output : aspis_core.field.M31) (opened : Array aspis_core.field.QM31 16#usize) (occupied inverse one_minus both : aspis_core.field.QM31) (state : OccupancyState15) :
    occupancy_tail15_5 input_occupancy output_occupancy expected_output opened occupied inverse one_minus both state =
      (occupancy_step15 opened one_minus both state 5#usize >>= occupancy_tail15_6 input_occupancy output_occupancy expected_output opened occupied inverse one_minus both) := by
  unfold occupancy_tail15_5
  conv_rhs => simp only [occupancy_step15,PV_B3P_Ordered227.bind_assoc,lift,bind_tc_ok]
  simp only [lift,bind_tc_ok]
  apply bind_equal9
  intro v0
  apply bind_equal9
  intro v1
  apply bind_equal9
  intro v2
  apply bind_equal9
  intro v3
  unfold occupancy_tail15_6
  rfl
theorem occupancy_fold15_5 (input_occupancy output_occupancy : aspis_core.field.QM31) (expected_output : aspis_core.field.M31) (opened : Array aspis_core.field.QM31 16#usize) (occupied inverse one_minus both : aspis_core.field.QM31) (state : OccupancyState15) :
    occupancy_tail15_5 input_occupancy output_occupancy expected_output opened occupied inverse one_minus both state =
      (PV_B3P_Ordered227.fold (occupancy_step15 opened one_minus both)
        [5#usize,6#usize,7#usize] state >>= occupancy_finish15 input_occupancy output_occupancy expected_output opened occupied inverse one_minus both) := by
  rw [occupancy_cell15_5]
  simp only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc]
  apply congrArg (fun k => occupancy_step15 opened one_minus both state 5#usize >>= k)
  funext next
  simpa only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc,bind_tc_ok] using occupancy_fold15_6 input_occupancy output_occupancy expected_output opened occupied inverse one_minus both next
#print axioms occupancy_cell15_5
#print axioms occupancy_fold15_5
end PV_B3P_Native15227
