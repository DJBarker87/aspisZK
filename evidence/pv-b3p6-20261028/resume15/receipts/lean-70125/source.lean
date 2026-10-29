import PV_B3P_OccupancyCell15_0227
import PV_B3P_NativeLeading15227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def native_occupancy15 (input_occupancy output_occupancy : aspis_core.field.QM31) (expected_output : aspis_core.field.M31) (opened : Array aspis_core.field.QM31 16#usize) : Result OccupancyState15 := do
  let occupied ← Array.index_usize opened 0#usize
  let inverse ← Array.index_usize opened 1#usize
  let one_minus ←
    aspis_core.field.QM31.sub aspis_core.field.QM31.ONE occupied
  let occupancy := Array.repeat 12#usize aspis_core.field.QM31.ZERO
  let both ← aspis_core.field.QM31.add input_occupancy output_occupancy
  let q ← aspis_core.field.QM31.sub occupied aspis_core.field.QM31.ONE
  let q1 ← aspis_core.field.QM31.mul occupied q
  let q2 ← aspis_core.field.QM31.mul both q1
  let occupancy1 ← Array.update occupancy 0#usize q2
  let q3 ← Array.index_usize opened 9#usize
  let q4 ← aspis_core.field.QM31.mul q3 inverse
  let q5 ← aspis_core.field.QM31.sub q4 occupied
  let q6 ← aspis_core.field.QM31.mul both q5
  let occupancy2 ← Array.update occupancy1 1#usize q6
  let q7 ← aspis_core.field.QM31.mul one_minus inverse
  let q8 ← aspis_core.field.QM31.mul both q7
  let occupancy3 ← Array.update occupancy2 2#usize q8
  let state ← range_loop13 (occupancy_step15 opened one_minus both) 0#usize 8#usize occupancy3
  occupancy_finish15 input_occupancy output_occupancy expected_output opened occupied inverse one_minus both state
attribute [local irreducible] Array.index_usize Array.update aspis_core.field.QM31.mul aspis_core.field.QM31.sub aspis_core.field.QM31.add reference_terminal.lift_m31 occupancy_tail15_0 occupancy_finish15 occupancy_step15
theorem native_occupancy_binding15 (input_occupancy output_occupancy : aspis_core.field.QM31) (expected_output : aspis_core.field.M31) (opened : Array aspis_core.field.QM31 16#usize) :
    native_occupancy15 input_occupancy output_occupancy expected_output opened =
      reference_terminal.occupancy_lanes_literal input_occupancy output_occupancy expected_output opened := by
  unfold native_occupancy15 reference_terminal.occupancy_lanes_literal
  apply bind_equal9
  intro p0
  apply bind_equal9
  intro p1
  apply bind_equal9
  intro p2
  apply bind_equal9
  intro p3
  apply bind_equal9
  intro p4
  apply bind_equal9
  intro p5
  apply bind_equal9
  intro p6
  apply bind_equal9
  intro p7
  apply bind_equal9
  intro p8
  apply bind_equal9
  intro p9
  apply bind_equal9
  intro p10
  apply bind_equal9
  intro p11
  apply bind_equal9
  intro p12
  apply bind_equal9
  intro p13
  apply bind_equal9
  intro p14
  apply bind_equal9
  intro p15
  rw [range_as_fold13 _ 0#usize 8#usize 8 _ (by rfl),leading_indices15]
  exact (occupancy_fold15_0 _ _ _ _ _ _ _ _ _).symm
#print axioms native_occupancy_binding15
end PV_B3P_Native15227
