import PV_B3P_Operations12227
import PV_B3P_RangeFold13227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

abbrev OccupancyState15 := Array aspis_core.field.QM31 12#usize
def occupancy_step15 (opened : Array aspis_core.field.QM31 16#usize)
    (one_minus both : aspis_core.field.QM31) (state : OccupancyState15) (lane : Usize) : Result OccupancyState15 := do
  let source ← lift (Usize.wrapping_add 2#usize lane)
  let q ← Array.index_usize opened source
  let q1 ← aspis_core.field.QM31.mul one_minus q
  let q2 ← aspis_core.field.QM31.mul both q1
  let target ← lift (Usize.wrapping_add 3#usize lane)
  Array.update state target q2

def occupancy_finish15 (input_occupancy output_occupancy : aspis_core.field.QM31) (expected_output : aspis_core.field.M31) (opened : Array aspis_core.field.QM31 16#usize) (occupied inverse one_minus both : aspis_core.field.QM31) (state : OccupancyState15) : Result OccupancyState15 := do
  let q33 ← Array.index_usize opened 10#usize
  let q34 ← aspis_core.field.QM31.mul q33 one_minus
  let q35 ← aspis_core.field.QM31.mul input_occupancy q34
  let q36 ← reference_terminal.lift_m31 expected_output
  let q37 ← aspis_core.field.QM31.sub occupied q36
  let q38 ← aspis_core.field.QM31.mul output_occupancy q37
  let q39 ← aspis_core.field.QM31.add q35 q38
  Array.update state 11#usize q39
end PV_B3P_Native15227
