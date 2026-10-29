import PV_B3P_ValueTail1001227
import PV_B3P_ValueRead900227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result ControlFlow Error
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row value_source_tail10_01

theorem value_source_equation10_00 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.add_value_lanes packed openings selectors =
      value_owned_stage9_00 packed openings selectors >>= (fun next => value_source_tail10_01 packed openings selectors next.1 next.2) := by
  unfold reference_terminal.add_value_lanes value_owned_stage9_00 value_read_context9_00
  conv_rhs => simp only [bind_assoc, bind_tc_ok]
  apply bind_equal9
  intro head_0
  apply bind_equal9
  intro head_1
  apply bind_equal9
  intro head_2
  apply bind_equal9
  intro head_3
  apply bind_equal9
  intro head_4
  apply bind_equal9
  intro head_5
  apply bind_equal9
  intro head_6
  apply bind_equal9
  intro head_7
  apply bind_equal9
  intro head_8
  apply bind_equal9
  intro head_9
  apply bind_equal9
  intro head_10
  apply bind_equal9
  intro head_11
  apply bind_equal9
  intro head_12
  apply bind_equal9
  intro head_13
  unfold value_source_tail10_01
  rfl

#print axioms value_source_equation10_00
end PV_B3P_Binding10227
