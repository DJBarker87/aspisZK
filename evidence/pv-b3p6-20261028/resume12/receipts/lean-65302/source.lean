import PV_B3P_SumOperation11227
import PV_B3P_P227_10
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
open Result
def sum_context11_add_path_lanes (sum_operation : SumOperation11)
  (packed : Array aspis_core.field.QM31 24#usize)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors) :
  Result (Array aspis_core.field.QM31 24#usize)
  := do
  let q ←
    sum_operation selectors.high
      aspis_core.field.QM31.ZERO 57#usize 63#usize
  let q1 ← Array.index_usize selectors.low 1#usize
  let q2 ← Array.index_usize selectors.low 5#usize
  let q3 ← aspis_core.field.QM31.add q1 q2
  let q4 ← Array.index_usize selectors.low 9#usize
  let q5 ← aspis_core.field.QM31.add q3 q4
  let q6 ← Array.index_usize selectors.low 13#usize
  let q7 ← aspis_core.field.QM31.add q5 q6
  let path_selector ← aspis_core.field.QM31.mul q q7
  let path ← reference_terminal.path_lanes_literal path_selector openings
  reference_terminal.add_preweighted packed 32#usize path
attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.mul Array.index_usize Array.update
theorem add_path_lanes_sum_caller11
  (packed : Array aspis_core.field.QM31 24#usize)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.add_path_lanes packed openings selectors = sum_context11_add_path_lanes source_sum_interval11 packed openings selectors := by
  have h := congrArg (fun operation => sum_context11_add_path_lanes operation packed openings selectors) sum_operation_binding11
  exact h
#print axioms add_path_lanes_sum_caller11
end PV_B3P_Binding11227
