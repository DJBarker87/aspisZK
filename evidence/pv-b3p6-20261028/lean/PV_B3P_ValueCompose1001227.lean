import PV_B3P_ValueTail1001227
import PV_B3P_ValueCompose1002227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

def value_owned_tail10_01 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result (Array aspis_core.field.QM31 24#usize) :=
  value_owned_stage9_01 packed openings selectors state >>= value_owned_tail10_02 packed openings selectors

def value_direct_tail10_01 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result (Array aspis_core.field.QM31 24#usize) :=
  value_direct_stage9_01 packed openings selectors state >>= value_direct_tail10_02 packed openings selectors

attribute [local irreducible] value_owned_stage9_01 value_owned_stage9_02 value_owned_stage9_03 value_owned_stage9_04 value_owned_stage9_05 value_owned_stage9_06 value_owned_stage9_07 value_owned_stage9_08 value_owned_stage9_09 value_owned_stage9_10 value_owned_stage9_11 value_owned_stage9_12 value_owned_stage9_13 value_owned_stage9_14 value_direct_stage9_01 value_direct_stage9_02 value_direct_stage9_03 value_direct_stage9_04 value_direct_stage9_05 value_direct_stage9_06 value_direct_stage9_07 value_direct_stage9_08 value_direct_stage9_09 value_direct_stage9_10 value_direct_stage9_11 value_direct_stage9_12 value_direct_stage9_13 value_direct_stage9_14

theorem value_tail_factor10_01 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_source_tail10_01 packed openings selectors state.1 state.2 = value_owned_tail10_01 packed openings selectors state := by
  rw [value_source_equation10_01]
  change (value_owned_stage9_01 packed openings selectors state >>= (fun next => value_source_tail10_02 packed openings selectors next.1 next.2)) = _
  apply congrArg (fun next => value_owned_stage9_01 packed openings selectors state >>= next)
  funext next
  exact value_tail_factor10_02 packed openings selectors next

theorem value_tail_read_binding10_01 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_owned_tail10_01 packed openings selectors state = value_direct_tail10_01 packed openings selectors state := by
  unfold value_owned_tail10_01 value_direct_tail10_01
  rw [value_stage_read_binding9_01]
  apply congrArg (fun next => value_direct_stage9_01 packed openings selectors state >>= next)
  funext next
  exact value_tail_read_binding10_02 packed openings selectors next

#print axioms value_tail_factor10_01
#print axioms value_tail_read_binding10_01
end PV_B3P_Binding10227
