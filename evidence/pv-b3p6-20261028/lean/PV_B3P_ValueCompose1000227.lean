import PV_B3P_ValueEntry10227
import PV_B3P_ValueCompose1001227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

def value_owned_tail10_00 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result (Array aspis_core.field.QM31 24#usize) :=
  value_owned_stage9_00 packed openings selectors >>= value_owned_tail10_01 packed openings selectors

def value_direct_tail10_00 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result (Array aspis_core.field.QM31 24#usize) :=
  value_direct_stage9_00 packed openings selectors >>= value_direct_tail10_01 packed openings selectors

attribute [local irreducible] value_owned_stage9_00 value_owned_stage9_01 value_owned_stage9_02 value_owned_stage9_03 value_owned_stage9_04 value_owned_stage9_05 value_owned_stage9_06 value_owned_stage9_07 value_owned_stage9_08 value_owned_stage9_09 value_owned_stage9_10 value_owned_stage9_11 value_owned_stage9_12 value_owned_stage9_13 value_owned_stage9_14 value_direct_stage9_00 value_direct_stage9_01 value_direct_stage9_02 value_direct_stage9_03 value_direct_stage9_04 value_direct_stage9_05 value_direct_stage9_06 value_direct_stage9_07 value_direct_stage9_08 value_direct_stage9_09 value_direct_stage9_10 value_direct_stage9_11 value_direct_stage9_12 value_direct_stage9_13 value_direct_stage9_14

theorem value_tail_factor10_00 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.add_value_lanes packed openings selectors = value_owned_tail10_00 packed openings selectors := by
  rw [value_source_equation10_00]
  change (value_owned_stage9_00 packed openings selectors >>= (fun next => value_source_tail10_01 packed openings selectors next.1 next.2)) = _
  apply congrArg (fun next => value_owned_stage9_00 packed openings selectors >>= next)
  funext next
  exact value_tail_factor10_01 packed openings selectors next

theorem value_tail_read_binding10_00 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    value_owned_tail10_00 packed openings selectors = value_direct_tail10_00 packed openings selectors := by
  unfold value_owned_tail10_00 value_direct_tail10_00
  rw [value_stage_read_binding9_00]
  apply congrArg (fun next => value_direct_stage9_00 packed openings selectors >>= next)
  funext next
  exact value_tail_read_binding10_01 packed openings selectors next

#print axioms value_tail_factor10_00
#print axioms value_tail_read_binding10_00
end PV_B3P_Binding10227
