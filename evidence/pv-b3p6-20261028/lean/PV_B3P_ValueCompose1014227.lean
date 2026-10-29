import PV_B3P_ValueTail1014227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

def value_owned_tail10_14 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result (Array aspis_core.field.QM31 24#usize) :=
  value_owned_stage9_14 packed openings selectors state

def value_direct_tail10_14 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result (Array aspis_core.field.QM31 24#usize) :=
  value_direct_stage9_14 packed openings selectors state

attribute [local irreducible] value_owned_stage9_14 value_direct_stage9_14

theorem value_tail_factor10_14 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_source_tail10_14 packed openings selectors state.1 state.2 = value_owned_tail10_14 packed openings selectors state := by
  rw [value_source_equation10_14]
  rfl

theorem value_tail_read_binding10_14 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_owned_tail10_14 packed openings selectors state = value_direct_tail10_14 packed openings selectors state := by
  unfold value_owned_tail10_14 value_direct_tail10_14
  rw [value_stage_read_binding9_14]

#print axioms value_tail_factor10_14
#print axioms value_tail_read_binding10_14
end PV_B3P_Binding10227
