import PV_B3P_ValueCompose1000227
import PV_B3P_ValueReadSequence9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] value_owned_stage9_00 value_owned_stage9_01 value_owned_stage9_02 value_owned_stage9_03 value_owned_stage9_04 value_owned_stage9_05 value_owned_stage9_06 value_owned_stage9_07 value_owned_stage9_08 value_owned_stage9_09 value_owned_stage9_10 value_owned_stage9_11 value_owned_stage9_12 value_owned_stage9_13 value_owned_stage9_14 value_direct_stage9_00 value_direct_stage9_01 value_direct_stage9_02 value_direct_stage9_03 value_direct_stage9_04 value_direct_stage9_05 value_direct_stage9_06 value_direct_stage9_07 value_direct_stage9_08 value_direct_stage9_09 value_direct_stage9_10 value_direct_stage9_11 value_direct_stage9_12 value_direct_stage9_13 value_direct_stage9_14

theorem value_entry_factor10 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.add_value_lanes packed openings selectors =
      value_owned_sequence9 packed openings selectors := by
  rw [value_tail_factor10_00]
  simp only [value_owned_sequence9, value_owned_tail10_00, value_owned_tail10_01, value_owned_tail10_02, value_owned_tail10_03, value_owned_tail10_04, value_owned_tail10_05, value_owned_tail10_06, value_owned_tail10_07, value_owned_tail10_08, value_owned_tail10_09, value_owned_tail10_10, value_owned_tail10_11, value_owned_tail10_12, value_owned_tail10_13, value_owned_tail10_14]

theorem add_value_read_binding10 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.add_value_lanes packed openings selectors =
      value_direct_sequence9 packed openings selectors :=
  (value_entry_factor10 packed openings selectors).trans
    (value_sequence_read_binding9 packed openings selectors)
#print axioms value_entry_factor10
#print axioms add_value_read_binding10
end PV_B3P_Binding10227
