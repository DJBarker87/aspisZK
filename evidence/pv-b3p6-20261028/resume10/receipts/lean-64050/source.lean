import PV_B3P_ValueFrames10227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] value_owned_stage9_00 value_owned_stage9_01 value_owned_stage9_02 value_owned_stage9_03 value_owned_stage9_04 value_owned_stage9_05 value_owned_stage9_06 value_owned_stage9_07 value_owned_stage9_08 value_owned_stage9_09 value_owned_stage9_10 value_owned_stage9_11 value_owned_stage9_12 value_owned_stage9_13 value_owned_stage9_14 value_selector10 value_owned_cont10_01 value_owned_cont10_02 value_owned_cont10_03 value_owned_cont10_04 value_owned_cont10_05 value_owned_cont10_06 value_owned_cont10_07 value_owned_cont10_08 value_owned_cont10_09 value_owned_cont10_10 value_owned_cont10_11 value_owned_cont10_12 value_owned_cont10_13 value_owned_cont10_14

theorem value_sequence_cps10 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    value_owned_sequence9 packed openings selectors = value_owned_cps10 packed openings selectors := by
  unfold value_owned_sequence9 value_owned_cps10
  rw [value_selector_pair10]
  simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
  apply bind_equal9
  intro selector
  rw [value_selector_frame10_01 packed openings selectors selector (Array.repeat 33#usize aspis_core.field.QM31.ZERO)]
  conv_rhs => unfold value_owned_cont10_01
  apply bind_equal9
  intro s1
  rw [value_selector_frame10_02 packed openings selectors selector s1.2]
  conv_rhs => unfold value_owned_cont10_02
  apply bind_equal9
  intro s2
  rw [value_selector_frame10_03 packed openings selectors selector s2.2]
  conv_rhs => unfold value_owned_cont10_03
  apply bind_equal9
  intro s3
  rw [value_selector_frame10_04 packed openings selectors selector s3.2]
  conv_rhs => unfold value_owned_cont10_04
  apply bind_equal9
  intro s4
  rw [value_selector_frame10_05 packed openings selectors selector s4.2]
  conv_rhs => unfold value_owned_cont10_05
  apply bind_equal9
  intro s5
  rw [value_selector_frame10_06 packed openings selectors selector s5.2]
  conv_rhs => unfold value_owned_cont10_06
  apply bind_equal9
  intro s6
  rw [value_selector_frame10_07 packed openings selectors selector s6.2]
  conv_rhs => unfold value_owned_cont10_07
  apply bind_equal9
  intro s7
  rw [value_selector_frame10_08 packed openings selectors selector s7.2]
  conv_rhs => unfold value_owned_cont10_08
  apply bind_equal9
  intro s8
  rw [value_selector_frame10_09 packed openings selectors selector s8.2]
  conv_rhs => unfold value_owned_cont10_09
  apply bind_equal9
  intro s9
  rw [value_selector_frame10_10 packed openings selectors selector s9.2]
  conv_rhs => unfold value_owned_cont10_10
  apply bind_equal9
  intro s10
  rw [value_selector_frame10_11 packed openings selectors selector s10.2]
  conv_rhs => unfold value_owned_cont10_11
  apply bind_equal9
  intro s11
  rw [value_selector_frame10_12 packed openings selectors selector s11.2]
  conv_rhs => unfold value_owned_cont10_12
  apply bind_equal9
  intro s12
  rw [value_selector_frame10_13 packed openings selectors selector s12.2]
  conv_rhs => unfold value_owned_cont10_13
  apply bind_equal9
  intro s13
  unfold value_owned_cont10_14
  rfl

theorem value_entry_factor10 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.add_value_lanes packed openings selectors = value_owned_sequence9 packed openings selectors :=
  (value_entry_cps10 packed openings selectors).trans (value_sequence_cps10 packed openings selectors).symm

theorem add_value_read_binding10 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.add_value_lanes packed openings selectors = value_direct_sequence9 packed openings selectors :=
  (value_entry_factor10 packed openings selectors).trans (value_sequence_read_binding9 packed openings selectors)
#print axioms value_sequence_cps10
#print axioms value_entry_factor10
#print axioms add_value_read_binding10
end PV_B3P_Binding10227
