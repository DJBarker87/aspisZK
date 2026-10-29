import PV_B3P_DigestReadSuffix900227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Success227
set_option autoImplicit false
attribute [local irreducible] reference_terminal.add_digest_binding reference_copy_terminal.Selectors.row reference_terminal.empty_root reference_terminal.digest227 reference_terminal.bounded_append_carry

theorem digest_source_factor9 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.public_digest_lanes public1 openings selectors =
      digest_suffix_00 public1 openings selectors := by
  unfold reference_terminal.public_digest_lanes
  conv_rhs => rw [digest_suffix_00_equation]; simp only [digest_stage_00,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_0_0
  apply bind_equal9
  intro head_0_1
  apply bind_equal9
  intro head_0_2
  apply bind_equal9
  intro head_0_3
  conv_rhs => rw [digest_suffix_01_equation]; simp only [digest_stage_01,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_1_0
  apply bind_equal9
  intro head_1_1
  apply bind_equal9
  intro head_1_2
  apply bind_equal9
  intro head_1_3
  conv_rhs => rw [digest_suffix_02_equation]; simp only [digest_stage_02,digest_assoc,digest_if_bind,digest_option_bind]
  apply recipient_equal9
  intro recipient_output
  conv_rhs => rw [digest_suffix_03_equation]; simp only [digest_stage_03,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_3_0
  apply bind_equal9
  intro head_3_1
  apply bind_equal9
  intro head_3_2
  apply bind_equal9
  intro head_3_3
  conv_rhs => rw [digest_suffix_04_equation]; simp only [digest_stage_04,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_4_0
  apply bind_equal9
  intro head_4_1
  apply bind_equal9
  intro head_4_2
  apply frontier_equal9
  intro frontier_output_4
  conv_rhs => rw [digest_suffix_05_equation]; simp only [digest_stage_05,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_5_0
  apply bind_equal9
  intro head_5_1
  apply bind_equal9
  intro head_5_2
  apply frontier_equal9
  intro frontier_output_5
  conv_rhs => rw [digest_suffix_06_equation]; simp only [digest_stage_06,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_6_0
  apply bind_equal9
  intro head_6_1
  apply bind_equal9
  intro head_6_2
  apply frontier_equal9
  intro frontier_output_6
  conv_rhs => rw [digest_suffix_07_equation]; simp only [digest_stage_07,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_7_0
  apply bind_equal9
  intro head_7_1
  apply bind_equal9
  intro head_7_2
  apply frontier_equal9
  intro frontier_output_7
  conv_rhs => rw [digest_suffix_08_equation]; simp only [digest_stage_08,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_8_0
  apply bind_equal9
  intro head_8_1
  apply bind_equal9
  intro head_8_2
  apply frontier_equal9
  intro frontier_output_8
  conv_rhs => rw [digest_suffix_09_equation]; simp only [digest_stage_09,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_9_0
  apply bind_equal9
  intro head_9_1
  apply bind_equal9
  intro head_9_2
  apply frontier_equal9
  intro frontier_output_9
  conv_rhs => rw [digest_suffix_10_equation]; simp only [digest_stage_10,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_10_0
  apply bind_equal9
  intro head_10_1
  apply bind_equal9
  intro head_10_2
  apply frontier_equal9
  intro frontier_output_10
  conv_rhs => rw [digest_suffix_11_equation]; simp only [digest_stage_11,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_11_0
  apply bind_equal9
  intro head_11_1
  apply bind_equal9
  intro head_11_2
  apply frontier_equal9
  intro frontier_output_11
  conv_rhs => rw [digest_suffix_12_equation]; simp only [digest_stage_12,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_12_0
  apply bind_equal9
  intro head_12_1
  apply bind_equal9
  intro head_12_2
  apply frontier_equal9
  intro frontier_output_12
  conv_rhs => rw [digest_suffix_13_equation]; simp only [digest_stage_13,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_13_0
  apply bind_equal9
  intro head_13_1
  apply bind_equal9
  intro head_13_2
  apply frontier_equal9
  intro frontier_output_13
  conv_rhs => rw [digest_suffix_14_equation]; simp only [digest_stage_14,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_14_0
  apply bind_equal9
  intro head_14_1
  apply bind_equal9
  intro head_14_2
  apply frontier_equal9
  intro frontier_output_14
  conv_rhs => rw [digest_suffix_15_equation]; simp only [digest_stage_15,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_15_0
  apply bind_equal9
  intro head_15_1
  apply bind_equal9
  intro head_15_2
  apply frontier_equal9
  intro frontier_output_15
  conv_rhs => rw [digest_suffix_16_equation]; simp only [digest_stage_16,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_16_0
  apply bind_equal9
  intro head_16_1
  apply bind_equal9
  intro head_16_2
  apply frontier_equal9
  intro frontier_output_16
  conv_rhs => rw [digest_suffix_17_equation]; simp only [digest_stage_17,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_17_0
  apply bind_equal9
  intro head_17_1
  apply bind_equal9
  intro head_17_2
  apply frontier_equal9
  intro frontier_output_17
  conv_rhs => rw [digest_suffix_18_equation]; simp only [digest_stage_18,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_18_0
  apply bind_equal9
  intro head_18_1
  apply bind_equal9
  intro head_18_2
  apply frontier_equal9
  intro frontier_output_18
  conv_rhs => rw [digest_suffix_19_equation]; simp only [digest_stage_19,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_19_0
  apply bind_equal9
  intro head_19_1
  apply bind_equal9
  intro head_19_2
  apply frontier_equal9
  intro frontier_output_19
  conv_rhs => rw [digest_suffix_20_equation]; simp only [digest_stage_20,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_20_0
  apply bind_equal9
  intro head_20_1
  apply bind_equal9
  intro head_20_2
  apply frontier_equal9
  intro frontier_output_20
  conv_rhs => rw [digest_suffix_21_equation]; simp only [digest_stage_21,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_21_0
  apply bind_equal9
  intro head_21_1
  apply bind_equal9
  intro head_21_2
  apply frontier_equal9
  intro frontier_output_21
  conv_rhs => rw [digest_suffix_22_equation]; simp only [digest_stage_22,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_22_0
  apply bind_equal9
  intro head_22_1
  apply bind_equal9
  intro head_22_2
  apply frontier_equal9
  intro frontier_output_22
  conv_rhs => rw [digest_suffix_23_equation]; simp only [digest_stage_23,digest_assoc,digest_if_bind,digest_option_bind]
  apply bind_equal9
  intro head_23_0
  apply bind_equal9
  intro head_23_1
  apply bind_equal9
  intro head_23_2
  apply frontier_equal9
  intro frontier_output_23
  rfl

#print axioms digest_source_factor9

theorem public_digest_read_binding9 (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.public_digest_lanes public1 openings selectors =
      digest_direct_suffix9_00 public1 openings selectors :=
  (digest_source_factor9 public1 openings selectors).trans
    (digest_suffix_read_binding9_00 public1 openings selectors)
#print axioms public_digest_read_binding9
end PV_B3P_Binding9227
