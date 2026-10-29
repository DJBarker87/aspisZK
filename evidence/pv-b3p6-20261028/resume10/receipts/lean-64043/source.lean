import PV_B3P_ValueCps1000227
import PV_B3P_ValueCps1001227
import PV_B3P_ValueCps1002227
import PV_B3P_ValueCps1003227
import PV_B3P_ValueCps1004227
import PV_B3P_ValueCps1005227
import PV_B3P_ValueCps1006227
import PV_B3P_ValueCps1007227
import PV_B3P_ValueCps1008227
import PV_B3P_ValueCps1009227
import PV_B3P_ValueCps1010227
import PV_B3P_ValueCps1011227
import PV_B3P_ValueCps1012227
import PV_B3P_ValueCps1013227
import PV_B3P_ValueReadSequence9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

def value_owned_cps10 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result (Array aspis_core.field.QM31 24#usize) := do
  let selector ← value_selector10 packed openings selectors
  let s1 ← value_owned_stage9_01 packed openings selectors (selector,Array.repeat 33#usize aspis_core.field.QM31.ZERO)
  let s2 ← value_owned_stage9_02 packed openings selectors (selector,s1.2)
  let s3 ← value_owned_stage9_03 packed openings selectors (selector,s2.2)
  let s4 ← value_owned_stage9_04 packed openings selectors (selector,s3.2)
  let s5 ← value_owned_stage9_05 packed openings selectors (selector,s4.2)
  let s6 ← value_owned_stage9_06 packed openings selectors (selector,s5.2)
  let s7 ← value_owned_stage9_07 packed openings selectors (selector,s6.2)
  let s8 ← value_owned_stage9_08 packed openings selectors (selector,s7.2)
  let s9 ← value_owned_stage9_09 packed openings selectors (selector,s8.2)
  let s10 ← value_owned_stage9_10 packed openings selectors (selector,s9.2)
  let s11 ← value_owned_stage9_11 packed openings selectors (selector,s10.2)
  let s12 ← value_owned_stage9_12 packed openings selectors (selector,s11.2)
  let s13 ← value_owned_stage9_13 packed openings selectors (selector,s12.2)
  value_owned_stage9_14 packed openings selectors (selector,s13.2)

def value_direct_cps10 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result (Array aspis_core.field.QM31 24#usize) := do
  let selector ← value_selector10 packed openings selectors
  let s1 ← value_direct_stage9_01 packed openings selectors (selector,Array.repeat 33#usize aspis_core.field.QM31.ZERO)
  let s2 ← value_direct_stage9_02 packed openings selectors (selector,s1.2)
  let s3 ← value_direct_stage9_03 packed openings selectors (selector,s2.2)
  let s4 ← value_direct_stage9_04 packed openings selectors (selector,s3.2)
  let s5 ← value_direct_stage9_05 packed openings selectors (selector,s4.2)
  let s6 ← value_direct_stage9_06 packed openings selectors (selector,s5.2)
  let s7 ← value_direct_stage9_07 packed openings selectors (selector,s6.2)
  let s8 ← value_direct_stage9_08 packed openings selectors (selector,s7.2)
  let s9 ← value_direct_stage9_09 packed openings selectors (selector,s8.2)
  let s10 ← value_direct_stage9_10 packed openings selectors (selector,s9.2)
  let s11 ← value_direct_stage9_11 packed openings selectors (selector,s10.2)
  let s12 ← value_direct_stage9_12 packed openings selectors (selector,s11.2)
  let s13 ← value_direct_stage9_13 packed openings selectors (selector,s12.2)
  value_direct_stage9_14 packed openings selectors (selector,s13.2)

theorem value_entry_cps10 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.add_value_lanes packed openings selectors = value_owned_cps10 packed openings selectors := by
  unfold value_owned_cps10
  conv_rhs => rw [←value_head_cps10_00 packed openings selectors]
  apply bind_equal9
  intro head_0_0
  apply bind_equal9
  intro head_0_1
  apply bind_equal9
  intro head_0_2
  apply bind_equal9
  intro head_0_3
  apply bind_equal9
  intro head_0_4
  apply bind_equal9
  intro head_0_5
  apply bind_equal9
  intro head_0_6
  apply bind_equal9
  intro head_0_7
  apply bind_equal9
  intro head_0_8
  apply bind_equal9
  intro head_0_9
  apply bind_equal9
  intro head_0_10
  apply bind_equal9
  intro head_0_11
  apply bind_equal9
  intro head_0_12
  apply bind_equal9
  intro head_0_13
  conv_rhs => rw [←value_head_cps10_01 packed openings selectors]
  apply bind_equal9
  intro head_1_0
  apply bind_equal9
  intro head_1_1
  apply bind_equal9
  intro head_1_2
  apply bind_equal9
  intro head_1_3
  apply bind_equal9
  intro head_1_4
  apply bind_equal9
  intro head_1_5
  apply bind_equal9
  intro head_1_6
  apply bind_equal9
  intro head_1_7
  apply bind_equal9
  intro head_1_8
  apply bind_equal9
  intro head_1_9
  apply bind_equal9
  intro head_1_10
  apply bind_equal9
  intro head_1_11
  apply bind_equal9
  intro head_1_12
  apply bind_equal9
  intro head_1_13
  apply bind_equal9
  intro head_1_14
  apply bind_equal9
  intro head_1_15
  apply bind_equal9
  intro head_1_16
  apply bind_equal9
  intro head_1_17
  apply bind_equal9
  intro head_1_18
  apply bind_equal9
  intro head_1_19
  conv_rhs => rw [←value_head_cps10_02 packed openings selectors]
  apply bind_equal9
  intro head_2_0
  apply bind_equal9
  intro head_2_1
  apply bind_equal9
  intro head_2_2
  apply bind_equal9
  intro head_2_3
  apply bind_equal9
  intro head_2_4
  apply bind_equal9
  intro head_2_5
  apply bind_equal9
  intro head_2_6
  apply bind_equal9
  intro head_2_7
  apply bind_equal9
  intro head_2_8
  apply bind_equal9
  intro head_2_9
  apply bind_equal9
  intro head_2_10
  apply bind_equal9
  intro head_2_11
  apply bind_equal9
  intro head_2_12
  apply bind_equal9
  intro head_2_13
  apply bind_equal9
  intro head_2_14
  apply bind_equal9
  intro head_2_15
  apply bind_equal9
  intro head_2_16
  apply bind_equal9
  intro head_2_17
  apply bind_equal9
  intro head_2_18
  apply bind_equal9
  intro head_2_19
  conv_rhs => rw [←value_head_cps10_03 packed openings selectors]
  apply bind_equal9
  intro head_3_0
  apply bind_equal9
  intro head_3_1
  apply bind_equal9
  intro head_3_2
  apply bind_equal9
  intro head_3_3
  apply bind_equal9
  intro head_3_4
  apply bind_equal9
  intro head_3_5
  apply bind_equal9
  intro head_3_6
  apply bind_equal9
  intro head_3_7
  apply bind_equal9
  intro head_3_8
  apply bind_equal9
  intro head_3_9
  apply bind_equal9
  intro head_3_10
  apply bind_equal9
  intro head_3_11
  apply bind_equal9
  intro head_3_12
  apply bind_equal9
  intro head_3_13
  apply bind_equal9
  intro head_3_14
  apply bind_equal9
  intro head_3_15
  apply bind_equal9
  intro head_3_16
  apply bind_equal9
  intro head_3_17
  apply bind_equal9
  intro head_3_18
  apply bind_equal9
  intro head_3_19
  apply bind_equal9
  intro head_3_20
  apply bind_equal9
  intro head_3_21
  apply bind_equal9
  intro head_3_22
  apply bind_equal9
  intro head_3_23
  apply bind_equal9
  intro head_3_24
  conv_rhs => rw [←value_head_cps10_04 packed openings selectors]
  apply bind_equal9
  intro head_4_0
  apply bind_equal9
  intro head_4_1
  apply bind_equal9
  intro head_4_2
  apply bind_equal9
  intro head_4_3
  apply bind_equal9
  intro head_4_4
  apply bind_equal9
  intro head_4_5
  apply bind_equal9
  intro head_4_6
  apply bind_equal9
  intro head_4_7
  apply bind_equal9
  intro head_4_8
  apply bind_equal9
  intro head_4_9
  apply bind_equal9
  intro head_4_10
  apply bind_equal9
  intro head_4_11
  apply bind_equal9
  intro head_4_12
  apply bind_equal9
  intro head_4_13
  apply bind_equal9
  intro head_4_14
  apply bind_equal9
  intro head_4_15
  apply bind_equal9
  intro head_4_16
  apply bind_equal9
  intro head_4_17
  apply bind_equal9
  intro head_4_18
  apply bind_equal9
  intro head_4_19
  apply bind_equal9
  intro head_4_20
  apply bind_equal9
  intro head_4_21
  apply bind_equal9
  intro head_4_22
  apply bind_equal9
  intro head_4_23
  apply bind_equal9
  intro head_4_24
  conv_rhs => rw [←value_head_cps10_05 packed openings selectors]
  apply bind_equal9
  intro head_5_0
  apply bind_equal9
  intro head_5_1
  apply bind_equal9
  intro head_5_2
  apply bind_equal9
  intro head_5_3
  apply bind_equal9
  intro head_5_4
  apply bind_equal9
  intro head_5_5
  apply bind_equal9
  intro head_5_6
  apply bind_equal9
  intro head_5_7
  apply bind_equal9
  intro head_5_8
  apply bind_equal9
  intro head_5_9
  apply bind_equal9
  intro head_5_10
  apply bind_equal9
  intro head_5_11
  apply bind_equal9
  intro head_5_12
  apply bind_equal9
  intro head_5_13
  apply bind_equal9
  intro head_5_14
  apply bind_equal9
  intro head_5_15
  apply bind_equal9
  intro head_5_16
  apply bind_equal9
  intro head_5_17
  apply bind_equal9
  intro head_5_18
  apply bind_equal9
  intro head_5_19
  apply bind_equal9
  intro head_5_20
  apply bind_equal9
  intro head_5_21
  apply bind_equal9
  intro head_5_22
  apply bind_equal9
  intro head_5_23
  apply bind_equal9
  intro head_5_24
  conv_rhs => rw [←value_head_cps10_06 packed openings selectors]
  apply bind_equal9
  intro head_6_0
  apply bind_equal9
  intro head_6_1
  apply bind_equal9
  intro head_6_2
  apply bind_equal9
  intro head_6_3
  apply bind_equal9
  intro head_6_4
  apply bind_equal9
  intro head_6_5
  apply bind_equal9
  intro head_6_6
  apply bind_equal9
  intro head_6_7
  apply bind_equal9
  intro head_6_8
  apply bind_equal9
  intro head_6_9
  apply bind_equal9
  intro head_6_10
  apply bind_equal9
  intro head_6_11
  apply bind_equal9
  intro head_6_12
  apply bind_equal9
  intro head_6_13
  apply bind_equal9
  intro head_6_14
  apply bind_equal9
  intro head_6_15
  apply bind_equal9
  intro head_6_16
  apply bind_equal9
  intro head_6_17
  apply bind_equal9
  intro head_6_18
  apply bind_equal9
  intro head_6_19
  apply bind_equal9
  intro head_6_20
  apply bind_equal9
  intro head_6_21
  apply bind_equal9
  intro head_6_22
  apply bind_equal9
  intro head_6_23
  apply bind_equal9
  intro head_6_24
  conv_rhs => rw [←value_head_cps10_07 packed openings selectors]
  apply bind_equal9
  intro head_7_0
  apply bind_equal9
  intro head_7_1
  apply bind_equal9
  intro head_7_2
  apply bind_equal9
  intro head_7_3
  apply bind_equal9
  intro head_7_4
  apply bind_equal9
  intro head_7_5
  apply bind_equal9
  intro head_7_6
  apply bind_equal9
  intro head_7_7
  apply bind_equal9
  intro head_7_8
  apply bind_equal9
  intro head_7_9
  apply bind_equal9
  intro head_7_10
  apply bind_equal9
  intro head_7_11
  apply bind_equal9
  intro head_7_12
  apply bind_equal9
  intro head_7_13
  apply bind_equal9
  intro head_7_14
  apply bind_equal9
  intro head_7_15
  conv_rhs => rw [←value_head_cps10_08 packed openings selectors]
  apply bind_equal9
  intro head_8_0
  apply bind_equal9
  intro head_8_1
  apply bind_equal9
  intro head_8_2
  apply bind_equal9
  intro head_8_3
  apply bind_equal9
  intro head_8_4
  apply bind_equal9
  intro head_8_5
  apply bind_equal9
  intro head_8_6
  apply bind_equal9
  intro head_8_7
  apply bind_equal9
  intro head_8_8
  apply bind_equal9
  intro head_8_9
  apply bind_equal9
  intro head_8_10
  apply bind_equal9
  intro head_8_11
  apply bind_equal9
  intro head_8_12
  apply bind_equal9
  intro head_8_13
  apply bind_equal9
  intro head_8_14
  apply bind_equal9
  intro head_8_15
  apply bind_equal9
  intro head_8_16
  apply bind_equal9
  intro head_8_17
  conv_rhs => rw [←value_head_cps10_09 packed openings selectors]
  apply bind_equal9
  intro head_9_0
  apply bind_equal9
  intro head_9_1
  apply bind_equal9
  intro head_9_2
  apply bind_equal9
  intro head_9_3
  apply bind_equal9
  intro head_9_4
  apply bind_equal9
  intro head_9_5
  apply bind_equal9
  intro head_9_6
  apply bind_equal9
  intro head_9_7
  apply bind_equal9
  intro head_9_8
  apply bind_equal9
  intro head_9_9
  apply bind_equal9
  intro head_9_10
  apply bind_equal9
  intro head_9_11
  apply bind_equal9
  intro head_9_12
  apply bind_equal9
  intro head_9_13
  apply bind_equal9
  intro head_9_14
  apply bind_equal9
  intro head_9_15
  apply bind_equal9
  intro head_9_16
  apply bind_equal9
  intro head_9_17
  conv_rhs => rw [←value_head_cps10_10 packed openings selectors]
  apply bind_equal9
  intro head_10_0
  apply bind_equal9
  intro head_10_1
  apply bind_equal9
  intro head_10_2
  apply bind_equal9
  intro head_10_3
  apply bind_equal9
  intro head_10_4
  apply bind_equal9
  intro head_10_5
  apply bind_equal9
  intro head_10_6
  apply bind_equal9
  intro head_10_7
  apply bind_equal9
  intro head_10_8
  apply bind_equal9
  intro head_10_9
  apply bind_equal9
  intro head_10_10
  apply bind_equal9
  intro head_10_11
  apply bind_equal9
  intro head_10_12
  apply bind_equal9
  intro head_10_13
  apply bind_equal9
  intro head_10_14
  apply bind_equal9
  intro head_10_15
  apply bind_equal9
  intro head_10_16
  apply bind_equal9
  intro head_10_17
  conv_rhs => rw [←value_head_cps10_11 packed openings selectors]
  apply bind_equal9
  intro head_11_0
  apply bind_equal9
  intro head_11_1
  apply bind_equal9
  intro head_11_2
  apply bind_equal9
  intro head_11_3
  apply bind_equal9
  intro head_11_4
  apply bind_equal9
  intro head_11_5
  apply bind_equal9
  intro head_11_6
  apply bind_equal9
  intro head_11_7
  apply bind_equal9
  intro head_11_8
  apply bind_equal9
  intro head_11_9
  apply bind_equal9
  intro head_11_10
  apply bind_equal9
  intro head_11_11
  apply bind_equal9
  intro head_11_12
  apply bind_equal9
  intro head_11_13
  apply bind_equal9
  intro head_11_14
  apply bind_equal9
  intro head_11_15
  apply bind_equal9
  intro head_11_16
  apply bind_equal9
  intro head_11_17
  conv_rhs => rw [←value_head_cps10_12 packed openings selectors]
  apply bind_equal9
  intro head_12_0
  apply bind_equal9
  intro head_12_1
  apply bind_equal9
  intro head_12_2
  apply bind_equal9
  intro head_12_3
  apply bind_equal9
  intro head_12_4
  apply bind_equal9
  intro head_12_5
  apply bind_equal9
  intro head_12_6
  apply bind_equal9
  intro head_12_7
  apply bind_equal9
  intro head_12_8
  apply bind_equal9
  intro head_12_9
  apply bind_equal9
  intro head_12_10
  apply bind_equal9
  intro head_12_11
  apply bind_equal9
  intro head_12_12
  apply bind_equal9
  intro head_12_13
  apply bind_equal9
  intro head_12_14
  apply bind_equal9
  intro head_12_15
  apply bind_equal9
  intro head_12_16
  apply bind_equal9
  intro head_12_17
  conv_rhs => rw [←value_head_cps10_13 packed openings selectors]
  apply bind_equal9
  intro head_13_0
  apply bind_equal9
  intro head_13_1
  apply bind_equal9
  intro head_13_2
  apply bind_equal9
  intro head_13_3
  apply bind_equal9
  intro head_13_4
  apply bind_equal9
  intro head_13_5
  apply bind_equal9
  intro head_13_6
  apply bind_equal9
  intro head_13_7
  apply bind_equal9
  intro head_13_8
  conv_rhs => unfold value_owned_stage9_14 value_read_context9_14
  rfl

attribute [local irreducible] value_owned_stage9_00 value_owned_stage9_01 value_owned_stage9_02 value_owned_stage9_03 value_owned_stage9_04 value_owned_stage9_05 value_owned_stage9_06 value_owned_stage9_07 value_owned_stage9_08 value_owned_stage9_09 value_owned_stage9_10 value_owned_stage9_11 value_owned_stage9_12 value_owned_stage9_13 value_owned_stage9_14 value_direct_stage9_00 value_direct_stage9_01 value_direct_stage9_02 value_direct_stage9_03 value_direct_stage9_04 value_direct_stage9_05 value_direct_stage9_06 value_direct_stage9_07 value_direct_stage9_08 value_direct_stage9_09 value_direct_stage9_10 value_direct_stage9_11 value_direct_stage9_12 value_direct_stage9_13 value_direct_stage9_14 value_selector10

theorem value_cps_read10 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    value_owned_cps10 packed openings selectors = value_direct_cps10 packed openings selectors := by
  unfold value_owned_cps10 value_direct_cps10
  simp only [value_stage_read_binding9_01, value_stage_read_binding9_02, value_stage_read_binding9_03, value_stage_read_binding9_04, value_stage_read_binding9_05, value_stage_read_binding9_06, value_stage_read_binding9_07, value_stage_read_binding9_08, value_stage_read_binding9_09, value_stage_read_binding9_10, value_stage_read_binding9_11, value_stage_read_binding9_12, value_stage_read_binding9_13, value_stage_read_binding9_14]

theorem add_value_cps_read_binding10 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.add_value_lanes packed openings selectors = value_direct_cps10 packed openings selectors :=
  (value_entry_cps10 packed openings selectors).trans (value_cps_read10 packed openings selectors)
#print axioms value_entry_cps10
#print axioms value_cps_read10
#print axioms add_value_cps_read_binding10
end PV_B3P_Binding10227
