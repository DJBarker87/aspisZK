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
  unfold reference_terminal.add_value_lanes value_owned_cps10
  rw [value_head_cps10_00]
  apply bind_equal9
  intro selector
  rw [value_head_cps10_01]
  apply bind_equal9
  intro s1
  rw [value_head_cps10_02]
  apply bind_equal9
  intro s2
  rw [value_head_cps10_03]
  apply bind_equal9
  intro s3
  rw [value_head_cps10_04]
  apply bind_equal9
  intro s4
  rw [value_head_cps10_05]
  apply bind_equal9
  intro s5
  rw [value_head_cps10_06]
  apply bind_equal9
  intro s6
  rw [value_head_cps10_07]
  apply bind_equal9
  intro s7
  rw [value_head_cps10_08]
  apply bind_equal9
  intro s8
  rw [value_head_cps10_09]
  apply bind_equal9
  intro s9
  rw [value_head_cps10_10]
  apply bind_equal9
  intro s10
  rw [value_head_cps10_11]
  apply bind_equal9
  intro s11
  rw [value_head_cps10_12]
  apply bind_equal9
  intro s12
  rw [value_head_cps10_13]
  apply bind_equal9
  intro s13
  unfold value_owned_stage9_14 value_read_context9_14
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
