import PV_B3P_ValueRead900227
import PV_B3P_ValueRead901227
import PV_B3P_ValueRead902227
import PV_B3P_ValueRead903227
import PV_B3P_ValueRead904227
import PV_B3P_ValueRead905227
import PV_B3P_ValueRead906227
import PV_B3P_ValueRead907227
import PV_B3P_ValueRead908227
import PV_B3P_ValueRead909227
import PV_B3P_ValueRead910227
import PV_B3P_ValueRead911227
import PV_B3P_ValueRead912227
import PV_B3P_ValueRead913227
import PV_B3P_ValueRead914227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

def value_owned_sequence9 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result (Array aspis_core.field.QM31 24#usize) := do
  let s0 ← value_owned_stage9_00 packed openings selectors
  let s1 ← value_owned_stage9_01 packed openings selectors s0
  let s2 ← value_owned_stage9_02 packed openings selectors s1
  let s3 ← value_owned_stage9_03 packed openings selectors s2
  let s4 ← value_owned_stage9_04 packed openings selectors s3
  let s5 ← value_owned_stage9_05 packed openings selectors s4
  let s6 ← value_owned_stage9_06 packed openings selectors s5
  let s7 ← value_owned_stage9_07 packed openings selectors s6
  let s8 ← value_owned_stage9_08 packed openings selectors s7
  let s9 ← value_owned_stage9_09 packed openings selectors s8
  let s10 ← value_owned_stage9_10 packed openings selectors s9
  let s11 ← value_owned_stage9_11 packed openings selectors s10
  let s12 ← value_owned_stage9_12 packed openings selectors s11
  let s13 ← value_owned_stage9_13 packed openings selectors s12
  value_owned_stage9_14 packed openings selectors s13

def value_direct_sequence9 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result (Array aspis_core.field.QM31 24#usize) := do
  let s0 ← value_direct_stage9_00 packed openings selectors
  let s1 ← value_direct_stage9_01 packed openings selectors s0
  let s2 ← value_direct_stage9_02 packed openings selectors s1
  let s3 ← value_direct_stage9_03 packed openings selectors s2
  let s4 ← value_direct_stage9_04 packed openings selectors s3
  let s5 ← value_direct_stage9_05 packed openings selectors s4
  let s6 ← value_direct_stage9_06 packed openings selectors s5
  let s7 ← value_direct_stage9_07 packed openings selectors s6
  let s8 ← value_direct_stage9_08 packed openings selectors s7
  let s9 ← value_direct_stage9_09 packed openings selectors s8
  let s10 ← value_direct_stage9_10 packed openings selectors s9
  let s11 ← value_direct_stage9_11 packed openings selectors s10
  let s12 ← value_direct_stage9_12 packed openings selectors s11
  let s13 ← value_direct_stage9_13 packed openings selectors s12
  value_direct_stage9_14 packed openings selectors s13

attribute [local irreducible] value_owned_stage9_00 value_owned_stage9_01 value_owned_stage9_02 value_owned_stage9_03 value_owned_stage9_04 value_owned_stage9_05 value_owned_stage9_06 value_owned_stage9_07 value_owned_stage9_08 value_owned_stage9_09 value_owned_stage9_10 value_owned_stage9_11 value_owned_stage9_12 value_owned_stage9_13 value_owned_stage9_14 value_direct_stage9_00 value_direct_stage9_01 value_direct_stage9_02 value_direct_stage9_03 value_direct_stage9_04 value_direct_stage9_05 value_direct_stage9_06 value_direct_stage9_07 value_direct_stage9_08 value_direct_stage9_09 value_direct_stage9_10 value_direct_stage9_11 value_direct_stage9_12 value_direct_stage9_13 value_direct_stage9_14

theorem value_sequence_read_binding9 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    value_owned_sequence9 packed openings selectors = value_direct_sequence9 packed openings selectors := by
  unfold value_owned_sequence9 value_direct_sequence9
  simp only [value_stage_read_binding9_00]
  simp only [value_stage_read_binding9_01]
  simp only [value_stage_read_binding9_02]
  simp only [value_stage_read_binding9_03]
  simp only [value_stage_read_binding9_04]
  simp only [value_stage_read_binding9_05]
  simp only [value_stage_read_binding9_06]
  simp only [value_stage_read_binding9_07]
  simp only [value_stage_read_binding9_08]
  simp only [value_stage_read_binding9_09]
  simp only [value_stage_read_binding9_10]
  simp only [value_stage_read_binding9_11]
  simp only [value_stage_read_binding9_12]
  simp only [value_stage_read_binding9_13]
  simp only [value_stage_read_binding9_14]

#print axioms value_sequence_read_binding9
end PV_B3P_Binding9227
