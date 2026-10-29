import PV_B3P_ValueCallerStage1207227
import PV_B3P_ValueCallerStage1214227
import PV_B3P_ValueScalingBridge11227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result
set_option autoImplicit false
open PV_B3P_Binding11227
attribute [local irreducible] value_direct_stage9_00 value_direct_stage9_01 value_direct_stage9_02 value_direct_stage9_03 value_direct_stage9_04 value_direct_stage9_05 value_direct_stage9_06 value_direct_stage9_07 value_direct_stage9_08 value_direct_stage9_09 value_direct_stage9_10 value_direct_stage9_11 value_direct_stage9_12 value_direct_stage9_13 value_direct_stage9_14 value_stage12_07 value_stage12_14 scale_frame11
def value_source12 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result (Array aspis_core.field.QM31 24#usize) := do
  let s0 ← value_direct_stage9_00 packed openings selectors
  let s1 ← value_direct_stage9_01 packed openings selectors s0
  let s2 ← value_direct_stage9_02 packed openings selectors s1
  let s3 ← value_direct_stage9_03 packed openings selectors s2
  let s4 ← value_direct_stage9_04 packed openings selectors s3
  let s5 ← value_direct_stage9_05 packed openings selectors s4
  let s6 ← value_direct_stage9_06 packed openings selectors s5
  let s7 ← value_stage12_07 packed openings selectors s6
  let scaled ← loop (usize_body scale_frame11 33#usize) (s7,0#usize)
  value_stage12_14 packed openings selectors scaled
theorem value_caller_binding12 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.add_value_lanes packed openings selectors = value_source12 packed openings selectors := by
  rw [add_value_scaling_binding11]
  unfold value_scaling_source11 value_source12
  simp only [value_stage_binding12_07,value_stage_binding12_14]
#print axioms value_caller_binding12
end PV_B3P_Binding12227
