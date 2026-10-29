import PV_B3P_ScaleLoop11227
import PV_B3P_ValueSequenceBridge10227
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227
set_option autoImplicit false
attribute [local irreducible] value_direct_stage9_00 value_direct_stage9_01 value_direct_stage9_02 value_direct_stage9_03 value_direct_stage9_04 value_direct_stage9_05 value_direct_stage9_06 value_direct_stage9_07 value_direct_stage9_08 value_direct_stage9_09 value_direct_stage9_10 value_direct_stage9_11 value_direct_stage9_12 value_direct_stage9_13 value_direct_stage9_14 scale_frame11 reference_terminal.add_value_lanes
def value_scaling_source11 (packed : Array aspis_core.field.QM31 24#usize)
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
  let scaled ← loop (usize_body scale_frame11 33#usize) (s7,0#usize)
  value_direct_stage9_14 packed openings selectors scaled
theorem value_direct_scaling11 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    value_direct_sequence9 packed openings selectors = value_scaling_source11 packed openings selectors := by
  unfold value_direct_sequence9 value_scaling_source11
  apply bind_equal9
  intro s0
  apply bind_equal9
  intro s1
  apply bind_equal9
  intro s2
  apply bind_equal9
  intro s3
  apply bind_equal9
  intro s4
  apply bind_equal9
  intro s5
  apply bind_equal9
  intro s6
  apply bind_equal9
  intro s7
  have h := congrArg (fun result => result >>= value_direct_stage9_14 packed openings selectors)
    (scaling_stages_loop11 packed openings selectors s7)
  simpa only [scaling_stages11,PV_B3P_Ordered227.bind_assoc] using h
theorem add_value_scaling_binding11 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.add_value_lanes packed openings selectors = value_scaling_source11 packed openings selectors :=
  (add_value_read_binding10 packed openings selectors).trans (value_direct_scaling11 packed openings selectors)
#print axioms value_direct_scaling11
#print axioms add_value_scaling_binding11
end PV_B3P_Binding11227
