import PV_B3P_SumCaller112227
import PV_B3P_SumCaller111227
import PV_B3P_NativePath15227
import PV_B3P_NativePreweighted15227
import PV_B3P_ValueScalingBridge11227
import PV_B3P_LinkDefinitions13227
namespace PV_B3P_Association554227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding11227 PV_B3P_Native15227
set_option autoImplicit false

/-- Selected client configuration has no optimized-terminal feature. -/
def path_dispatch_source554 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result (Array aspis_core.field.QM31 24#usize) := do
  let nodes ← source_sum_interval11 selectors.high aspis_core.field.QM31.ZERO 57#usize 63#usize
  let l1 ← Array.index_usize selectors.low 1#usize
  let l5 ← Array.index_usize selectors.low 5#usize
  let s1 ← aspis_core.field.QM31.add l1 l5
  let l9 ← Array.index_usize selectors.low 9#usize
  let s2 ← aspis_core.field.QM31.add s1 l9
  let l13 ← Array.index_usize selectors.low 13#usize
  let s3 ← aspis_core.field.QM31.add s2 l13
  let selected ← aspis_core.field.QM31.mul nodes s3
  let path ← native_path15 selected openings
  native_preweighted15 packed 32#usize path

theorem path_dispatch_reference554 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    path_dispatch_source554 packed openings selectors = reference_terminal.add_path_lanes packed openings selectors := by
  rw [add_path_lanes_sum_caller11]
  unfold path_dispatch_source554 sum_context11_add_path_lanes
  simp only [native_path_binding15,native_preweighted_binding15]

theorem path_dispatch_source_link554 :
    PV_B3P_Links13227.PV_B3P_Link_terminal_add_path_lanes path_dispatch_source554 :=
  funext fun packed => funext fun openings => funext (path_dispatch_reference554 packed openings)

/-- Whole source association is recorded separately, including the selected
33-write scaling branch; this proof retains the original total Link. -/
theorem value_source_link554 :
    PV_B3P_Links13227.PV_B3P_Link_terminal_add_value_lanes value_scaling_source11 := by
  funext packed openings selectors
  exact (add_value_scaling_binding11 packed openings selectors).symm

theorem initial_absorption_source_link554 :
    PV_B3P_Links13227.PV_B3P_Link_terminal_semantic_initial_and_absorption
      (sum_context11_semantic_initial_and_absorption source_sum_interval11) := by
  funext public1 openings selectors
  exact (semantic_initial_and_absorption_sum_caller11 public1 openings selectors).symm

#print axioms path_dispatch_reference554
#print axioms path_dispatch_source_link554
#print axioms value_source_link554
#print axioms initial_absorption_source_link554
end PV_B3P_Association554227
