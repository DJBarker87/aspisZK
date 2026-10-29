import PV_B3P_NativePreweighted15227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 Result
set_option autoImplicit false

def native_schedule15 (packed : Array aspis_core.field.QM31 24#usize)
    (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result (Array aspis_core.field.QM31 24#usize) := do
  let (initial,absorption) ← reference_terminal.semantic_initial_and_absorption public1 openings selectors
  let packed1 ← native_preweighted15 packed 0#usize initial
  native_preweighted15 packed1 16#usize absorption

theorem native_schedule_binding15 (packed : Array aspis_core.field.QM31 24#usize)
    (public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    native_schedule15 packed public1 openings selectors =
      PV_B3P_227.reference_terminal.add_schedule_lanes packed public1 openings selectors := by
  unfold native_schedule15 PV_B3P_227.reference_terminal.add_schedule_lanes
  simp only [native_preweighted_binding15]
#print axioms native_schedule_binding15
end PV_B3P_Native15227
