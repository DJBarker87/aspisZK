import PV_B3P_P227_14
import PV_B3P_PreweightedLoop12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false
def context12_preweighted_reference_terminal_add_schedule_lanes (operation : {N : Usize} → Array aspis_core.field.QM31 24#usize → Usize → Array aspis_core.field.QM31 N → Result (Array aspis_core.field.QM31 24#usize))
  (packed : Array aspis_core.field.QM31 24#usize)
  (public1 : reference_terminal.SemanticPublic)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors) :
  Result (Array aspis_core.field.QM31 24#usize)
  := do
  let (initial, absorption) ←
    reference_terminal.semantic_initial_and_absorption public1 openings
      selectors
  let packed1 ← operation packed 0#usize initial
  operation packed1 16#usize absorption
theorem caller12_preweighted_reference_terminal_add_schedule_lanes 
  (packed : Array aspis_core.field.QM31 24#usize)
  (public1 : reference_terminal.SemanticPublic)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors) :
    @reference_terminal.add_schedule_lanes packed public1 openings selectors = @context12_preweighted_reference_terminal_add_schedule_lanes (@source_preweighted12) packed public1 openings selectors :=
  congrArg (fun operation => @context12_preweighted_reference_terminal_add_schedule_lanes operation packed public1 openings selectors) preweighted_operation_binding12
#print axioms caller12_preweighted_reference_terminal_add_schedule_lanes
end PV_B3P_Binding12227
