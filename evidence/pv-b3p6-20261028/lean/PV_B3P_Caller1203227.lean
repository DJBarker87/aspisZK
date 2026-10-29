import PV_B3P_P227_14
import PV_B3P_PreweightedLoop12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false
def context12_preweighted_reference_terminal_add_occupancy_lanes (operation : {N : Usize} → Array aspis_core.field.QM31 24#usize → Usize → Array aspis_core.field.QM31 N → Result (Array aspis_core.field.QM31 24#usize))
  (packed : Array aspis_core.field.QM31 24#usize)
  (public1 : reference_terminal.SemanticPublic)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors) :
  Result (Array aspis_core.field.QM31 24#usize)
  := do
  let i ← reference_terminal.INPUT_OCCUPANCY_ROW
  let input_occupancy ← reference_copy_terminal.Selectors.row selectors i
  let i1 ← reference_terminal.OUTPUT_OCCUPANCY_ROW
  let output_occupancy ← reference_copy_terminal.Selectors.row selectors i1
  let expected_output ←
    reference_terminal.variant_expected_output public1.variant
  let occupancy ←
    reference_terminal.occupancy_lanes_literal input_occupancy output_occupancy
      expected_output openings.z
  operation packed 0#usize occupancy
theorem caller12_preweighted_reference_terminal_add_occupancy_lanes 
  (packed : Array aspis_core.field.QM31 24#usize)
  (public1 : reference_terminal.SemanticPublic)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors) :
    @reference_terminal.add_occupancy_lanes packed public1 openings selectors = @context12_preweighted_reference_terminal_add_occupancy_lanes (@source_preweighted12) packed public1 openings selectors :=
  congrArg (fun (operation : {N : Usize} → Array aspis_core.field.QM31 24#usize → Usize → Array aspis_core.field.QM31 N → Result (Array aspis_core.field.QM31 24#usize)) => @context12_preweighted_reference_terminal_add_occupancy_lanes @operation packed public1 openings selectors) preweighted_operation_binding12
#print axioms caller12_preweighted_reference_terminal_add_occupancy_lanes
end PV_B3P_Binding12227
