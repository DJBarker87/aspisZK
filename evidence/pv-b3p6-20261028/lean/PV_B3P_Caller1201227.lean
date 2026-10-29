import PV_B3P_P227_14
import PV_B3P_PreweightedLoop12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false
def context12_preweighted_reference_terminal_add_path_lanes (operation : {N : Usize} → Array aspis_core.field.QM31 24#usize → Usize → Array aspis_core.field.QM31 N → Result (Array aspis_core.field.QM31 24#usize))
  (packed : Array aspis_core.field.QM31 24#usize)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors) :
  Result (Array aspis_core.field.QM31 24#usize)
  := do
  let q ←
    reference_terminal.sum_interval227 selectors.high
      aspis_core.field.QM31.ZERO 57#usize 63#usize
  let q1 ← Array.index_usize selectors.low 1#usize
  let q2 ← Array.index_usize selectors.low 5#usize
  let q3 ← aspis_core.field.QM31.add q1 q2
  let q4 ← Array.index_usize selectors.low 9#usize
  let q5 ← aspis_core.field.QM31.add q3 q4
  let q6 ← Array.index_usize selectors.low 13#usize
  let q7 ← aspis_core.field.QM31.add q5 q6
  let path_selector ← aspis_core.field.QM31.mul q q7
  let path ← reference_terminal.path_lanes_literal path_selector openings
  operation packed 32#usize path
theorem caller12_preweighted_reference_terminal_add_path_lanes 
  (packed : Array aspis_core.field.QM31 24#usize)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors) :
    @reference_terminal.add_path_lanes packed openings selectors = @context12_preweighted_reference_terminal_add_path_lanes (@source_preweighted12) packed openings selectors :=
  congrArg (fun operation => @context12_preweighted_reference_terminal_add_path_lanes operation packed openings selectors) preweighted_operation_binding12
#print axioms caller12_preweighted_reference_terminal_add_path_lanes
end PV_B3P_Binding12227
