import PV_B3P_SumOperation11227
import PV_B3P_P227_10
namespace PV_B3P_Binding11227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
def sum_context11_poseidon_selectors (sum_operation : SumOperation11)
  (selectors : reference_copy_terminal.Selectors) :
  Result aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors
  := do
  let q ←
    sum_operation selectors.high
      aspis_core.field.QM31.ZERO 0#usize 57#usize
  ok { block := q, «local» := selectors.low }
attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.mul Array.index_usize Array.update
theorem poseidon_selectors_sum_caller11
  (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.poseidon_selectors selectors = sum_context11_poseidon_selectors source_sum_interval11 selectors := by
  have h := congrArg (fun operation => sum_context11_poseidon_selectors operation selectors) sum_operation_binding11
  exact h
#print axioms poseidon_selectors_sum_caller11
end PV_B3P_Binding11227
