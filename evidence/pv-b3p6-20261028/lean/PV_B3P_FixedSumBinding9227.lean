import PV_B3P_SumLoopBinding9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

theorem sum_all_binding9 (high : Array aspis_core.field.QM31 64#usize)
    (initial : aspis_core.field.QM31) :
    reference_terminal.sum_interval227 high initial 0#usize 57#usize =
      usize_plan (sum_step high) 57 0#usize initial :=
  sum_interval_binding high 57#usize 0#usize 57 initial rfl
#print axioms sum_all_binding9

theorem sum_nodes_first_binding9 (high : Array aspis_core.field.QM31 64#usize)
    (initial : aspis_core.field.QM31) :
    reference_terminal.sum_interval227 high initial 4#usize 25#usize =
      usize_plan (sum_step high) 21 4#usize initial :=
  sum_interval_binding high 25#usize 4#usize 21 initial rfl
#print axioms sum_nodes_first_binding9

theorem sum_nodes_second_binding9 (high : Array aspis_core.field.QM31 64#usize)
    (initial : aspis_core.field.QM31) :
    reference_terminal.sum_interval227 high initial 33#usize 57#usize =
      usize_plan (sum_step high) 24 33#usize initial :=
  sum_interval_binding high 57#usize 33#usize 24 initial rfl
#print axioms sum_nodes_second_binding9

theorem sum_occupancy_binding9 (high : Array aspis_core.field.QM31 64#usize)
    (initial : aspis_core.field.QM31) :
    reference_terminal.sum_interval227 high initial 57#usize 63#usize =
      usize_plan (sum_step high) 6 57#usize initial :=
  sum_interval_binding high 63#usize 57#usize 6 initial rfl
#print axioms sum_occupancy_binding9

theorem poseidon_selectors_interval_binding9 (selectors : reference_copy_terminal.Selectors) :
    reference_terminal.poseidon_selectors selectors = (do
      let block ← usize_plan (sum_step selectors.high) 57 0#usize aspis_core.field.QM31.ZERO
      .ok ({block := block, «local» := selectors.low} : aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors)) := by
  unfold reference_terminal.poseidon_selectors
  rw [sum_all_binding9]
#print axioms poseidon_selectors_interval_binding9
end PV_B3P_Binding9227
