import PV_B3P_NativeSumHigh15227
import PV_B3P_Operations12227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def native_poseidon_selectors15 (selectors : reference_copy_terminal.Selectors) :
    Result aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors := do
  let block ← source_sum_ranges13 selectors.high [(0#usize,57#usize)] aspis_core.field.QM31.ZERO
  .ok { block := block, «local» := selectors.low }

theorem native_poseidon_selectors_binding15 (selectors : reference_copy_terminal.Selectors) :
    native_poseidon_selectors15 selectors = PV_B3P_227.reference_terminal.poseidon_selectors selectors := by
  have interval := congrFun (congrFun (congrFun (congrFun sum_operation_binding11 selectors.high)
    aspis_core.field.QM31.ZERO) 0#usize) 57#usize
  unfold source_sum_interval11 at interval
  unfold native_poseidon_selectors15 PV_B3P_227.reference_terminal.poseidon_selectors
  simp only [source_sum_ranges13,range_loop_binding13,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
  rw [←interval]
#print axioms native_poseidon_selectors_binding15
end PV_B3P_Native15227
