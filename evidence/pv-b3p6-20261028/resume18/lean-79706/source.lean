import PV_B3P_ExpandSource554227
import PV_B3P_ExpandSuccess227
import PV_B3P_PoseidonSelectorCaller15227
import PV_B3P_SelectorCorrection14227
namespace PV_B3P_Association554227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding11227 PV_B3P_Success227
set_option autoImplicit false

/-- The statement constructor sums 49 high weights before expanding local. -/
def statement_constructor49_source554 (point : Array aspis_core.field.QM31 10#usize) :
    Result aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors := do
  let high ← expand_source554 64#usize point 0#usize 6#usize
  let block ← source_sum_interval11 high aspis_core.field.QM31.ZERO 0#usize 49#usize
  let low ← expand_source554 16#usize point 6#usize 4#usize
  .ok { block, «local» := low }

theorem statement_constructor49_reference554 (point : Array aspis_core.field.QM31 10#usize) :
    statement_constructor49_source554 point = PV_B3P_Correct14227.constructor14 49#usize point := by
  obtain ⟨high,hh⟩ := expand_total 64#usize point 0#usize 6#usize
    (by change 0+6≤10; omega) (by change 64≤64; omega)
  obtain ⟨low,hl⟩ := expand_total 16#usize point 6#usize 4#usize
    (by change 6+4≤10; omega) (by change 16≤16; omega)
  unfold statement_constructor49_source554 PV_B3P_Correct14227.constructor14
    reference_copy_terminal.Selectors.at_point
  simp only [expand_source_reference554,←sum_operation_binding11,hh,hl,bind_tc_ok]

/-- The terminal constructor expands both arrays and selects the 57-row prefix. -/
def terminal_constructor57_source554 (point : Array aspis_core.field.QM31 10#usize) :
    Result aspis_statement.state_only_poseidon.StateOnlyPoseidonSelectors := do
  let high ← expand_source554 64#usize point 0#usize 6#usize
  let low ← expand_source554 16#usize point 6#usize 4#usize
  PV_B3P_Native15227.native_poseidon_selectors15 { high, low }

theorem terminal_constructor57_reference554 (point : Array aspis_core.field.QM31 10#usize) :
    terminal_constructor57_source554 point = PV_B3P_Links13227.selector_reference13 point := by
  unfold terminal_constructor57_source554 PV_B3P_Links13227.selector_reference13
    reference_copy_terminal.Selectors.at_point
  simp only [expand_source_reference554,PV_B3P_Native15227.native_poseidon_selectors_binding15,
    PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

theorem terminal_constructor57_link554 :
    PV_B3P_Links13227.PV_B3P_Link_poseidon_at_point terminal_constructor57_source554 :=
  funext terminal_constructor57_reference554

#print axioms statement_constructor49_reference554
#print axioms terminal_constructor57_reference554
#print axioms terminal_constructor57_link554
end PV_B3P_Association554227
