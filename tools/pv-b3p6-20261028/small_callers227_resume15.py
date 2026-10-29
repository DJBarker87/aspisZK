from pathlib import Path
L=Path('evidence/pv-b3p6-20261028/lean');h='''namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false
'''
s='import PV_B3P_NativeSumHigh15227\nimport PV_B3P_Operations12227\n'+h+'''
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
''';(L/'PV_B3P_PoseidonSelectorCaller15227.lean').write_text(s)
s='import PV_B3P_NativePreweighted15227\n'+h.replace('PV_B3P_Binding13227 ','')+'''
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
''';(L/'PV_B3P_ScheduleCaller15227.lean').write_text(s)
