from pathlib import Path
L=Path('evidence/pv-b3p6-20261028/lean');h='''namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false
'''
s='import PV_B3P_RangeFold13227\n'+h.replace('PV_B3P_227 ','')+'''
theorem fold_pointwise15 {α β : Type} (left right : α → β → Result α)
    (indices : List β) (state : α)
    (same : ∀ index ∈ indices, ∀ state, left state index = right state index) :
    PV_B3P_Ordered227.fold left indices state = PV_B3P_Ordered227.fold right indices state := by
  induction indices generalizing state with
  | nil => rfl
  | cons index rest ih =>
    simp only [PV_B3P_Ordered227.fold]
    rw [same index (by simp)]
    apply congrArg (Aeneas.Std.bind _)
    funext next
    exact ih next (fun i member => same i (by simp only [List.mem_cons]; exact Or.inr member))

theorem indices_bound_sixteen15 (index : Usize) (member : index ∈ usize_indices11 16 0#usize) : index.val < 16 := by
  rw [indices_sixteen13] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals subst index; decide
#print axioms fold_pointwise15
#print axioms indices_bound_sixteen15
end PV_B3P_Native15227
''';(L/'PV_B3P_BoundedFold15227.lean').write_text(s)
s='import PV_B3P_AbsorptionStep15227\nimport PV_B3P_SelectIndex227\n'+h+'''
def absorption_native_value15 (lane : Usize) (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31)
    (openings : Array aspis_core.field.QM31 16#usize) : Result aspis_core.field.QM31 := do
  let blocks ← if lane < 2#usize then .ok fixed
    else if lane < aspis_statement.poseidon2.RATE then aspis_core.field.QM31.add fixed chunk_two
    else do
      let a ← aspis_core.field.QM31.add fixed chunk_two
      let b ← aspis_core.field.QM31.add a chunk_eight
      aspis_core.field.QM31.add b nodes
  let scaled ← aspis_core.field.QM31.mul low blocks
  let opened ← Array.index_usize openings lane
  aspis_core.field.QM31.mul scaled opened

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.mul Array.update

theorem absorption_native_value_binding15 (lane : Usize) (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31)
    (openings : Array aspis_core.field.QM31 16#usize) (bound : lane.val < 16) :
    absorption_native_value15 lane low fixed chunk_two chunk_eight nodes openings =
      (do let opened ← reference_terminal.read227 openings lane
          reference_terminal.absorption_lane227 lane low fixed chunk_two chunk_eight nodes opened) := by
  have read := PV_B3P_SelectIndex227.index_value openings lane bound
  simp only [absorption_native_value15,reference_terminal.read227,
    reference_terminal.absorption_lane227,read,bind_tc_ok,PV_B3P_Ordered227.bind_assoc]
#print axioms absorption_native_value_binding15
end PV_B3P_Native15227
''';(L/'PV_B3P_AbsorptionNativeRead15227.lean').write_text(s)
for label,args,pars,sourcecall in [
 ('Interpolation','weights column0 column1 column2','(weights : Array aspis_core.field.QM31 3#usize) (column0 column1 column2 : Array U32 16#usize)','interpolation_native_value15 weights column0 column1 column2 lane'),
 ('Absorption','low fixed chunk_two chunk_eight nodes openings','(low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31) (openings : Array aspis_core.field.QM31 16#usize)','absorption_native_value15 lane low fixed chunk_two chunk_eight nodes openings')]:
 lo=label.lower();s=f'import PV_B3P_Native{label}15227\nimport PV_B3P_{label}Native'+('Reads'if label=='Interpolation'else'Read')+'15227\nimport PV_B3P_BoundedFold15227\n'+h
 s+=f'''\ndef {lo}_source_step15 {pars} (state : Array aspis_core.field.QM31 16#usize) (lane : Usize) : Result (Array aspis_core.field.QM31 16#usize) := do
  let value ← {sourcecall}
  Array.update state lane value

theorem {lo}_source_step_binding15 {pars} (state : Array aspis_core.field.QM31 16#usize)
    (lane : Usize) (bound : lane.val < 16) :
    {lo}_source_step15 {args} state lane = {lo}_step15 {args} state lane := by
  unfold {lo}_source_step15 {lo}_step15
  rw [{lo}_native_value_binding15 {'lane '+args if label=='Absorption' else args+' lane'} bound]
  simp only [PV_B3P_Ordered227.bind_assoc]

def {lo}_source15 {pars} : Result (Array aspis_core.field.QM31 16#usize) :=
  loop (usize_body ({lo}_source_step15 {args}) 16#usize)
    (Array.repeat 16#usize aspis_core.field.QM31.ZERO,0#usize)

theorem {lo}_source_binding15 {pars} :
    {lo}_source15 {args} = reference_{'poseidon.interpolate_three_constant_columns' if label=='Interpolation'else'terminal.absorption_lanes_literal'} {args} := by
  rw [←native_{lo}_binding15]
  unfold {lo}_source15 native_{lo}15
  rw [loop_as_fold11 _ 16#usize 0#usize 16 _ (by rfl),
    range_as_fold13 _ 0#usize 16#usize 16 _ (by rfl)]
  apply fold_pointwise15
  intro index member state
  exact {lo}_source_step_binding15 {args} state index (indices_bound_sixteen15 index member)
#print axioms {lo}_source_step_binding15
#print axioms {lo}_source_binding15
end PV_B3P_Native15227
'''
 (L/f'PV_B3P_{label}Source15227.lean').write_text(s)
