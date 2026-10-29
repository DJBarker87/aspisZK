"""Pure counter-list shape, then symbolic loop transport; no field evaluation."""
from pathlib import Path
import sys
L=Path('evidence/pv-b3p6-20261028/lean');files={}
h='namespace PV_B3P_Binding11227\nopen Aeneas Aeneas.Std PV_B3P_Binding9227\nset_option autoImplicit false\n'
s='import PV_B3P_UsizeLoop9227\nimport PV_B3P_Ordered227\n'+h+'''
def usize_indices11 : Nat → Usize → List Usize
  | 0, _ => []
  | n+1, i => i :: usize_indices11 n (Usize.wrapping_add i 1#usize)

theorem plan_as_fold11 {α : Type} (step : α → Usize → Result α)
    (n : Nat) (i : Usize) (state : α) :
    usize_plan step n i state = PV_B3P_Ordered227.fold step (usize_indices11 n i) state := by
  induction n generalizing i state with
  | zero => exact Eq.refl _
  | succ n ih =>
    simp only [usize_plan,usize_indices11,PV_B3P_Ordered227.fold]
    exact congrArg (fun k => step state i >>= k) (funext fun next => ih _ next)

theorem loop_as_fold11 {α : Type} (step : α → Usize → Result α)
    (stop i : Usize) (n : Nat) (state : α) (h : i.val+n=stop.val) :
    loop (usize_body step stop) (state,i) =
      PV_B3P_Ordered227.fold step (usize_indices11 n i) state :=
  (usize_loop_plan step stop i n state h).trans (plan_as_fold11 step n i state)
#print axioms plan_as_fold11
#print axioms loop_as_fold11
end PV_B3P_Binding11227
''';files['PV_B3P_PlanFold11227']=s
for size in [20,33]:
 s='import PV_B3P_PlanFold11227\nimport PV_B3P_IndexSteps9227\n'+h
 for i in range(size):s+=f'theorem next11_{size}_{i} : Usize.wrapping_add {i}#usize 1#usize = {i+1}#usize := next_exact _ _ (Eq.refl _)\n#print axioms next11_{size}_{i}\n'
 idx='['+', '.join(f'{i}#usize'for i in range(size))+']'
 s+=f'theorem indices11_{size} : usize_indices11 {size} 0#usize = {idx} := by\n  simp only [usize_indices11,'+','.join(f'next11_{size}_{i}'for i in range(size))+']\n'
 s+=f'#print axioms indices11_{size}\nend PV_B3P_Binding11227\n';files[f'PV_B3P_Indices{size}11227']=s
s='import PV_B3P_ScaleCompose11227\nimport PV_B3P_Indices3311227\n'+h+'open PV_B3P_227\n'
params='''(packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9)'''
s+=f'''theorem scaling_stages_loop11 {params} :
    scaling_stages11 packed openings selectors state =
      loop (usize_body scale_frame11 33#usize) (state,0#usize) := by
  rw [loop_as_fold11 scale_frame11 33#usize 0#usize 33 state (Eq.refl _),indices11_33]
  exact scaling_stages_fold11 packed openings selectors state
#print axioms scaling_stages_loop11
end PV_B3P_Binding11227
''';files['PV_B3P_ScaleLoop11227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
