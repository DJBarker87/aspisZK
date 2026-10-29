"""Bind actual six emitted scaling stages to source-shaped33-cell loop and frame."""
from pathlib import Path
import sys,json
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';O=D/'resume11';files={}
h='namespace PV_B3P_Binding11227\nopen Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227\nset_option autoImplicit false\n'
s='import PV_B3P_ValueReadTypes9227\nimport PV_B3P_Ordered227\nimport PV_B3P_DigestCpsEq9227\n'+h+'''
abbrev ScaleRange11 := Array aspis_core.field.QM31 33#usize
def scale_cell11 (selector : aspis_core.field.QM31) (range : ScaleRange11) (index : Usize) : Result ScaleRange11 := do
  let original ← Array.index_usize range index
  let scaled ← aspis_core.field.QM31.mul selector original
  Array.update range index scaled

def scale_frame11 (state : ValueState9) (index : Usize) : Result ValueState9 := do
  let next ← scale_cell11 state.1 state.2 index
  .ok (state.1,next)

/-- The scalar is a frame, while every successful write is threaded forward. -/
theorem scale_frame_fold11 (indices : List Usize) (selector : aspis_core.field.QM31) (range : ScaleRange11) :
    PV_B3P_Ordered227.fold scale_frame11 indices (selector,range) = (do
      let next ← PV_B3P_Ordered227.fold (scale_cell11 selector) indices range
      .ok (selector,next)) := by
  induction indices generalizing range with
  | nil => exact Eq.refl _
  | cons index rest ih =>
    simp only [PV_B3P_Ordered227.fold,scale_frame11,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
    apply bind_equal9
    intro next
    exact ih next
#print axioms scale_frame_fold11
end PV_B3P_Binding11227
''';files['PV_B3P_ScaleFrame11227']=s
params='''(packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9)'''
groups=[]
for i in range(8,14):
 start=(i-8)*6;stop=min(start+6,33);idx='['+', '.join(f'{j}#usize'for j in range(start,stop))+']';groups.append(idx)
 s=f'import PV_B3P_ScaleFrame11227\nimport PV_B3P_ValueRead9{i:02}227\n'+h
 s+='attribute [local irreducible] Array.index_usize Array.update aspis_core.field.QM31.mul\n'
 s+=f'''theorem scale_stage11_{i:02} {params} :
    value_direct_stage9_{i:02} packed openings selectors state =
      PV_B3P_Ordered227.fold scale_frame11 {idx} state := by
  rcases state with ⟨selector,range⟩
  rw [scale_frame_fold11]
  unfold value_direct_stage9_{i:02} value_read_context9_{i:02}
  conv_rhs => simp only [PV_B3P_Ordered227.fold,scale_cell11,PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms scale_stage11_{i:02}
end PV_B3P_Binding11227
''';files[f'PV_B3P_ScaleStage11{i:02}227']=s
allidx='['+', '.join(f'{i}#usize'for i in range(33))+']';g='['+', '.join(groups)+']'
s='import PV_B3P_ScaleFrame11227\n'+h
s+=f'''theorem scale_partition11 : ({g} : List (List Usize)).flatten = {allidx} := by
  exact Eq.refl _
#print axioms scale_partition11
end PV_B3P_Binding11227
''';files['PV_B3P_ScalePartition11227']=s
s=''.join(f'import PV_B3P_ScaleStage11{i:02}227\n'for i in range(8,14))+'import PV_B3P_ScalePartition11227\n'+h
s+='attribute [local irreducible] scale_frame11 value_direct_stage9_08 value_direct_stage9_09 value_direct_stage9_10 value_direct_stage9_11 value_direct_stage9_12 value_direct_stage9_13\n'
s+=f'def scaling_stages11 {params} : Result ValueState9 := do\n'
for i in range(8,13):s+=f'  let s{i} ← value_direct_stage9_{i:02} packed openings selectors '+('state' if i==8 else f's{i-1}')+'\n'
s+='  value_direct_stage9_13 packed openings selectors s12\n'
s+=f'''theorem scaling_stages_fold11 {params} :
    scaling_stages11 packed openings selectors state =
      PV_B3P_Ordered227.fold scale_frame11 {allidx} state := by
  unfold scaling_stages11
  simp only [scale_stage11_08,scale_stage11_09,scale_stage11_10,scale_stage11_11,scale_stage11_12,scale_stage11_13]
  have h := PV_B3P_Ordered227.flatten scale_frame11 {g} state
  rw [scale_partition11] at h
  simpa only [PV_B3P_Ordered227.ranges,bind_tc_ok,PV_B3P_Binding9227.result_right] using h
#print axioms scaling_stages_fold11
end PV_B3P_Binding11227
''';s=s.replace('import PV_B3P_ScalePartition11227\n','import PV_B3P_ScalePartition11227\nimport PV_B3P_NineUnroll9227\n');files['PV_B3P_ScaleCompose11227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
(O/'scale-modules.json').write_text(json.dumps(list(files),indent=2)+'\n')if '--check'not in sys.argv else None
