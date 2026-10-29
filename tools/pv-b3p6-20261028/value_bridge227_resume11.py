"""Compose source scaling loop into actual value entry through small named stages."""
from pathlib import Path
import sys
L=Path('evidence/pv-b3p6-20261028/lean');h='namespace PV_B3P_Binding11227\nopen Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding10227\nset_option autoImplicit false\n'
params='''(packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)'''
s='import PV_B3P_ScaleLoop11227\nimport PV_B3P_ValueSequenceBridge10227\n'+h
s+='attribute [local irreducible] '+ ' '.join(f'value_direct_stage9_{i:02}'for i in range(15))+' scale_frame11 reference_terminal.add_value_lanes\n'
s+=f'def value_scaling_source11 {params} : Result (Array aspis_core.field.QM31 24#usize) := do\n'
for i in range(8):s+=f'  let s{i} ← value_direct_stage9_{i:02} packed openings selectors'+(''if i==0 else f' s{i-1}')+'\n'
s+='  let scaled ← loop (usize_body scale_frame11 33#usize) (s7,0#usize)\n  value_direct_stage9_14 packed openings selectors scaled\n'
s+=f'''theorem value_direct_scaling11 {params} :
    value_direct_sequence9 packed openings selectors = value_scaling_source11 packed openings selectors := by
  unfold value_direct_sequence9 value_scaling_source11
'''
for i in range(8):s+=f'  apply bind_equal9\n  intro s{i}\n'
s+='''  have h := congrArg (fun result => result >>= value_direct_stage9_14 packed openings selectors)
    (scaling_stages_loop11 packed openings selectors s7)
  simpa only [scaling_stages11,PV_B3P_Ordered227.bind_assoc] using h
'''
s+=f'''theorem add_value_scaling_binding11 {params} :
    reference_terminal.add_value_lanes packed openings selectors = value_scaling_source11 packed openings selectors :=
  (add_value_read_binding10 packed openings selectors).trans (value_direct_scaling11 packed openings selectors)
#print axioms value_direct_scaling11
#print axioms add_value_scaling_binding11
end PV_B3P_Binding11227
'''
files={'PV_B3P_ValueScalingBridge11227':s}
s='import PV_B3P_ScaleLoop11227\n'+h.replace(' PV_B3P_Binding10227','')
s+='''theorem scale_loop_frame11 (selector : aspis_core.field.QM31) (range : ScaleRange11) :
    loop (usize_body scale_frame11 33#usize) ((selector,range),0#usize) = (do
      let next ← loop (usize_body (scale_cell11 selector) 33#usize) (range,0#usize)
      .ok (selector,next)) := by
  rw [loop_as_fold11 scale_frame11 33#usize 0#usize 33 (selector,range) (Eq.refl _)]
  rw [loop_as_fold11 (scale_cell11 selector) 33#usize 0#usize 33 range (Eq.refl _)]
  exact scale_frame_fold11 _ selector range
#print axioms scale_loop_frame11
end PV_B3P_Binding11227
''';files['PV_B3P_ScaleLoopFrame11227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
