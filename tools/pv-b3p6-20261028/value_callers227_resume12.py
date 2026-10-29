"""Replace rejected whole-value contexts by two small, named stage contexts.
No depth/heartbeat limit changes; all unchanged stages stay locally opaque.
"""
from pathlib import Path
import re,json,sys
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';files={}
h='namespace PV_B3P_Binding12227\nopen Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result\nset_option autoImplicit false\n'
specs=[(7,'reconstruct','reference_terminal.reconstruct_10','Array aspis_core.field.QM31 16#usize → Result aspis_core.field.QM31','source_reconstruct','(funext fun view => (reconstruct_body_binding view).symm)','PV_B3P_ReconstructBinding9227'),
       (14,'preweighted','reference_terminal.add_preweighted','{N : Usize} → Array aspis_core.field.QM31 24#usize → Usize → Array aspis_core.field.QM31 N → Result (Array aspis_core.field.QM31 24#usize)','@source_preweighted12','preweighted_operation_binding12','PV_B3P_PreweightedLoop12227')]
for i,label,callee,ty,source,law,imp in specs:
 raw=(L/f'PV_B3P_ValueRead9{i:02}227.lean').read_text()
 decl=re.search(r'^def value_read_context9_'+f'{i:02}'+r'\b[\s\S]*?(?=^/--|^def |\Z)',raw,re.M)[0].strip()
 ctx=f'value_context12_{i:02}';stage=f'value_stage12_{i:02}'
 decl=decl.replace('def value_read_context9_'+f'{i:02}','def '+ctx+' (operation : '+ty+')',1).replace(callee,'operation')
 params='''(packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9)'''
 rettype='ValueState9' if i==7 else '(Array aspis_core.field.QM31 24#usize)'
 s=f'import PV_B3P_ValueRead9{i:02}227\nimport {imp}\n'+h+decl+'\n'
 s+=f'''def {stage} {params} : Result {rettype} :=
  {ctx} ({source}) (fun values i => Array.index_usize values i) packed openings selectors state
theorem value_stage_binding12_{i:02} {params} :
    value_direct_stage9_{i:02} packed openings selectors state = {stage} packed openings selectors state :=
  congrArg (fun (operation : {ty}) => {ctx} @operation
    (fun values i => Array.index_usize values i) packed openings selectors state) {law}
#print axioms value_stage_binding12_{i:02}
end PV_B3P_Binding12227
'''
 files[f'PV_B3P_ValueCallerStage12{i:02}227']=s
s='import PV_B3P_ValueCallerStage1207227\nimport PV_B3P_ValueCallerStage1214227\nimport PV_B3P_ValueScalingBridge11227\n'+h
s+='open PV_B3P_Binding11227\n'
s+='attribute [local irreducible] '+ ' '.join(f'value_direct_stage9_{i:02}' for i in range(15))+' value_stage12_07 value_stage12_14 scale_frame11\n'
params='''(packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)'''
s+=f'def value_source12 {params} : Result (Array aspis_core.field.QM31 24#usize) := do\n'
for i in range(8):
 fn=f'value_stage12_{i:02}' if i==7 else f'value_direct_stage9_{i:02}'
 s+=f'  let s{i} ← {fn} packed openings selectors'+('' if i==0 else f' s{i-1}')+'\n'
s+='  let scaled ← loop (usize_body scale_frame11 33#usize) (s7,0#usize)\n  value_stage12_14 packed openings selectors scaled\n'
s+=f'''theorem value_caller_binding12 {params} :
    reference_terminal.add_value_lanes packed openings selectors = value_source12 packed openings selectors := by
  rw [add_value_scaling_binding11]
  unfold value_scaling_source11 value_source12
  simp only [value_stage_binding12_07,value_stage_binding12_14]
#print axioms value_caller_binding12
end PV_B3P_Binding12227
'''
files['PV_B3P_ValueCallerBridge12227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
if '--check'not in sys.argv:(D/'resume12/value-caller-modules.json').write_text(json.dumps(list(files),indent=2)+'\n')
