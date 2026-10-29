"""Bind interval transformations at actual callers using operation congruence."""
from pathlib import Path
import re,sys,json
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';files={}
h='namespace PV_B3P_Binding11227\nopen Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227\nset_option autoImplicit false\n'
s='import PV_B3P_SumLoopBinding9227\nimport PV_B3P_DigestCpsEq9227\n'+h+'''
abbrev SumOperation11 := Array aspis_core.field.QM31 64#usize → aspis_core.field.QM31 → Usize → Usize → Result aspis_core.field.QM31

def source_sum_interval11 : SumOperation11 := fun high initial start stop =>
  loop (usize_body (sum_step high) stop) (initial,start)

theorem sum_operation_binding11 : reference_terminal.sum_interval227 = source_sum_interval11 := by
  funext high initial start stop
  change reference_terminal.sum_interval227_loop high stop initial start = _
  exact sum_loop_binding high stop initial start

#print axioms sum_operation_binding11
end PV_B3P_Binding11227
''';files['PV_B3P_SumOperation11227']=s
raw=(D/'raw227-parts-resume5/Funs.lean').read_text()
for number,name in enumerate(['poseidon_selectors','semantic_initial_and_absorption','add_path_lanes']):
 match=re.search(r'^def reference_terminal\.'+name+r'\b[\s\S]*?(?=^/--|\Z)',raw,re.M);assert match,name
 decl=match[0].strip();body=decl.replace('def reference_terminal.'+name,'def sum_context11_'+name+' (sum_operation : SumOperation11)',1).replace('reference_terminal.sum_interval227','sum_operation')
 head=decl[:decl.index(':=')];head=head.replace('def reference_terminal.'+name,'theorem '+name+'_sum_caller11',1)
 # Return type becomes equality, while original parameters are copied verbatim.
 split=head.rfind(' :')
 # locate result-type colon following last argument group; signatures contain nested types.
 depth=0;boundary=None
 for i,c in enumerate(head):
  if c in '([{':depth+=1
  elif c in ')]}':depth-=1
  elif c==':'and depth==0:boundary=i;break
 assert boundary is not None
 params=head[:boundary]
 args='selectors'if name=='poseidon_selectors'else'public1 openings selectors'if name=='semantic_initial_and_absorption'else'packed openings selectors'
 s='import PV_B3P_SumOperation11227\nimport PV_B3P_P227_10\n'+h+'open Result\n'
 s+=body+'\n'
 s+='attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.mul Array.index_usize Array.update\n'
 s+=params+f''':
    reference_terminal.{name} {args} = sum_context11_{name} source_sum_interval11 {args} := by
  have h := congrArg (fun operation => sum_context11_{name} operation {args}) sum_operation_binding11
  exact h
#print axioms {name}_sum_caller11
end PV_B3P_Binding11227
'''
 files[f'PV_B3P_SumCaller11{number}227']=s
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
if '--check'not in sys.argv:(D/'resume11/sum-caller-modules.json').write_text(json.dumps(list(files),indent=2)+'\n')
