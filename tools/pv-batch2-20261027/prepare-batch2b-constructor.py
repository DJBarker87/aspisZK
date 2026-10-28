"""Restore the discarded private constructor environment; split only fixed rows.
No shared env-J source is touched. --check validates byte-exact generated outputs.
The aggregate scopes each original component separately; generated Aeneas
options stay in their original component, while new proof declarations use defaults.
"""
from pathlib import Path
import hashlib,json,re,sys
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
E=Path('evidence/pv-batch2-20261027/batch2b')
seen=set();ordered=[];external=set()
def visit(name):
 if name in seen:return
 seen.add(name);p=L/(name+'.lean');s=p.read_text()
 for imp in re.findall(r'^import (\S+)',s,re.M):
  if imp.startswith('R1Z.PV_B2_'):visit(imp[4:])
  else:external.add(imp)
 ordered.append((p,s))
visit('PV_B2_WeightsTotal')
body=[];pins=[]
for p,s in ordered:
 pins.append(dict(path=str(p),sha256=hashlib.sha256(s.encode()).hexdigest()))
 s=re.sub(r'^import .*\n','',s,flags=re.M)
 body.append('-- Component: '+p.name+'\nsection\n'+s+'\n'+('end\n'*len(re.findall(r'^noncomputable section$',s,re.M)))+'end\n')
output='-- Restored private environment after the prior recorded cache cleanup.\n'+''.join('import '+x+'\n' for x in sorted(external))+'\n'+'\n'.join(body)
outputs={L/'PV_B2_ConstructorEnvironment.lean':output}
# Retain the exact emitted per-row monadic code, including every restoration.
source=(L/'PV_B2_W_22_host_weights_Weights_new.lean').read_text()
code=source.split('  := do\n',1)[1].split('\n\n\n#print axioms',1)[0]
starts=['  let a2 ←','  let a18 ←','  let a34 ←','  let scp ←','  let scp1 ←']
ends=['  let a18 ←','  let a34 ←','  let scp ←','  let scp1 ←','  let factors25 :=']
for i,(start,end) in enumerate(zip(starts,ends)):
 fragment=code[code.index(start):code.index(end)]
 if i:
  prev=i*5;prev_a=17 if i==1 else 33 if i==2 else 49 if i==3 else 59
  fragment=fragment.replace(f'  let factors{prev} := index_mut_back{prev-1} a{prev_a}\n','')
  fragment=re.sub(r'\bfactors'+str(prev)+r'\b','factors',fragment)
 last_back=5*i+4;last_a=[17,33,49,59,69][i]
 fragment+=f'  ok (index_mut_back{last_back} a{last_a})\n'
 params='(factors : Factors) (points : Points)' if i<3 else '(factors : Factors) (z : Array Point 2#usize)'
 prev='PV_B2_ConstructorEnvironment' if i==0 else f'PV_B2_ConstructorRow{i-1}'
 head='''set_option autoImplicit false
noncomputable section
namespace PV_B2_ConstructorRows
open Aeneas Aeneas.Std Result PV_B2_ArrayTotal PV_B2_WeightsNative
'''
 if i==0:head+='''abbrev K := ProverRwFull.aspis_core.field.QM31
abbrev Point := ProverRwFull.aspis_core.circle.SecureCirclePoint
abbrev Factors := Array (Array (Array K 4#usize) 5#usize) 5#usize
abbrev Points := Array (Array K 10#usize) 3#usize
'''
 text=f'import R1Z.{prev}\n'+head+f'\n/-- Exact fixed factor row {i}; all array restorations are retained. -/\ndef row{i} {params} : Result Factors := do\n'+fragment
 text+=f'''\ntheorem row{i}_total {params} : Total (row{i} factors {'points' if i<3 else 'z'}) := by
  unfold row{i}
  simp only [PV_B2_FieldTotal.QM31_mul,PV_B2_FieldTotal.QM31_add,
    PV_B2_FieldTotal.QM31_sub,bind_tc_ok]
  repeat' first
    | exact ⟨_,rfl⟩
    | exact read _ _ (by decide)
    | exact write _ _ _ (by decide)
    | exact borrow _ _ (by decide)
    | exact PV_B2_WeightsTotal.double _
    | apply PV_B2_ArrayTotal.bind
    | (intro x; cases x)
#print axioms row{i}_total
end PV_B2_ConstructorRows
'''
 outputs[L/f'PV_B2_ConstructorRow{i}.lean']=text
manifest=dict(components=pins,external_imports=sorted(external),row_count=5,whole_constructor_reduction=False,scope='private constructor environment and per-row generic totality; no source/copy/ledger closure claim',outputs={str(p):hashlib.sha256(s.encode()).hexdigest() for p,s in outputs.items()})
for p,s in outputs.items():
 if '--check' in sys.argv:assert p.read_text()==s,p
 else:p.write_text(s)
p=E/'CONSTRUCTOR-PREFLIGHT.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==manifest
else:p.write_text(json.dumps(manifest,indent=2)+'\n')
print('checked' if '--check' in sys.argv else 'prepared',len(outputs),'private modules')
