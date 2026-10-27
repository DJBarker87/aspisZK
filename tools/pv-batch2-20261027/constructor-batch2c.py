"""Port retained fixed-row proofs to exact raw extracted carriers, reproducibly.
No shared module is copied or substituted. No statement claims native transport.
"""
from pathlib import Path
import sys,json,hashlib,re
from named_discriminants import qualify
L=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');B=Path('evidence/pv-batch2-20261027/batch2b/drafts');E=B.parent.parent/'batch2c'
s=(B/'PV_B2_ConstructorEnvironment.lean.txt').read_text().replace('import R1Z.ProverRwFullTypes\n','')
p=Path('evidence/pv-batch2-20261027/extraction-weights/generated-252/Types.lean');t=p.read_text().replace('import Aeneas\n','').replace('PV_B2_252','PV_B2_C_Carrier')
s=s.replace('import Aeneas\n','import Aeneas\nsection\n'+t+'\nend\n',1).replace('ProverRwFull.','PV_B2_C_Carrier.')
for n in ['WeightsNative','FieldValue','FieldTotal','ArrayTotal','WeightsTotal']:s=s.replace('PV_B2_'+n,'PV_B2_C_'+n)
outputs={L/'PV_B2_C_ConstructorEnvironment.lean':qualify(s)}
for i in range(5):
 s=(B/f'PV_B2_ConstructorRow{i}.lean.txt').read_text()
 for n in ['ConstructorEnvironment','ConstructorRow','ConstructorRows','WeightsNative','FieldValue','FieldTotal','ArrayTotal','WeightsTotal']:s=s.replace('PV_B2_'+n,'PV_B2_C_'+n)
 s=s.replace('ProverRwFull.','PV_B2_C_Carrier.')
 if i>=3:
  a=s.index(' := by\n',s.index(f'theorem row{i}_total'))+len(' := by\n');b=s.index(f'#print axioms row{i}_total',a)
  body=s.split(' : Result Factors := do\n',1)[1].split(f'\ntheorem row{i}_total',1)[0]
  steps=[f'  unfold row{i}']
  for m in re.finditer(r'^  let (.*?) ←\s*\n?\s*(.*)',body,re.M):
   name,term=m.groups()
   if term.startswith('Array.index_usize'):leaf='read _ _ (by decide)'
   elif term.startswith('Array.index_mut_usize'):leaf='borrow _ _ (by decide)'
   elif term.startswith('Array.update'):leaf='write _ _ _ (by decide)'
   elif term.startswith('host_weights.double'):leaf='PV_B2_C_WeightsTotal.double _'
   elif term.startswith('aspis_core.field.QM31.mul'):leaf='⟨_,PV_B2_C_FieldTotal.QM31_mul _ _⟩'
   else:raise Exception(term)
   steps.append('  apply PV_B2_C_ArrayTotal.bind _ _ ('+leaf+')')
   steps.append(('  rintro ⟨'+name[1:-1]+'⟩') if name.startswith('(') else '  intro '+('unused' if name=='_' else name))
  steps.append('  exact ⟨_,rfl⟩')
  s=s[:a]+'\n'.join(steps)+'\n'+s[b:]
 outputs[L/f'PV_B2_C_ConstructorRow{i}.lean']=s
for p,s in outputs.items():
 if '--check' in sys.argv:assert p.read_text()==s,p
 else:p.write_text(s)
j=dict(scope='raw-carrier generic totality; no native/original/copy/row bridge claim',outputs={str(p):hashlib.sha256(s.encode()).hexdigest() for p,s in outputs.items()})
p=E/'CONSTRUCTOR-PREFLIGHT.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==j
else:p.write_text(json.dumps(j,indent=2)+'\n')
