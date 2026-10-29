"""Freeze current successful sources only; one combined, axioms, focused audit."""
from pathlib import Path
import json,re,hashlib,subprocess
D=Path('evidence/pv-b3p6-20261028');O=D/'resume10';L=D/'lean';base='9e271d32e606772fffbddf687a4c5deae0eb9c80'
receipts=json.loads((O/'receipt-index.json').read_text());assert len(receipts)==97
latest={}
for r in receipts:
 if r['exit']==0:latest[r['module']]=r
accepted={};excluded=[]
new={p.stem:p for p in L.glob('*.lean')if not subprocess.run(['git','cat-file','-e',base+':'+str(p)],capture_output=True).returncode==0}
for m,p in new.items():
 raw=p.read_bytes();sha=hashlib.sha256(raw).hexdigest();r=latest.get(m)
 if r and r['source_sha256']==sha:accepted[m]=r
 else:excluded.append(dict(module=m,path=str(p),sha256=sha,status='excluded: rejected, superseded or unsubmitted draft',attempts=[dict(attempt=x['attempt'],exit=x['exit'])for x in receipts if x['module']==m]))
# Explicitly exclude abandoned raw-tail and tuple-continuation prototypes, even
# when smaller tails once compiled. Their successful support is redundant.
for m in list(accepted):
 if m.startswith('PV_B3P_ValueTail'):
  r=accepted.pop(m);excluded.append(dict(module=m,path=str(L/(m+'.lean')),sha256=r['source_sha256'],status='superseded raw-tail family; excluded from accepted audit',attempts=[dict(attempt=x['attempt'],exit=x['exit'])for x in receipts if x['module']==m]))
theorems=[]
for m in sorted(accepted):
 raw=(L/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',raw,re.M)[1]
 theorems += [ns+'.'+x for x in re.findall(r'^theorem (\S+)',raw,re.M)]
keys=['value_entry_factor10','add_value_read_binding10','accumulate_storage_binding10','accumulate_nine_cell_binding10','full_round_body_binding10','full_round_packed_body_binding10','full_round_m31_constants_body_binding10','full_round_m31_constants_packed_body_binding10']
keys=['PV_B3P_Binding10227.'+x for x in keys];assert set(keys)<=set(theorems)
imports='import PV_B3P_Resume9Combined\n'+''.join('import '+m+'\n'for m in sorted(accepted))
(L/'PV_B3P_Resume10Combined.lean').write_text(imports+'\n-- Transformation support only; V244 and runjoin op227 remain open.\n'+''.join('#check '+n+'\n#print axioms '+n+'\n'for n in keys))
(L/'PV_B3P_Resume10Axioms.lean').write_text('import PV_B3P_Resume10Combined\n'+''.join('#print axioms '+n+'\n'for n in sorted(set(theorems))))
(L/'PV_B3P_Resume10Focused.lean').write_text('import PV_B3P_Resume10Axioms\n-- One frozen focused manifest, no endpoint replay claim.\n'+''.join('#check '+n+'\n#print axioms '+n+'\n'for n in keys))
record=dict(base=base,accepted_normal_modules=sorted(accepted),new_theorems=sorted(set(theorems)),key_theorems=keys,audit_targets=['PV_B3P_Resume10Combined','PV_B3P_Resume10Axioms','PV_B3P_Resume10Focused'],audit_ids=[64097,64098,64099],sources=[dict(module=m,path=str(L/(m+'.lean')),sha256=r['source_sha256'])for m,r in sorted(accepted.items())],evidence_class='model/source-transformation support; not exhaustive native source binding or callback closure',semantic_use='reclassification within existing Charon/Aeneas tool trust',compiler_boundary='V370 / owner D381,D386 retained; own-1 does not require machine-code correspondence')
(O/'focused-manifest.json').write_text(json.dumps(record,indent=2)+'\n');(O/'unaccepted-candidates.json').write_text(json.dumps(excluded,indent=2)+'\n')
print(json.dumps(dict(accepted=len(accepted),theorems=len(theorems),excluded=len(excluded))))
