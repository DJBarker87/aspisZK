"""Freeze only current, successfully compiled sources for the three reserved audits."""
from pathlib import Path
import json,re,hashlib,subprocess
D=Path('evidence/pv-b3p6-20261028');O=D/'resume9';L=D/'lean';base='0c43174f5334a5b9b276071808bfd69f5e792a3c'
receipts=json.loads((O/'receipt-index.json').read_text());assert len(receipts)==97
accepted={r['module']:r for r in receipts if r['exit']==0};errors=[]
for m,r in accepted.items():
 raw=(L/(m+'.lean')).read_bytes()
 if hashlib.sha256(raw).hexdigest()!=r['source_sha256']:errors.append(dict(module=m,expected=r['source_sha256'],actual=hashlib.sha256(raw).hexdigest()))
assert not errors,errors
old=set(subprocess.check_output(['git','ls-tree','-r','--name-only',base,str(L)],text=True).splitlines())
new={p.stem:p for p in L.glob('*.lean')if str(p)not in old}
keys=['equality_body_binding','reconstruct_body_binding','sum_interval_binding','public_digest_read_binding9','value_sequence_read_binding9','matrix_cell_result']
keys += [f'accumulation_store9_{c}_{k}'for c in range(3)for k in range(3)]
keys=['PV_B3P_Binding9227.'+n for n in keys]
theorems=[]
for m,p in sorted(new.items()):
 if m not in accepted:continue
 raw=p.read_text();ns=re.search(r'^namespace (\S+)',raw,re.M)[1]
 theorems += [ns+'.'+n for n in re.findall(r'^theorem (\S+)',raw,re.M)]
assert set(keys)<=set(theorems)
imports='import PV_B3P_Resume8Combined\n'+''.join('import '+m+'\n'for m in sorted(accepted))
s=imports+'\n-- Accepted support only: no native op227 closure is inferred.\n'+''.join('#check '+n+'\n#print axioms '+n+'\n'for n in keys)
(L/'PV_B3P_Resume9Combined.lean').write_text(s)
s='import PV_B3P_Resume9Combined\n\n'+''.join('#print axioms '+n+'\n'for n in sorted(set(theorems)))
(L/'PV_B3P_Resume9Axioms.lean').write_text(s)
s='import PV_B3P_Resume9Axioms\n\n-- Exactly one frozen focused manifest; no endpoint replay claim.\n'+''.join('#check '+n+'\n#print axioms '+n+'\n'for n in keys)
(L/'PV_B3P_Resume9Focused.lean').write_text(s)
excluded=[]
for m,p in sorted(new.items()):
 if m in accepted or m.startswith('PV_B3P_Resume9'):continue
 attempts=[dict(attempt=r['attempt'],exit=r['exit'])for r in receipts if r['module']==m]
 excluded.append(dict(module=m,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),status='rejected or superseded; excluded'if attempts else'uncompiled draft/prototype; excluded',attempts=attempts))
manifest=dict(base=base,accepted_normal_modules=sorted(accepted),new_accepted_modules=sorted(set(new)&set(accepted)),new_theorems=sorted(set(theorems)),key_theorems=keys,audit_targets=['PV_B3P_Resume9Combined','PV_B3P_Resume9Axioms','PV_B3P_Resume9Focused'],audit_ids=[63197,63198,63199],evidence_class='focused model/source-transformation support; not V244 closure or endpoint replay',semantic_use='reclassification within existing Charon/Aeneas tool trust',compiler_boundary='V370 / pending owner D381,D386 retained; no machine-code correspondence required under own-1',sources=[dict(module=m,path=str(L/(m+'.lean')),sha256=r['source_sha256'])for m,r in sorted(accepted.items())])
for name,x in [('focused-manifest.json',manifest),('unaccepted-candidates.json',excluded),('current-source-check.json',dict(checked=len(accepted),mismatches=errors))]:(O/name).write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(normal_modules=len(accepted),new_modules=len(manifest['new_accepted_modules']),new_theorems=len(set(theorems)),excluded=len(excluded))))
