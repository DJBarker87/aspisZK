"""Audit only current successful exact source snapshots from this round."""
from pathlib import Path
import json,re,hashlib,subprocess
D=Path('evidence/pv-b3p6-20261028');O=D/'resume13';L=D/'lean'
base='7eab3fb68fe64bacff8e32d371126f5aa75cd865'
rows=json.loads((O/'receipt-index.json').read_text());assert len(rows)==97
latest={}
for r in rows:
 if r['exit']==0:latest[r['module']]=r
accepted={};excluded=[]
for m,r in latest.items():
 p=L/(m+'.lean');sha=hashlib.sha256(p.read_bytes()).hexdigest()
 if sha==r['source_sha256']:accepted[m]=r
 else:excluded.append(dict(module=m,status='superseded current source differs',attempt=r['attempt']))
for p in L.glob('*.lean'):
 if p.stem in accepted:continue
 if subprocess.run(['git','cat-file','-e',base+':'+str(p)],capture_output=True).returncode:
  excluded.append(dict(module=p.stem,status='unsubmitted, rejected or superseded draft; no credit',attempts=[dict(attempt=r['attempt'],exit=r['exit'])for r in rows if r['module']==p.stem]))
theorems=[]
for m in sorted(accepted):
 raw=(L/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',raw,re.M)
 assert ns,m
 theorems += [ns[1]+'.'+n for n in re.findall(r'^theorem (\S+)',raw,re.M)]
assert len(set(theorems))==len(theorems)
keys=['PV_B3P_Binding13227.'+n for n in [
 'selected_callback13','selected_scalar_callback13','scalar_links_satisfiable13',
 'prepared_link13','reconstruct_cleanup_binding13','projected_link13','iter_mut_restoration13',
 'slice_loop_plan13','slice_four_literal13','frozen_mask_adapter_link13','sum_high_link13',
 'fields_rejected_suffix_keeps_prefix13']]+[
 'PV_B3P_Groups13227.selected_from_function_links13',
 'PV_B3P_Groups13227.function_group_joint_witness13',
 'PV_B3P_Groups13227.changed_bodies_satisfiable13',
 'PV_B3P_ScalarBinding13227.semantic_source_binding13']
accepted_keys=[k for k in keys if k in theorems]
imports='import PV_B3P_Resume12Combined\n'+''.join('import '+m+'\n'for m in sorted(accepted))
(L/'PV_B3P_Resume13Combined.lean').write_text(imports+'\n-- Model transformation support; no op227 discharge claim.\n'+''.join('#check '+k+'\n#print axioms '+k+'\n'for k in accepted_keys))
(L/'PV_B3P_Resume13Axioms.lean').write_text('import PV_B3P_Resume13Combined\n'+''.join('#print axioms '+k+'\n'for k in sorted(theorems)))
(L/'PV_B3P_Resume13Focused.lean').write_text('import PV_B3P_Resume13Axioms\n-- One final frozen focused manifest.\n'+''.join('#check '+k+'\n#print axioms '+k+'\n'for k in accepted_keys))
x=dict(base=base,accepted_normal_modules=sorted(accepted),new_theorems=sorted(theorems),key_theorems=accepted_keys,unaccepted_key_theorems=sorted(set(keys)-set(accepted_keys)),audit_targets=['PV_B3P_Resume13Combined','PV_B3P_Resume13Axioms','PV_B3P_Resume13Focused'],audit_ids=[66697,66698,66699],sources=[dict(module=m,path=str(L/(m+'.lean')),sha256=r['source_sha256'])for m,r in sorted(accepted.items())],evidence_class='local model and transformation laws; not a complete own-1 association or callback closure',semantic_use='reclassification within existing Charon/Aeneas tool trust',compiler_boundary='V370 / pending owner D381,D386 retained')
(O/'focused-manifest.json').write_text(json.dumps(x,indent=2)+'\n')
(O/'unaccepted-candidates.json').write_text(json.dumps(excluded,indent=2)+'\n')
print(json.dumps(dict(accepted_modules=len(accepted),theorems=len(theorems),excluded=len(excluded),key_theorems=accepted_keys)))
