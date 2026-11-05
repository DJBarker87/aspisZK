from pathlib import Path
import json,hashlib,subprocess,re
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-finish2-20261105';M=E.parent/'slice-d-finish-20261105'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputs={}
def pin(p):
 inputs[str(p.relative_to(E.parent.parent))]=dict(sha256=sha(p),bytes=p.stat().st_size)
def gate(base,name,good):
 p=base/name;r=json.loads((p/'receipt.json').read_text());assert r['exit_status']==(0 if good else 1),(name,r['exit_status'])
 out=(p/'stdout.log').read_text();assert ('VERIFICATION:- SUCCESSFUL' if good else 'VERIFICATION:- FAILED')in out
 if not good:assert 'Failed Checks: assertion failed:'in out
 g=json.loads((base/(name+'-graph-check.json')).read_text());assert g['graph_matches_frozen']is True and not g['new_package_tuples']and not g['edge_errors']
 lock=json.loads((base/(name+'-lock-check.json')).read_text());assert lock['unchanged']and lock['before']==lock['after']==g['lock_sha256']
 assert r['env']['CARGO_NET_OFFLINE']=='true'
 for n in ['receipt.json','stdout.log']:pin(p/n)
 for n in ['-graph-check.json','-lock-check.json']:pin(base/(name+n))
 return dict(attempt=name,receipt=str((p/'receipt.json').relative_to(E.parent.parent)),exit=r['exit_status'],module=r['module'],lock_sha256=lock['before'])
pairs=[]
for i in range(88,98,2):pairs.append([gate(M,f'NGM_K{i:03d}',True),gate(M,f'NGM_K{i+1:03d}',False)])
pairs.append([gate(M,'NGM_K100',True),gate(P,'NGW_K034',False)])
for base,names in [(M,['NGM_NATIVE_INPUTS.json','NGM_helper_erasure.py','NGM_HELPER_ERASURE.json','NGM_helper_reference.rs.txt','NGM_E003/receipt.json']), (P,['NGW_POLYNOMIAL_IMPORTS.json','NGW_HelperRef/Funs.lean','NGW_HelperRef/Types.lean','NGW_E001/receipt.json','NGW_helper_reference.rs.txt','NGW_PolynomialAdd.lean','NGW_Horner.lean','NGW_CurrentAddPort.lean','NGW_SCAN_RECONCILIATION.json'])]:
 for n in names:pin(base/n)
patch=E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch';pin(patch)
frozen=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-r1-cost-probe/src/verifier.rs'],text=True)
a=frozen.index('fn polynomial(');b=frozen.index('{',a);depth=1;c=b+1
while depth:depth+=(frozen[c]=='{')-(frozen[c]=='}');c+=1
source=frozen[a:c];(E/'NHE_frozen_polynomial.rs.txt').write_text(source+'\n');pin(E/'NHE_frozen_polynomial.rs.txt')
norm=lambda s:re.sub(r'\s+','',s)
assert '(0..7).rev().fold(E::ZERO,|a,i|a.mul(x).add(field(bytes,i)))'in norm(source)
assert json.loads((M/'NGM_HELPER_ERASURE.json').read_text())['frozen_revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
(E/'NHE_INPUT_INDEX.json').write_text(json.dumps(inputs,indent=2)+'\n')
(E/'NHE_POLYNOMIAL_VALIDATION.json').write_text(json.dumps(dict(status='PASS retained native evidence and exact source-fold shape',new_kani_runs=0,pairs=pairs,kmx_patch_sha256=sha(patch),extraction_failure='NGM_E003; retained, no rerun',replacement='NGW_E001 extracted cell add reference + NHE_HornerPort.go induction under ruling ah',source_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',no_success_premise=True,domain='canonical x; arbitrary immutable byte slice; every failure and divergence retained; indices 6..0 each below 64'),indent=2)+'\n')
print('PASS',len(pairs),'retained native pairs')
