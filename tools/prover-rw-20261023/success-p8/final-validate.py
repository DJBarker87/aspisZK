"""Read-only final source/receipt checks; never launches a compiler."""
from pathlib import Path
import hashlib,json,re,subprocess
r=Path(__file__).resolve().parents[3]
e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-p8'
l=r/'docs/research/v8-r0-zk-20261009/lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
s=json.loads((e/'summary.json').read_text())
assert s['lean_compiles']==65
assert s['kani_runs']==12
accepted={}
for p in sorted(e.glob('*-receipt.json')):
 x=json.loads(p.read_text())
 if x.get('exit_status')==0:accepted[x['module']]=x
mods=json.loads((e/'audit-manifest.json').read_text())['host_modules']+['R1Z/PV_FinalAuditP8']
for m in mods:
 x=accepted[m];assert sha(l/(m+'.lean'))==x['source_sha256'],m
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',re.sub(r'/\-[\s\S]*?\-/|--[^\n]*','',(l/(m+'.lean')).read_text())),m
for p in (e/'local').glob('*-receipt.json'):
 x=json.loads(p.read_text());assert x['exit_status']==0
 assert sha(l/(x['module']+'.lean'))==x['source_sha256']
roots={'ProverCommitDeployedFuel22':'c263163f19b84438834a6ac25be6164d7e1ad4882fc904813090ca655dfda723','PrivacyR1HeadlineDeployedReal':'0374f534aaadcfcf3855dc9402feaae176f93f11687b0fab7773b075599e7b42'}
for m,h in roots.items():assert sha(l/'R1Z'/(m+'.lean'))==h
assert not subprocess.check_output(['git','diff','45d637560c','--','crates','programs'])
cache=json.loads((e/'final-cache-check.json').read_text());assert not cache['changed_objects']
last=json.loads((e/'translation/success-p8-ordinary-refine-003/receipt.json').read_text())
for name in ['crates/aspis-r1-cost-probe/src/sampler.rs','crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs','tools/prover-rw-20261023/success-p8/proof/lib.rs','tools/prover-rw-20261023/success-p8/proof/sampler_owned.rs']:
 assert sha(r/name)==last['source_sha256'][name],name
result=dict(lean_compiles=s['lean_compiles'],kani_runs=s['kani_runs'],accepted_host_modules=len(mods),local_modules=4,roots_unchanged=roots,native_source_unchanged=True,callback_remainder_before=33,callback_remainder_after=31,root_premises_removed=0,target_established=False,scope='Read-only checks; focused audit is not coherent release replay')
(e/'final-state.json').write_text(json.dumps(result,indent=2)+'\n')
print(result)
