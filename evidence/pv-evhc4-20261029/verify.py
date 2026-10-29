"""Read-only hash, first-root, failed-source, and ID audit. No compiler."""
from pathlib import Path
import hashlib,json,time,re,sys
B=Path('/home/dombarker/project-offloads/codex-pv-evhc-20261029'); E=B/'resume4'; E.mkdir(exist_ok=True)
P=B.parent/'codex-pv-evhc2-20261029'; R=P/'resume3'
sha=lambda p:hashlib.file_digest(Path(p).open('rb'),'sha256').hexdigest()
ready=json.load(open(E/'READY.json')); start=time.monotonic()
expected={'cohort_manifest_sha256':'f8ff7cfcc649f1b99a01b0703353d4856a472ac198884cb80b706863b9d07d65','authoritative_ndr_manifest_sha256':'cbd00ba461b8b8e683d15eaf460e1d317ddedf55b2b5e2309e4fcf2b6d035dd8','consumer_source_sha256':'2861d5b5b538dde3d821647a5175529b169b248386de6868be0bd05e74d314e4','first_root_preflight_sha256':'31e9cb1ed3ac4c9b2c5a89e1f5bda7dbd8d8a2092eea6a5d69a5e5bb13dbab4a'}
for k,v in expected.items():assert ready[k]==v,(k,'READY mismatch')
files={'cohort_manifest_sha256':Path(ready['cohort_manifest_path']),'authoritative_ndr_manifest_sha256':P/'NDR_FINAL_COHORT_PINS.json','consumer_source_sha256':B/'sources/PV_EVH_FixtureConsumer.lean','first_root_preflight_sha256':R/'first-root-preflight.json'}
for k,p in files.items():assert sha(p)==expected[k],(str(p),'hash mismatch')
roots=[P/'objects',B.parent/'codex-cx-reconcile-cache-20261028/objects',Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
assert ready['LEAN_PATH']==':'.join(map(str,roots))
manifest=json.load(open(files['cohort_manifest_sha256'])); pre=json.load(open(files['first_root_preflight_sha256']))
assert manifest['LEAN_PATH']==pre['LEAN_PATH']==ready['LEAN_PATH']
assert manifest['authoritative_manifest_sha256']==expected['authoritative_ndr_manifest_sha256']
assert manifest['first_root_preflight_sha256']==expected['first_root_preflight_sha256']
runner_pins={'reservation_agg16.py':'d6d40da5e7cad196b15974eb96526f28073d20b2c24855303d69bc605ebcac0f','S2W_lean_host_agg16.py':'9b325ab05e4aea7c8a2c3499ccef5de11898fdcba38cb803fc6a85111ca3f1dd','S2W_run_host_agg16.py':'8165ccff93f7d9b6043f55bf641c30c95c5af0f86d28b6e1b1ffef3aa5ea7ff6'}
for name,h in runner_pins.items():
 assert sha(B.parent/'codex-cx-fixture-cache-20261027'/name)==h,name
 assert sha(B/name)==h,name
for name,h in ready['normal_runners'].items():assert sha(P/name)==h,name
assert sha(P/'build3.py')==ready['launch_guard_sha256']
assert sha('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')==ready['summary']['lean_binary_sha256']
checked=0
for entry in manifest['entries']:
 m=entry['module']; top=m.split('.')[0]
 root=next(r for r in roots if (r/top).is_dir() or (r/(top+'.olean')).is_file())
 p=root/(m.replace('.','/')+'.olean')
 assert str(p)==entry['path'],(m,'first root changed',str(p))
 for f in [entry]+entry['companions']:
  q=Path(f['path']); assert q.is_file() and not q.is_symlink(),str(q)
  if q.is_relative_to(roots[0]):assert q.stat().st_nlink==1,('not plain copy',str(q))
  assert sha(q)==f['sha256'],('object mismatch',m,str(q))
  checked+=1
for m in ['PV_EVH_Deployed','PV_RJ4IDB_CallerLive','NDR_CombinedAudit']:assert any(e['module']==m for e in manifest['entries']),m
# Source-only guard across this line, including archived environment failures.
prior=[]
for job in B.parent.glob('codex-pv-evhc*-20261029'):
 for p in job.rglob('receipt.json'):
  v=json.load(open(p)); hs=v.get('source_hashes',{})
  if expected['consumer_source_sha256'] in hs.values():
   prior.append(dict(path=str(p),exit=v.get('exit_status'),source_hashes=hs))
   assert v.get('exit_status')==0,('failed consumer source; no retry',str(p))
assert not prior,('consumer already attempted',prior)
# Inventory receipt/output directories across jobs, excluding source/object trees.
used={}; pattern=re.compile(r'(?<![A-Za-z0-9])(707\d\d)(?![A-Za-z0-9])')
for job in B.parent.glob('*'):
 if not job.is_dir():continue
 candidates=list(job.glob('*'))
 for sub in ['evidence','receipts','resume3','resume4']:
  if (job/sub).is_dir():candidates+=list((job/sub).rglob('*'))
 for p in candidates:
  for a in pattern.findall(str(p.relative_to(job))):used.setdefault(a,[]).append(str(p))
sent=B.parent/'r1-privacy-build-integration-20261019/evidence/sent.txt'
if sent.exists():
 for l in sent.read_text().splitlines():
  for a in pattern.findall(l):used.setdefault(a,[]).append('sent.txt: '+l)
assert '70700' not in used,('ID collision',used.get('70700'))
result=dict(status='PASS',source_revision='5e9df8eb46b7ba32cde9b0eb430d93f5fc41fffd',LEAN_PATH=ready['LEAN_PATH'],pins=expected,runner_pins=runner_pins,modules=len(manifest['entries']),files_verified=checked,prior_consumer_receipts=prior,id_audit=used,next_id=70700,wall_seconds=time.monotonic()-start,verifier_sha256=sha(E/'verify.py'),print_axioms='N/A read-only preflight')
(E/'verified.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
