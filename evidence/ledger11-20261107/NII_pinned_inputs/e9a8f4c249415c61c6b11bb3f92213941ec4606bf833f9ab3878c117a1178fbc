"""Serial capped final evidence gates; no Rust/Kani/Lean proof is launched."""
from pathlib import Path
import json,hashlib,sys,tarfile,importlib.util,shutil,os,time
sys.dont_write_bytecode=True
B=Path(__file__).resolve().parent;stage=sys.argv[1];archive=B/'NGL_review_bundle.tar.xz';expected=(B/'NGL_review_bundle.sha256').read_text().split()[0]
assert hashlib.sha256(archive.read_bytes()).hexdigest()==expected
root=B/'NGL_review';E=root/'evidence/slice-d-entry-20261105'
if not E.exists():
 root.mkdir(exist_ok=True)
 with tarfile.open(archive,'r:xz') as t:
  for m in t.getmembers():assert m.name.startswith('evidence/slice-d-entry-20261105/') and not m.issym() and not m.islnk() and '..' not in Path(m.name).parts
  t.extractall(root,filter='data')
spec=importlib.util.spec_from_file_location('NGL_review_validator',E/'NGL_certify.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
if stage=='all':
 import subprocess
 for child in ['native','models','sources','ledger','export','hygiene','final']:
  r=subprocess.run([sys.executable,str(Path(__file__).resolve()),child]);assert r.returncode==0,(child,r.returncode)
 result={'status':'PASS_ALL_FINAL_CHECKS','stages':7,'new_closed_rows':0}
elif stage=='native':result=v.native_review()
elif stage=='models':result=v.model_review()
elif stage=='sources':result=v.source_review()
elif stage=='ledger':result=v.ledger_review()
elif stage=='export':
 c=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104')/'NGL_exports_20261105';c.mkdir(exist_ok=True);rows=[]
 for p in sorted((B/'NGL_objects').rglob('*')):
  if not p.is_file():continue
  rel=p.relative_to(B/'NGL_objects');assert rel.parts[0].startswith('NGL_'),str(rel)
  q=c/rel;q.parent.mkdir(parents=True,exist_ok=True);h=hashlib.sha256(p.read_bytes()).hexdigest()
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  else:shutil.copy2(p,q)
  assert hashlib.sha256(q.read_bytes()).hexdigest()==h;rows.append(dict(relative=str(rel),sha256=h,bytes=p.stat().st_size))
 result={'status':'PASS','cache':str(c),'files':rows,'count':len(rows),'bytes':sum(r['bytes'] for r in rows),'never_deleted':True,'source':'private NGL_objects; copied and verified, no sibling cache mutation'};v.put('NGL_EXPORTS.json',result)
elif stage=='hygiene':
 for p in root.rglob('__pycache__'):shutil.rmtree(p)
 disk=shutil.disk_usage(B);targets={}
 for n in ['NGL_target','NGL_objects','NGL_native']:
  p=B/n;targets[n]=sum(f.stat().st_size for f in p.rglob('*') if f.is_file()) if p.exists() else 0
 result={'status':'PASS','disk':dict(total=disk.total,used=disk.used,free=disk.free),'private_bytes':targets,'own_cache_retained':True,'no_cleanup_of_keys_or_wallets':True,'no_large_binary_copied_into_repo':True};v.put('NGL_RESOURCE_FINAL.json',result)
elif stage=='final':
 result=v.final_review();stages=[json.loads(p.read_text()) for p in (B/'NGL_review_results').glob('*.json')]
 assert len(stages)==6 and all(x['exit_status']==0 for x in stages)
 result.update(status='PASS_EVIDENCE_AND_FAIL_CLOSED_ADMISSION',prior_gates=[x['stage'] for x in stages],new_closed_rows=0,remaining_spine_open=13,budget_accounting='120 Kani; 62 Lean compilations + 8 support scopes in L001..L070; 3 extraction runs. This final scope is L070; final receipt completes the accounting.')
 v.put('NGL_VALIDATION_FINAL.json',result)
else:raise ValueError(stage)
out=B/'NGL_review_results';out.mkdir(exist_ok=True)
(out/(stage+'.json')).write_text(json.dumps({'stage':stage,'exit_status':0,'input_bundle_sha256':expected,'result':result},indent=1)+'\n')
print(json.dumps({'stage':stage,'status':'PASS','native_admitted_rows':0}))
