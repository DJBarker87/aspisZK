"""Retain checked outputs, remove ONLY own rebuildable build scratch."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code=r'''
from pathlib import Path
import hashlib,json,shutil,os,time
B=Path('/home/dombarker/project-offloads/codex-cx-verify-observed-20261105')
D=Path('/home/dombarker/project-offloads/codex-cx-prepared-claim-cache-20261104/NGX_seed_20261105/NGX_exports_20261105')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert json.loads((B/'NGX_L070/receipt.json').read_text())['exit_status']==0
assert json.loads((B/'NGX_L066/receipt.json').read_text())['exit_status']==0
before=shutil.disk_usage(B).free;copied=[];removed=[]
source=B/'NGX_native';dest=D/'NGX_native';dest.mkdir(exist_ok=True)
for p in source.rglob('*'):
 if not p.is_file():continue
 q=dest/p.relative_to(source);q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(p)==sha(q)
 else:shutil.copy2(p,q)
 copied.append(dict(source=str(p),retained=str(q),sha256=sha(q),bytes=q.stat().st_size))
for name in ['NGX_Driver','NGX_ProofDriver']:
 expected=PINS[name]['sha256']
 assert sha(dest/name)==expected
for name in ['NGX_target','NGX_extract_target','NGX_tmp']:
 p=B/name
 if p.exists():
  assert p.parent==B and not p.is_symlink()
  shutil.rmtree(p);removed.append(str(p))
for name,target in [('NGX_native',dest),('NGX_objects',D)]:
 p=B/name
 if p.is_symlink():assert p.resolve()==target.resolve()
 else:
  assert p.is_dir()and p.parent==B
  shutil.rmtree(p);p.symlink_to(target,target_is_directory=True);removed.append(str(p)+' (replaced by retained-cache alias)')
report=dict(status='PASS',terminal_receipts=['NGX_L070','NGX_L066'],copied_native=copied,removed_rebuildable_only=removed,retained_cache=str(D),retained_cache_never_deleted=True,free_before=before,free_after=shutil.disk_usage(B).free,keys_created_or_removed=False)
(B/'NGX_CLEANUP.json').write_text(json.dumps(report,indent=1));print(json.dumps(report))
'''
code='PINS='+repr({n:json.loads((E/'NGX_L065'/(n+'_BINARY_PIN.json')).read_text())for n in ['NGX_Driver','NGX_ProofDriver']})+'\n'+code
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NGX_CLEANUP_TRANSPORT.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr),indent=1))
assert r.returncode==0,r.stderr
report=json.loads(r.stdout);(E/'NGX_CLEANUP.json').write_text(json.dumps(report,indent=1));print(json.dumps({k:v for k,v in report.items()if k!='copied_native'}))
