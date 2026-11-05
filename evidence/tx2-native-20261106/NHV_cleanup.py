"""Remove only owned rebuildable scratch after independently verified exports."""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-tx2-native-20261106';H='dombarker@100.108.41.90'
code=f'''from pathlib import Path
import os,json,shutil,hashlib
b=Path({B!r});assert json.loads((b/'NHV_CACHE_VERIFICATION.json').read_text())['status']=='PASS'
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:
  cwd=(p/'cwd').resolve();cmd=(p/'cmdline').read_bytes().replace(bytes([0]),b' ').decode(errors='replace')
  if (cwd==b or str(cwd).startswith(str(b)+'/')) and any(n in cmd for n in ['cargo','cbmc','lean','NHV_gate','S2W_run_host']):active.append(dict(pid=p.name,command=cmd))
 except (OSError,PermissionError):pass
assert not active,active
exports=json.loads((b/'NHV_EXPORT.json').read_text())['own_exports']
for r in exports:assert hashlib.sha256(Path(r['destination']).read_bytes()).hexdigest()==r['sha256']
removed=[]
for name in ['NHV_target','NHV_tmp','NHV_objects','NHV_native']:
 p=b/name
 if not p.exists():continue
 size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file());shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
for p in sorted(b.rglob('__pycache__'),reverse=True):
 if p.is_dir():shutil.rmtree(p)
peers=[]
p=b.parent/'codex-cx-extract-stage-20261106'
for n in ['NHR_stage.py','NHR_STAGING_MANIFEST.json','NHR_FROZEN_PAYLOAD.json.xz']:
 q=p/n;peers.append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
shared_tmp=[dict(path=str(p),bytes=p.stat().st_size,mtime=p.stat().st_mtime) for pattern in ['external-sat*.cnf','smt2_dec_problem*'] for p in Path('/tmp').glob(pattern) if p.is_file()]
out=dict(active_formal_processes=active,removed=removed,retained_exports=len(exports),retained_cache='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NHV_exports_20261106',disk_free_bytes=shutil.disk_usage(b).free,shared_tmp_unattributed_preserved=shared_tmp,peer_source_pins_read_only=peers)
(b/'NHV_HOST_END.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
 (E/f'NHV_CLEANUP-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:
  (E/'NHV_HOST_END.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n');break
 if r.returncode==255 and retry<10:time.sleep(60);continue
 raise RuntimeError('Owned cleanup failed; do not touch peers: '+r.stdout+r.stderr)
