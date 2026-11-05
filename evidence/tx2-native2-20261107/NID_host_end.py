"""Read-only final own-workspace/cache inventory; never remove retained caches."""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-tx2-native2-20261107'
code=f'''from pathlib import Path
import os,json,hashlib,shutil,subprocess
b=Path({B!r});c=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104')
assert json.loads((b/'NID_CACHE_VERIFICATION.json').read_text())['status']=='PASS'
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:
  cwd=(p/'cwd').resolve();cmd=(p/'cmdline').read_bytes().replace(bytes([0]),b' ').decode(errors='replace')
  if str(cwd).startswith(str(b)) and any(x in cmd for x in ['lean','cargo','cbmc','charon','aeneas','S2W_run_host']):active.append(dict(pid=int(p.name),command=cmd))
 except (OSError,PermissionError):pass
assert not active,active
exports=json.loads((b/'NID_EXPORT.json').read_text())['own_exports']
for r in exports:assert hashlib.sha256(Path(r['destination']).read_bytes()).hexdigest()==r['sha256']
paths=[b/'NID_target',b/'NID_objects',b/'NID_tmp',c/'NID_seed_20261107',c/'NID_exports_20261107']
sizes=[]
for p in paths:
 if p.exists():sizes.append(dict(path=str(p),bytes=int(subprocess.check_output(['du','-sb','--',str(p)],text=True).split()[0])))
out=dict(active_own_formal_processes=active,retained=sizes,removed=[],all_own_caches_retained=True,verified_export_files=len(exports),disk_free_bytes=shutil.disk_usage(b).free,no_peer_worktree_access=True,no_key_or_chain_operations=True)
print(json.dumps(out))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
 (E/f'NID_END-{retry}.log').write_text(r.stdout+r.stderr)
 if r.returncode==0:
  out=json.loads(r.stdout);(E/'NID_HOST_END.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));break
 if r.returncode==255 and retry<10:time.sleep(60);continue
 raise RuntimeError('Final own inventory failed: '+r.stderr)
