from pathlib import Path
import os,json,hashlib,shutil,subprocess
B=Path.cwd();C=B.parent/'codex-cx-slice-d-prepared-cache-20261104'
x=json.loads((B/'NIL_CACHE_VERIFICATION.json').read_text());assert x['status']=='PASS'
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit() or int(p.name)==os.getpid():continue
 try:
  cwd=(p/'cwd').resolve();cmd=(p/'cmdline').read_bytes().replace(bytes([0]),b' ').decode(errors='replace')
  if str(cwd).startswith(str(B)) and any(z in cmd for z in ['/bin/lean','cargo-kani','cbmc','charon','aeneas']):active.append(dict(pid=int(p.name),command=cmd))
 except (OSError,PermissionError):pass
assert not active,active
exports=json.loads((B/'NIL_EXPORT.json').read_text())['own_exports']
for r in exports:assert hashlib.sha256(Path(r['destination']).read_bytes()).hexdigest()==r['sha256']
paths=[B/'NIL_target',B/'NIL_objects',B/'NIL_tmp',C/'NIL_seed_20261107',C/'NIL_exports_20261107'];sizes=[]
for p in paths:
 if p.exists():sizes.append(dict(path=str(p),bytes=int(subprocess.check_output(['du','-sb','--',str(p)],text=True).split()[0])))
out=dict(status='PASS',active_own_formal_processes=active,retained=sizes,removed=[],all_own_caches_retained=True,verified_export_files=len(exports),disk_free_bytes=shutil.disk_usage(B).free,no_peer_worktree_access=True,no_key_or_chain_operations=True)
(B/'NIL_RETENTION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
