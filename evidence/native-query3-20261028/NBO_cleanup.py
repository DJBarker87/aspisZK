from NBO_host import *
import fcntl
with (E/'NBO_SERIAL.lock').open('a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 r=py(f'''from pathlib import Path
import json,shutil,hashlib,subprocess
b=Path({B!r});target=b/'NBO_target';tmp=b/'NBO_tmp';removed=[]
assert target.name=='NBO_target' and target.parent==b and not target.is_symlink()
if target.exists():
 files=[p for p in target.rglob('*') if p.is_file()]
 removed.append(dict(path=str(target),files=len(files),bytes=sum(p.stat().st_size for p in files)))
 shutil.rmtree(target)
solvers=[]
for p in tmp.rglob('*'):
 if p.is_file() and ((p.name.startswith('external-sat') and p.suffix=='.cnf') or p.name.startswith('smt2_dec_problem')):
  solvers.append(dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()));p.unlink()
cache=Path('/home/dombarker/project-offloads/codex-cx-query-cache-20261028');assert cache.is_dir()
print(json.dumps(dict(removed=removed,solver_files=solvers,cache_retained=str(cache),scratch_source_retained=str(b/'NBO_src'),no_keys_touched=True,target_absent=not target.exists())))
''')
 assert r.returncode==0,r.stderr
 (E/'NBO_CLEANUP.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
 print(r.stdout[:1500])
