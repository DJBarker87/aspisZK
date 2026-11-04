from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,shutil,hashlib
B=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul4-20261029');C=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul4-cache-20261029')
assert C.is_dir() and (C/'NFA_exports_20261104').is_dir()
for rc in B.glob('NFA_*/receipt.json'):
 x=json.loads(rc.read_text());p=Path(x['cgroup'])/'cgroup.procs'
 assert not p.exists() or not p.read_text().split(),x['attempt']
removed=[]
for name in ['NFA_target','NFA_objects','NFA_tmp']:
 p=B/name
 if not p.exists():continue
 assert p.is_relative_to(B) and not p.is_symlink()
 size=sum(q.stat().st_size for q in p.rglob('*') if q.is_file())
 shutil.rmtree(p);removed.append(dict(path=str(p),bytes=size))
p=B/'NFA_native/NFA_Driver'
if p.is_file():
 h=hashlib.sha256(p.read_bytes()).hexdigest();size=p.stat().st_size;p.unlink();removed.append(dict(path=str(p),bytes=size,sha256=h))
# Shared UID/global temp files have no reliable ownership binding to this run.
# Keep every unattributed one; only the assigned NFA_tmp was removed above.
shared=[dict(path=str(p),bytes=p.stat().st_size) for pattern in ['external-sat*.cnf','smt2_dec_problem*'] for p in Path('/tmp').glob(pattern) if p.is_file()]
print(json.dumps(dict(removed=removed,own_cache_retained=str(C),unattributed_shared_solver_files_retained=shared,all_own_cgroups_terminal=True)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NFA_CLEANUP_TRANSPORT.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr)))
assert r.returncode==0,r.stderr
(E/'NFA_CLEANUP.json').write_text(r.stdout)
x=json.loads(r.stdout);print('removed',sum(i['bytes'] for i in x['removed']),'scratch bytes; cache retained; all scopes terminal')
