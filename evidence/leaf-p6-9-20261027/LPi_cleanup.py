"""Remove only this terminated job's rebuildable private caches; retain all sources."""
from pathlib import Path
import subprocess,shlex,json
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-leaf-p6-9-20261027'
script='''from pathlib import Path
import hashlib,json,shutil,subprocess
b=Path(BASE)
objects={str(p.relative_to(b)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in (b/'LPi_objects').rglob('*.olean')}
removed={}
for name in ['LPi_objects','LPi_target']:
 p=b/name
 assert not p.is_symlink()
 assert p.parent==b
 if p.exists():
  removed[name]=sum(q.stat().st_size for q in p.rglob('*') if q.is_file())
  shutil.rmtree(p)
tmp=b/'LPi_tmp'
solver=[]
if tmp.exists():
 for p in tmp.rglob('*'):
  if p.is_file() and (p.name.startswith('external-sat') or p.name.startswith('smt2_dec_problem')):
   solver.append({'name':str(p.relative_to(tmp)),'bytes':p.stat().st_size});p.unlink()
processes=subprocess.check_output(['ps','-eo','pid,args'],text=True).splitlines()
# Compiler/solver command paths point into this job; ignore the collecting Python/ssh shell itself.
live=[x for x in processes if str(b) in x and any(t in x for t in ['cargo-kani kani','kani-driver','/bin/cbmc','lean -j1']) and 'python3 -c' not in x and '/bin/sh -c' not in x]
print(json.dumps({'private_objects':objects,'removed_cache_logical_bytes':removed,'removed_own_solver_files':solver,'remaining_own_prover_commands':live,'sources_and_shared_cache_retained':True}))
'''.replace('BASE',repr(B))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],capture_output=True,text=True,check=True)
data=json.loads(r.stdout);(E/'LPi_cleanup.json').write_text(json.dumps(data,indent=2)+'\n')
print('Removed private cache bytes',sum(data['removed_cache_logical_bytes'].values()),'live prover commands',data['remaining_own_prover_commands'])
assert not data['remaining_own_prover_commands']
