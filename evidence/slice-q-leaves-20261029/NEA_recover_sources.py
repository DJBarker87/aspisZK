"""Recover exact source snapshots read-only; archive Rust references only as patches."""
from pathlib import Path
import subprocess,json,difflib,hashlib,time
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json
b=Path('/home/dombarker/project-offloads/codex-cx-slice-q-leaves-20261029');out={}
for a in b.glob('NEA_[LE][0-9][0-9][0-9]'):
 for p in (a/'sources').rglob('*'):
  if p.is_file() and p.suffix in ['.lean','.py','.rs']:
   out[str(p.relative_to(b))]=p.read_text()
removed=[]
for p in (b/'NEA_tmp').rglob('*'):
 if p.is_file() and (p.name.startswith('external-sat') or p.name.startswith('smt2_dec_problem')):removed.append(str(p));p.unlink()
print(json.dumps({'sources':out,'removed_own_solver_temps':removed}))
'''
for i in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3 -'],input=code,capture_output=True,text=True)
 if r.returncode!=255:break
 if i<10:time.sleep(60)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);manifest={}
for n,s in x['sources'].items():
 p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if p.suffix=='.rs':
  p=p.with_suffix('.patch');p.write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/'+Path(n).name)))
 else:p.write_text(s)
 manifest[n]={'sha256':hashlib.sha256(s.encode()).hexdigest(),'archive':str(p.relative_to(E))}
(E/'NEA_RECOVERED_SOURCES.json').write_text(json.dumps({'files':manifest,'removed_own_solver_temps':x['removed_own_solver_temps']},indent=2)+'\n')
print('Recovered',len(manifest),'snapshots')
