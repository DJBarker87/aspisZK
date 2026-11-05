"""Verify retained own exports, then remove only owned rebuildable scratch."""
from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,hashlib,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-ledger12-20261107')
x=json.loads((b/'NIR_EXPORT.json').read_text())
for row in x['files']:assert hashlib.sha256(Path(row['path']).read_bytes()).hexdigest()==row['sha256']
removed=[]
for name in ['NIR_native','NIR_objects','NIR_tmp']:
 p=b/name
 if p.exists():
  rows=[dict(path=str(q),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest())for q in p.rglob('*')if q.is_file()]
  if name=='NIR_objects':
   for q in p.rglob('*'):
    if q.is_file():
     dest=Path(x['export'])/q.relative_to(p);assert dest.is_file()and hashlib.sha256(dest.read_bytes()).hexdigest()==hashlib.sha256(q.read_bytes()).hexdigest()
  removed+=rows;shutil.rmtree(p)
y=dict(status='PASS',export=x['export'],cache_retained=True,removed_files=len(removed),removed_bytes=sum(r['bytes']for r in removed),files=removed,disk_free=shutil.disk_usage(b).free)
(b/'NIR_HOST_END.json').write_text(json.dumps(y,indent=1)+'\\n');print(json.dumps(y))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 if r.returncode==0:break
 if r.returncode==255:
  # Mutation was submitted: do not resubmit; recover read-only on the next link.
  time.sleep(60)
  r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat /home/dombarker/project-offloads/codex-cx-ledger12-20261107/NIR_HOST_END.json'],text=True,capture_output=True)
  if r.returncode==0:break
  raise RuntimeError('Cleanup submission transport lost; recovery unresolved; never resubmit')
 raise RuntimeError(r.stderr)
x=json.loads(r.stdout);(E/'NIR_HOST_END.json').write_text(json.dumps(x,indent=1)+'\n');print('NIR own scratch removed after verified export; cache retained')
