"""Retain own checked objects and audit binary, then remove rebuildable job scratch."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
assert json.loads((E/'NGH_RESUME_AUDIT_COMPLETE.json').read_text())['status']=='PASS'
code=r'''
from pathlib import Path
import hashlib,shutil,json
b=Path('/home/dombarker/project-offloads/codex-cx-slice-d-field3-20261105')
c=Path('/home/dombarker/project-offloads/codex-cx-slice-d-field3-cache-20261104')
d=c/'NGH_exports_20261105';d.mkdir(exist_ok=True)
rows=[]
for p in (b/'NGH_objects').rglob('*'):
 if not p.is_file():continue
 q=d/p.relative_to(b/'NGH_objects');q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
 assert p.read_bytes()==q.read_bytes()
 rows.append(dict(path=str(q),source=str(p),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
p=b/'NGH_native/NGH_Driver';q=c/'NGH_native_20261105/NGH_Driver';q.parent.mkdir(exist_ok=True);shutil.copy2(p,q)
rows.append(dict(path=str(q),source=str(p),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
removed=[]
for name in ['NGH_target','NGH_objects','NGH_native','NGH_tmp']:
 p=b/name
 if p.exists():shutil.rmtree(p);removed.append(str(p))
out=dict(status='PASS',cache=str(c),exports=str(d),files=rows,removed_rebuildable_job_scratch=removed,cache_deleted=False,cache_bytes=sum(p.stat().st_size for p in c.rglob('*')if p.is_file()),source_workspace=str(b),replay='Prepend NGH_exports_20261105 to the ordered LEAN_PATH from NGH_L025.json; all fallback inputs remain read-only and pinned there.')
(b/'NGH_CACHE_END.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,'Transport/cleanup failure: inspect, do not blindly repeat destructive step'
x=json.loads(r.stdout);(E/'NGH_CACHE_END.json').write_text(json.dumps(x,indent=1)+'\n')
print(json.dumps(dict(status=x['status'],retained_files=len(x['files']),cache_bytes=x['cache_bytes'],cache_deleted=False)))
