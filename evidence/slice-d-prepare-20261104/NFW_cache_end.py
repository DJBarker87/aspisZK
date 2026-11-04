"""Export this job's compiled modules to its retained cache, then remove only
its rebuildable build outputs. Run once, after all submitted scopes terminate.
No keys or shared paths are deleted. Inputs and receipts remain retained.
"""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
host='dombarker@100.108.41.90'
code='''from pathlib import Path
import hashlib,json,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepare-20261104')
c=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepare-cache-20261104')/'NFW_exports_20261104'
c.mkdir(exist_ok=True)
allowed=set()
for receipt in b.glob('NFW_L???/receipt.json'):
 r=json.loads(receipt.read_text())
 if r['exit_status']==0 and r['kind'] in ['lean','dependency']:
  allowed.add(r['module'])
rows=[]
for p in sorted((b/'NFW_objects').rglob('*')):
 if p.is_file() and p.name.split('.')[0] in allowed:
  assert p.name.startswith(('NFW_','KMX_CopyMeaning')),str(p)
  q=c/p.relative_to(b/'NFW_objects');q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  digest=lambda z:hashlib.sha256(z.read_bytes()).hexdigest()
  assert digest(p)==digest(q)
  rows.append(dict(path=str(q),bytes=q.stat().st_size,sha256=digest(q)))
assert rows
out=dict(cache=str(c),files=rows,count=len(rows),bytes=sum(x['bytes'] for x in rows),cache_retained=True,removed_build_outputs=[])
for name in ['NFW_target','NFW_ref_target','NFW_error_ref_target','NFW_objects','NFW_tmp','NFW_native']:
 p=b/name
 if p.exists():
  assert p.parent==b and name.startswith('NFW_')
  shutil.rmtree(p);out['removed_build_outputs'].append(str(p))
(b/'NFW_CACHE_END.json').write_text(json.dumps(out,indent=1)+'\\n')
print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',host,'python3'],input=code,text=True,capture_output=True)
(E/'NFW_CACHE_END.transport.log').write_text(r.stderr);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);(E/'NFW_CACHE_END.json').write_text(json.dumps(j,indent=1)+'\n');print(j['count'],j['bytes'])
