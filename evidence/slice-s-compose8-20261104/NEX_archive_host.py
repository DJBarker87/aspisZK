"""Archive owned objects into the retained private cache, then remove rebuildable scratch only."""
import subprocess,json
from pathlib import Path
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import hashlib,json,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-slice-s-compose8-20261029')
c=b.parent/'codex-cx-slice-s-compose8-cache-20261029'
assert (b/'NEX_L040/receipt.json').exists()
r=json.loads((b/'NEX_L040/receipt.json').read_text());assert r['exit_status']==0
out={}
for srcname,dstname in [('NEX_objects','NEX_final_objects_20261104'),('NEX_generated','NEX_final_sources_20261104')]:
 src=b/srcname;dst=c/dstname;dst.mkdir(exist_ok=True)
 for p in src.rglob('*'):
  if not p.is_file():continue
  rel=p.relative_to(src);q=dst/rel;q.parent.mkdir(parents=True,exist_ok=True)
  h=hashlib.sha256(p.read_bytes()).hexdigest()
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  else:shutil.copy2(p,q)
  assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  out[str(q)]={'sha256':h,'bytes':q.stat().st_size}
removed=[]
for name in ['NEX_target','NEX_tmp','NEX_objects']:
 p=b/name
 assert p.parent==b and p.name in ['NEX_target','NEX_tmp','NEX_objects']
 if p.exists():shutil.rmtree(p);removed.append(str(p))
print(json.dumps({'cache':str(c),'preserved':out,'removed_rebuildable_scratch':removed,'private_cache_deleted':False,'keys_or_wallets_touched':False},indent=1))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NEX_HOST_ARCHIVE.stderr.log').write_text(r.stderr)
assert r.returncode==0,r.stderr
(E/'NEX_HOST_ARCHIVE.json').write_text(r.stdout)
print('archived',len(json.loads(r.stdout)['preserved']))
