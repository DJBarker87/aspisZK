"""PCM-owned cache input selection, copying retained objects; no shared writes."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-pc-pool-library1-cache-20261110'
manifest=json.loads((E.parent/'lib-20261111/LIB_BUNDLE_EXPORT.json').read_text())
selected=[r for r in manifest['files'] if r.get('module') in ['RSL_Base','RSL_Pool']]
assert len(selected)==2
code='''from pathlib import Path
import json,hashlib,shutil
b=Path(B); b.mkdir(exist_ok=True)
rows=[]
for r in selected:
 p=Path(r['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
 for s in ['', '.private','.server']:
  src=Path(str(p)+s)
  if not src.exists():continue
  dst=b/'PCM_seed'/src.name;dst.parent.mkdir(exist_ok=True)
  h=hashlib.sha256(src.read_bytes()).hexdigest()
  if dst.exists():assert hashlib.sha256(dst.read_bytes()).hexdigest()==h
  else:shutil.copy2(src,dst)
  rows.append(dict(source=str(src),destination=str(dst),sha256=h,bytes=dst.stat().st_size))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 dst=b/n
 if dst.exists():assert dst.read_bytes()==(w/n).read_bytes()
 else:shutil.copy2(w/n,dst)
(b/'PCM_objects').mkdir(exist_ok=True)
(b/'PCM_tmp').mkdir(exist_ok=True)
print(json.dumps(dict(files=rows,disk=shutil.disk_usage(b)._asdict())))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nselected='+repr(selected)+'\n'+code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
(E/'PCM_CACHE_IMPORTS.json').write_text(r.stdout)
print('PCM cache seeded: '+str(len(json.loads(r.stdout)['files']))+' pinned object files')
