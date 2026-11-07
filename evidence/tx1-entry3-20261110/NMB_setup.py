"""Copy, hash-validate and retain named predecessor exports; no shared writes."""
from NMB_transport import *
import hashlib,lzma
manifests={tag:json.loads((E/f'NMB_seed_{tag}.json').read_text()) for tag in ['NLQ','NLF','NLS']}
admission('NMB_seed')
code='''from pathlib import Path
import json,shutil,hashlib,lzma
b=Path(B);rows=[]
for tag,m in manifests.items():
 src=Path(m['export'])
 for f in m['files']:
  rel=f.get('relative') or str(Path(f['path']).relative_to(src))
  p=src/rel;raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest()
  assert h==f['sha256'],str(p)
  q=b/'NMB_seed'/tag/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  rows.append(dict(source=str(p),destination=str(q),sha256=h,bytes=len(raw)))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
for n in ['NMB_objects','NMB_generated','NMB_tmp','NMB_target']:(b/n).mkdir(exist_ok=True)
x=dict(files=rows,bytes=sum(r['bytes'] for r in rows))
(b/'NMB_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(x).encode()))
print(json.dumps(dict(files=len(rows),bytes=x['bytes'])))
'''
r=ssh('python3','B='+repr(B)+'\nmanifests='+repr(manifests)+'\n'+code)
(E/'NMB_SETUP.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stderr
r=ssh('python3',"from pathlib import Path;print(Path("+repr(B+'/NMB_CACHE_IMPORTS.json.xz')+").read_bytes().hex())")
assert r.returncode==0
(E/'NMB_CACHE_IMPORTS.json.xz').write_bytes(bytes.fromhex(r.stdout.strip()))
print('NMB export copy validated')
