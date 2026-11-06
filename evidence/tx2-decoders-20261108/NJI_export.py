from NJI_transport import *
import re,hashlib
src=(E/'NJI_COMBINED_IMPORT.lean').read_text()
mods=re.findall(r'^import (NJI_[\w.]+)',src,re.M)+['NJI_COMBINED_IMPORT']
expected={m:hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest() for m in mods}
dest='/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJI_exports_20261108'
r=ssh('python3',f'''from pathlib import Path
import hashlib,shutil,json
b=Path({B!r});dest=Path({dest!r});expected={expected!r};rows=[]
for module,source_hash in expected.items():
 rel=module.replace('.','/');source=b/'NJI_generated'/(rel+'.lean');assert hashlib.sha256(source.read_bytes()).hexdigest()==source_hash
 p=b/'NJI_objects'/(rel+'.olean');assert p.is_file()
 for f in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not f.is_file():continue
  out=dest/f.relative_to(b/'NJI_objects');out.parent.mkdir(parents=True,exist_ok=True);h=hashlib.sha256(f.read_bytes()).hexdigest()
  if out.exists():assert hashlib.sha256(out.read_bytes()).hexdigest()==h
  else:shutil.copy2(f,out)
  rows.append(dict(module=module,path=str(out),bytes=out.stat().st_size,sha256=h,source_sha256=source_hash))
print(json.dumps(dict(path=str(dest),objects=rows,bytes=sum(x['bytes'] for x in rows),modules=len(expected),seed_manifest='NJI_SEED.json',seed_bytes=12798640,own_target=str(b/'NJI_target'),target_retained=True,cache_retained=True)))
''');assert r.returncode==0,r.stderr
(E/'NJI_EXPORTS.json').write_text(json.dumps(json.loads(r.stdout),indent=1)+'\n')
x=json.loads(r.stdout);print('Retained export',x['modules'],'modules',x['bytes'],'bytes')
