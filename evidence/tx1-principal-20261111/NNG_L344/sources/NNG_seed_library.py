from pathlib import Path
import json,shutil,hashlib
B=Path.cwd();P=Path('/home/dombarker/project-offloads/codex-cx-lib-20261111');pins=[]
def copy(f,q,expected=None):
 data=f.read_bytes();h=hashlib.sha256(data).hexdigest()
 if expected:assert h==expected,str(f)
 q.parent.mkdir(exist_ok=True,parents=True)
 if q.exists():assert q.read_bytes()==data,str(q)
 else:shutil.copyfile(f,q)
 pins.append(dict(source=str(f),destination=str(q),sha256=h,bytes=len(data)))
spec=json.loads((B/'NNG_LIB_SPEC_PINS.json').read_text())
assert spec['revision']=='b5d8c1d436901e9842aaa4de38b9baeda6b4d9d6'
for row in spec['objects']:
 f=Path(row['path']);q=B/'NNG_RSL3'/f.name;copy(f,q,row['sha256'])
 for suffix in ['.private','.server']:
  z=Path(str(f)+suffix)
  if z.exists():copy(z,Path(str(q)+suffix))
 z=f.with_suffix('.ir')
 if z.exists():copy(z,q.with_suffix('.ir'))
for row in json.loads((B/'NNG_LIB_C_IMPORTS.json').read_text())['files']:
 f=Path(row['destination']);q=B/('NNG_'+str(f.relative_to(P)))
 copy(f,q,row['sha256'])
request=json.loads((B/'NNG_LIB_SEED_REQUEST5.json').read_text())
for row in request['modules']:
 m=row['module'];src=P/'LIB_generated'/(m+'.lean');assert hashlib.sha256(src.read_bytes()).hexdigest()==row['source_sha256']
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  f=P/'LIB_objects'/(m+suffix)
  if f.exists():copy(f,B/'NNG_LIB_objects'/f.name)
(B/'NNG_LIBRARY_PINS.json').write_text(json.dumps(dict(revision=request['revision'],rev3=spec['revision'],objects=pins),indent=1))
print('Copied concrete LIB_VLib, merged LIBC objects and exact rev3 RSL closure; no rev2 object selected')
