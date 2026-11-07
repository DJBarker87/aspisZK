from pathlib import Path
import hashlib,json,shutil
B=Path.cwd();P=Path('/home/dombarker/project-offloads/codex-cx-lib-20261111');pins=[]
request=json.loads((B/'NNG_COMPLETE_LIB_REQUEST.json').read_text())
for row in request['modules']:
 m=row['module'];src=P/'LIB_generated'/(m+'.lean')
 assert hashlib.sha256(src.read_bytes()).hexdigest()==row['sha256'],m
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  f=P/'LIB_objects'/(m+suffix)
  if not f.exists():continue
  data=f.read_bytes();dst=B/'NNG_LIB_objects'/f.name
  if dst.exists():assert dst.read_bytes()==data, 'Existing pinned object changed: '+m
  else:shutil.copyfile(f,dst)
  pins.append(dict(source=str(f),destination=str(dst),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)))
(B/'NNG_COMPLETE_LIB_PINS.json').write_text(json.dumps(dict(revision=request['revision'],objects=pins),indent=1))
print('Copied exact completed library objects; existing pinned objects unchanged')
