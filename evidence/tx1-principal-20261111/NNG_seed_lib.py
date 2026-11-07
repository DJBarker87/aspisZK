from pathlib import Path
import json,shutil,hashlib
B=Path.cwd();P=Path('/home/dombarker/project-offloads/codex-cx-lib-20261111');request=json.loads((B/'NNG_LIB_SEED_REQUEST.json').read_text());pins=[]
for row in request['modules']:
 m=row['module'];source=P/'LIB_generated'/(m+'.lean');assert hashlib.sha256(source.read_bytes()).hexdigest()==row['source_sha256'],m
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  f=P/'LIB_objects'/(m+suffix)
  if f.exists():
   q=B/'NNG_LIB_objects'/f.name;q.parent.mkdir(exist_ok=True);shutil.copyfile(f,q)
   pins.append(dict(source=str(f),destination=str(q),sha256=hashlib.sha256(f.read_bytes()).hexdigest(),bytes=f.stat().st_size))
(B/'NNG_LIB_SEED_PINS.json').write_text(json.dumps(dict(revision=request['revision'],objects=pins),indent=1))
print('Copied committed LIB carrier objects after exact source hash validation')
