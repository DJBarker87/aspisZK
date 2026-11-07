from pathlib import Path
import json,hashlib,shutil
B=Path.cwd();pins=[]
for m,h in json.loads((B/'NNG_F9_RETAIN_REQUEST.json').read_text()).items():
 s=B/'NNG_generated'/(m+'.lean');assert hashlib.sha256(s.read_bytes()).hexdigest()==h,m
 for ext in ['.olean','.olean.private','.olean.server','.ir']:
  p=B/'NNG_objects'/(m+ext)
  if p.exists():pins.append(dict(module=m,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
assert len([p for p in pins if p['path'].endswith('.olean')])==12
(B/'NNG_F9_RETAINED_OBJECTS.json').write_text(json.dumps(dict(objects=pins,retained_in_place=True,deletions=0,free_bytes=shutil.disk_usage(B).free),indent=1))
print('Pinned12 checked own modules in retained private cache; no deletions')
