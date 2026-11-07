from pathlib import Path
import json,hashlib,shutil
B=Path.cwd();request=json.loads((B/'NNG_F9_REQUEST.json').read_text());pins=[]
for row in request['files']:
 f=Path(row['path']);data=f.read_bytes();assert hashlib.sha256(data).hexdigest()==row['sha256'],str(f)
 dst=B/'NNG_F9_objects'/f.name;dst.parent.mkdir(exist_ok=True)
 if dst.exists():assert dst.read_bytes()==data
 else:shutil.copyfile(f,dst)
 pins.append(dict(source=str(f),destination=str(dst),sha256=row['sha256'],bytes=len(data)))
(B/'NNG_F9_PINS.json').write_text(json.dumps(dict(revision=request['revision'],objects=pins),indent=1))
print('F9 retained objects copied with exact hash checks; old objects retained')
