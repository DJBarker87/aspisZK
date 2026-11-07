from pathlib import Path
import json,hashlib,shutil
B=Path.cwd();P=Path('/home/dombarker/project-offloads/codex-cx-tx1-owned-20261111');pins=[]
for row in json.loads((B/'NNG_NMT_REQUEST.json').read_text())['modules']:
 assert hashlib.sha256((P/row['source']).read_bytes()).hexdigest()==row['sha256']
 for ext in ['.olean','.olean.private','.olean.server','.ir']:
  src=P/'NMT_objects'/(row['module']+ext)
  if not src.exists():continue
  dst=B/'NNG_objects'/(row['module']+ext);dst.parent.mkdir(parents=True,exist_ok=True)
  data=src.read_bytes()
  if dst.exists():assert dst.read_bytes()==data
  else:shutil.copyfile(src,dst)
  pins.append(dict(source=str(src),destination=str(dst),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)))
(B/'NNG_NMT_OBJECT_PINS.json').write_text(json.dumps(pins,indent=1))
print('Copied pinned fresh NMT tx1 objects into own cache; existing objects unchanged')
