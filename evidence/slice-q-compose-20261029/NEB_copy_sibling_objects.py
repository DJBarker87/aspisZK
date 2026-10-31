"""Copy peer artifacts only when pinned by its committed successful consumers."""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent;P=json.loads((E/'NEB_SIBLING_OBJECT_PINS.json').read_text())
script='''from pathlib import Path
import hashlib,json,shutil
pins=PINS
cache=Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose-cache-20261029')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
out=[]
for m,d in pins.items():
 p=Path(d['path']);assert sha(p)==d['sha256'],(m,'peer artifact changed')
 for src in p.parent.glob(p.name+'*'):
  dst=cache/(m.replace('.','/')+'.olean'+src.name[len(p.name):]);dst.parent.mkdir(parents=True,exist_ok=True)
  if dst.exists():assert sha(src)==sha(dst),'conflicting cache artifact'
  else:shutil.copy2(src,dst)
  out.append(dict(module=m,source=str(src),destination=str(dst),sha256=sha(dst),peer_build_receipt=d['build_receipt'],peer_consumer_receipt=d['consumer_receipt']))
print(json.dumps(out))
'''.replace('PINS',repr(P))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=script,text=True,capture_output=True);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'NEB_SIBLING_OBJECT_IMPORTS.json').write_text(json.dumps(out,indent=1)+'\n');print('pinned artifacts copied',len(out))
