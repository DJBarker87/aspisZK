"""Read-only predecessor source provenance; never starts Lean."""
from pathlib import Path
import json,hashlib
B=Path('/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028')
x=json.loads(Path('/home/dombarker/project-offloads/codex-cx-l188-cache-20261028/NDJ_CACHE_PINS.json').read_text())
manifest=json.loads(Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/object-source-manifest.json').read_text())['modules']
out={}
for r in x['objects']:
 if r['module'] in out:continue
 row={};s=r.get('source')
 if s and Path(s).is_file():row['available_source']=dict(path=s,sha256=hashlib.sha256(Path(s).read_bytes()).hexdigest())
 pin=manifest.get(r['module'],{}).get('source_pin')
 if pin:row['source_pin']=pin
 if row:out[r['module']]=row
(B/'NDO_PREDECESSOR_SOURCE_PINS.json').write_text(json.dumps(out,indent=2)+'\n')
print(len(out))
