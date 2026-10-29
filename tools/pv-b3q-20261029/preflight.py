"""Read-only h4/h6 preflight; only writes this line's directory."""
from pathlib import Path
import json,hashlib,subprocess,time
H=Path('/home/dombarker/project-offloads/codex-pv-b3q-20261029')
B=Path('/home/dombarker/project-offloads/codex-pv-b3p6-20261028')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
H.mkdir(exist_ok=True)
bad=[];ext=json.loads((B/'external-object-manifest.json').read_text())
for r in ext:
 p=Path(r['path']);actual=sha(p) if p.exists() else None
 if actual!=r['object_sha256']:bad.append(dict(kind='external',module=r['module'],path=str(p),expected=r['object_sha256'],actual=actual))
x=dict(epoch=time.time(),external_count=len(ext),mismatches=bad)
(H/'preflight.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(x));assert not bad,bad
