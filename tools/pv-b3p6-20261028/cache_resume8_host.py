"""Read-only check of retained own cache against resume7's frozen inventory."""
from pathlib import Path
import json,hashlib,time
from run import H
rows=json.loads((H/'archive-resume7/private-object-manifest.json').read_text());bad=[]
for r in rows:
 p=H/r['path'];actual=hashlib.sha256(p.read_bytes()).hexdigest()if p.exists()else None
 if actual!=r['sha256']:bad.append(dict(path=str(p),expected=r['sha256'],actual=actual))
x=dict(checked=len(rows),mismatches=bad,epoch=time.time(),authority='own retained private-object-manifest.json from resume7; all unchanged predecessors reused read-only')
(H/'cache-verification-resume8.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x));assert not bad
