"""Read-only h4 preflight: check replay's entire external object inventory."""
from pathlib import Path
import hashlib,json,time
H=Path('/home/dombarker/project-offloads/codex-pv-b3p6-20261028')
p=H/'external-object-manifest.json'
rows=json.loads(p.read_text());checked=[];bad=[]
for r in rows:
 q=Path(r['path']);h=hashlib.sha256(q.read_bytes()).hexdigest() if q.is_file() else None
 x=dict(module=r['module'],path=str(q),expected=r['object_sha256'],actual=h,match=h==r['object_sha256'])
 checked.append(x)
 if not x['match']:bad.append(x)
out=dict(manifest_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),checked_before_any_compile=True,checked_count=len(checked),mismatches=bad,objects=checked,epoch=time.time())
(H/'external-verification.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps(dict(checked=len(checked),mismatches=bad)))
