from pathlib import Path
import json, hashlib, time
H=Path('/home/dombarker/project-offloads/codex-pv-b3q2-20261031')
B=H.parent/'codex-pv-b3q-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads((B/'cache-verification.json').read_text());bad=[]
for n,r in x['objects'].items():
 p=Path(r['object']);expected=r.get('object_sha256',r.get('sha256'))
 if sha(p)!=expected:bad.append(n)
(H/'cache-verification.json').write_text(json.dumps(dict(inherited=str(B),objects=x['objects'],mismatches=bad),indent=2))
assert not bad,bad
print(json.dumps(dict(inherited_objects=len(x['objects']),mismatches=bad)))
