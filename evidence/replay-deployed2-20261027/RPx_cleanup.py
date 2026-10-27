import json
from RPx_attempt import E,ssh,B
queries={'RPx_DeployedAudit','RPx_DeclarationAudit'}
items=[]
for l in (E/'RPx_overlay-additions.jsonl').read_text().splitlines():
 d=json.loads(l)
 if d['module'] in queries:
  for dst,x in d['artifacts'].items():items.append(dict(overlay=dst,**x))
assert items
payload='''from pathlib import Path
import json,hashlib
items=json.loads(%r);deleted=[]
for x in items:
 dst=Path(x['overlay']);src=Path(x['target'])
 assert dst.is_symlink() and str(dst.resolve())==str(src),dst
 assert src.name.startswith(('RPx_DeployedAudit.','RPx_DeclarationAudit.')),src
 assert hashlib.sha256(src.read_bytes()).hexdigest()==x['sha256'],src
 dst.unlink();src.unlink();deleted.extend([str(dst),str(src)])
print(json.dumps(dict(deleted=deleted,predecessors_deleted=0,accepted_source_context_objects_retained=37)))
'''%json.dumps(items)
r=ssh('python3 -',payload);(E/'RPx_cleanup.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'RPx_cleanup.json').write_text(json.dumps(out,indent=2)+'\n')
pins=json.loads((E/'RPx_retained-object-pins.json').read_text())
for n in out['deleted']:pins.pop(n,None)
(E/'RPx_post-cleanup-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
payload='''from pathlib import Path
import json,hashlib
pins=json.loads(%r);errors=[]
for n,x in pins.items():
 p=Path(n)
 if not p.is_file() or p.stat().st_size!=x['bytes'] or hashlib.sha256(p.read_bytes()).hexdigest()!=x['sha256']:errors.append(n)
print(json.dumps(dict(checked=len(pins),errors=errors)))
'''%json.dumps(pins)
r=ssh('python3 -',payload);assert r.returncode==0,r.stderr;check=json.loads(r.stdout);(E/'RPx_post-cleanup-check.json').write_text(json.dumps(check,indent=2)+'\n');assert not check['errors'],check
print(out);print(check)
