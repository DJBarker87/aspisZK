"""Remove completed own query-only objects after final consistency verification."""
from pathlib import Path
import json
from RPt_attempt import E,B,ssh
assert json.loads((E/'RPt_final-verification.json').read_text())['errors']==[]
assert json.loads((E/'RPt_axiom-audit.json').read_text())['errors']==[]
names=['RPt_BEnAudit']+[f'RPt_AuditBatch{i:02d}' for i in range(1,5)]
payload='''from pathlib import Path
import hashlib,json
B=Path(%r);names=json.loads(%r);removed=[]
for name in names:
 assert name.startswith('RPt_')
 for ext in ['.olean','.olean.server','.olean.private','.ir']:
  p=B/'RPt_objects'/(name+ext);link=B/'RPt_overlay'/(name+ext)
  if not p.exists():continue
  assert p.is_file() and not p.is_symlink()
  if link.is_symlink():
   assert link.resolve()==p
   link.unlink()
  elif link.exists():raise AssertionError(str(link))
  removed.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size})
  p.unlink()
print(json.dumps({'removed_query_only_objects':removed,'retained':'All accepted source-context proof objects, sources and predecessor caches'}))
'''%(B,json.dumps(names))
r=ssh('python3 -',payload);assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
(E/'RPt_cleanup.json').write_text(json.dumps(out,indent=2)+'\n')
pins=json.loads((E/'RPt_final-object-pins.json').read_text())
for row in out['removed_query_only_objects']:pins.pop(row['path'],None)
(E/'RPt_retained-object-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
print(r.stdout)
