"""Remove only completed RPv query objects after the final audit and seal."""
from pathlib import Path
import json
from RPv_attempt import E,B,ssh
assert json.loads((E/'RPv_verification.json').read_text())['errors']==[]
assert json.loads((E/'RPv_axiom-audit.json').read_text())['errors']==[]
names=['RPv_FJv_TopAudit']+[f'RPv_AuditBatch{i:02d}' for i in range(1,12)]
payload='''from pathlib import Path
import hashlib,json
B=Path(%r);names=json.loads(%r);removed=[]
for name in names:
 assert name.startswith('RPv_')
 for ext in ['.olean','.olean.server','.olean.private','.ir']:
  p=B/'RPv_objects'/(name+ext);link=B/'RPv_overlay'/(name+ext)
  if not p.exists():continue
  assert p.is_file() and not p.is_symlink()
  if link.is_symlink():
   assert link.resolve()==p
   link.unlink()
  elif link.exists():raise AssertionError(str(link))
  removed.append({'path':str(p),'overlay':str(link),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size})
  p.unlink()
assert not (B/'RPv_overlay/RPv_FIr_FinishComparison.olean').exists()
print(json.dumps({'removed_query_only_objects':removed,'failed_object_not_installed':True,'retained':'Every accepted source-context object and all predecessor sources/caches'}))
'''%(B,json.dumps(names))
r=ssh('python3 -',payload);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);(E/'RPv_cleanup.json').write_text(json.dumps(out,indent=2)+'\n')
pins=json.loads((E/'RPv_retained-object-pins.json').read_text());(E/'RPv_pre-cleanup-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
for row in out['removed_query_only_objects']:
 pins.pop(row['path'],None);pins.pop(row['overlay'],None)
(E/'RPv_retained-object-pins.json').write_text(json.dumps(pins,indent=2)+'\n');print('removed query artifacts',len(out['removed_query_only_objects']),'retained pins',len(pins))
