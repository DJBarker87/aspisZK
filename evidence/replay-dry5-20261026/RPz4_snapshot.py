"""Read-only object hash inventory and trusted-base stability evidence."""
from pathlib import Path
import hashlib,json,datetime
B=Path('/home/dombarker/project-offloads/codex-cx-replay-dry-20261026')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
trusted=json.loads((B/'RPz_trusted-base.json').read_text());checked=[];changed=[];missing=[]
for name,pin in trusted['artifacts'].items():
 p=Path(name)
 if not p.is_file():missing.append(name);continue
 actual={'sha256':sha(p),'bytes':p.stat().st_size}
 if actual!=pin:changed.append({'path':name,'before':pin,'after':actual})
 checked.append(name)
objects={str(p.relative_to(B)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted((B/'RPz4_objects').rglob('*')) if p.is_file()}
out={'default_lake_object_directory_exists':(B/'.lake/build/lib/lean').exists(),'checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'fresh_repository_objects':objects,'trusted_base_manifest_sha256':sha(B/'RPz_trusted-base.json'),'trusted_artifacts_checked':len(checked),'trusted_artifacts_changed':changed,'trusted_artifacts_missing':missing,'qualification':'Hash inventory only; no additional Lean invocation or source-to-object proof. Existing toolchain/library artifacts remain the owner-approved trusted base.'}
(B/'RPz4_final-object-inventory.json').write_text(json.dumps(out,indent=2)+'\n')
print('fresh files',len(objects),'trusted checked',len(checked),'changed',len(changed),'missing',len(missing))
