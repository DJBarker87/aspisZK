"""h4/h6'' first-root resolution and hashes; read-only external objects."""
from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');A=H/'external-object-authority.json'
raw=A.read_bytes();assert hashlib.sha256(raw).hexdigest()=='d9187c800b7479f66ec6147e3c8e91c1158d382c4aa467bf678e76901b9a8c0e'
rows=json.loads(raw);roots=sorted({str(Path(r['path']).parents[len(r['module'].split('/'))-1]) for r in rows})
# Root source authority has exactly one selected root per top namespace.
by_namespace={}
for r in rows:
 namespace=r['module'].split('/')[0];root=str(Path(r['path']).parents[len(r['module'].split('/'))-1]);by_namespace.setdefault(namespace,set()).add(root)
assert all(len(v)==1 for v in by_namespace.values())
checks=[]
for r in rows:
 namespace=r['module'].split('/')[0]
 root=next((Path(p) for p in roots if (Path(p)/namespace).is_dir() or (Path(p)/(namespace+'.olean')).is_file()),None)
 p=root/(r['module']+'.olean') if root else None
 actual=hashlib.sha256(p.read_bytes()).hexdigest() if p and p.is_file() else None
 checks.append(dict(module=r['module'],path=str(p),authority_path=r['path'],expected=r['object_sha256'],actual=actual,match=actual==r['object_sha256'] and str(p)==r['path']))
record=dict(authority_sha256=hashlib.sha256(raw).hexdigest(),roots=roots,first_root_rule=True,checks=checks,all_match=all(r['match'] for r in checks))
(H/'lean-authority-check.json').write_text(json.dumps(record,indent=2)+'\n')
assert record['all_match'],[r for r in checks if not r['match']]
(H/'lean-roots.json').write_text(json.dumps(roots,indent=2)+'\n')
print('EXTERNAL_OBJECTS_VERIFIED',len(checks),flush=True)
