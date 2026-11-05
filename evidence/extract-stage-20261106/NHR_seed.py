"""Copy read-only assigned cache seeds; never modify/delete existing seed/cache."""
from pathlib import Path
import hashlib,json,shutil
E=Path(__file__).resolve().parent
P=Path('/home/dombarker/project-offloads')
D=P/'codex-cx-slice-d-prepared-cache-20261104'/'NHR_seed_20261106'
roots=[P/'codex-cx-slice-d-define-cache-20261104'/'NFQ_exports_20261104',P/'codex-cx-slice-q-accum-cache-20261104'/'NFS_exports_20261104',P/'codex-cx-slice-q-phase-cache-20261104'/'NFN_exports_20261104',P/'codex-cx-slice-q-mul9-cache-20261104'/'NFM_exports_20261104',P/'codex-cx-leaf-cache-20261027',P/'codex-cx-cpilot-cache-20261028']
pins=[]
for i,root in enumerate(roots):
 assert root.is_dir(),root
 dest=D/str(i)
 for p in sorted(root.rglob('*')):
  if not p.is_file() or not str(p).endswith(('.olean','.olean.private','.olean.server','.ir')):continue
  q=dest/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True)
  h=hashlib.sha256(p.read_bytes()).hexdigest()
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  else:shutil.copy2(p,q)
  pins.append(dict(source=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
(E/'NHR_SEED.json').write_text(json.dumps(dict(roots=[str(D/str(i)) for i in range(6)],files=pins),indent=2)+'\n')
print(len(pins),sum(p['bytes'] for p in pins))
