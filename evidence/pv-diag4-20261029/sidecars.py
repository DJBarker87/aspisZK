from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag4-20261029')
assert json.loads((D/'v2-dependency-preflight.json').read_text())['mismatches']==[]
rows=[]
for p in (D/'objects').rglob('*.olean'):
 if not p.is_symlink():continue
 real=p.resolve()
 for suffix in ['.server','.private','IR']:
  q=real.with_suffix('.ir') if suffix=='IR' else Path(str(real)+suffix)
  out=p.with_suffix('.ir') if suffix=='IR' else Path(str(p)+suffix)
  if q.is_file():
   if not out.exists():out.symlink_to(q)
   rows.append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
(D/'sidecar-pins.json').write_text(json.dumps(rows,indent=2)+'\n')
print('pinned sidecars',len(rows))
