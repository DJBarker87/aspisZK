from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');rows=[]
for r in json.loads((D/'external-authority.json').read_text()):
 dst=D/'objects'/(r['module']+'.olean');dst.parent.mkdir(parents=True,exist_ok=True)
 if not dst.exists():dst.symlink_to(r['path'])

for p in (D/'objects').rglob('*.olean'):
 real=p.resolve()
 for suffix in ['.server','.private','IR']:
  s=real.with_suffix('.ir') if suffix=='IR' else Path(str(real)+suffix);dst=p.with_suffix('.ir') if suffix=='IR' else Path(str(p)+suffix)
  if s.is_file():
   if not dst.exists():dst.symlink_to(s)
   rows.append(dict(module=str(p.relative_to(D/'objects')),kind=suffix,path=str(s),sha256=hashlib.sha256(s.read_bytes()).hexdigest()))
(D/'resume-sidecar-pins.json').write_text(json.dumps(rows,indent=2)+'\n');print('private project sidecars',len(rows))
