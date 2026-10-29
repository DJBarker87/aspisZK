from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag4-20261029');P=D.parent/'codex-pv-diag3-20261029';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();bad=[];counts={}
for name in ['external-sidecars.json','sidecar-pins.json']:
 rows=json.loads((P/name).read_text());counts[name]=dict(sha256=sha(P/name),checked=len(rows))
 for r in rows:
  p=Path(r['path']);actual=sha(p) if p.is_file() else None
  if actual!=r['sha256']:bad.append(dict(path=str(p),expected=r['sha256'],actual=actual))
(D/'sidecar-preflight.json').write_text(json.dumps(dict(authorities=counts,mismatches=bad),indent=2)+'\n');print(counts,'mismatches',len(bad));assert not bad
