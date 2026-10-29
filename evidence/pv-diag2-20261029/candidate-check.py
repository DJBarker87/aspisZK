from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');S=D.parent/'codex-pv-fscan-20261028/src';x=json.loads((D/'candidate-source-pins.json').read_text());bad=[]
for r in x['rows']:
 p=S/r['path'];h=hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
 if h!=r['sha256']:bad.append(dict(**r,actual_sha256=h))
(D/'candidate-host-check.json').write_text(json.dumps(dict(candidate_revision=x['revision'],checked=len(x['rows']),mismatches=bad),indent=2)+'\n');print('source identity',len(x['rows']),'mismatches',len(bad));assert not bad
