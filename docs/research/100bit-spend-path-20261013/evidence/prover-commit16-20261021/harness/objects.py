#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent.parent
rows=[json.loads(l) for p in sorted((E/'lean').glob('attempts-*.jsonl')) for l in p.read_text().splitlines()]
latest={r['module']:r for r in rows if r['accepted']}
inputs=[dict(module=m,source_sha256=r['source_sha256'],deps=r['deps']) for m,r in latest.items()]
code='''import hashlib,json
from pathlib import Path
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
env=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
paths=[J/'objects']+[Path(x) for x in env['LEAN_PATH'].split(':')]
rows=[]
for x in %r:
 p=J/'sources'/x['module'];o=J/'objects'/Path(x['module']).with_suffix('.olean')
 assert hashlib.sha256(p.read_bytes()).hexdigest()==x['source_sha256'],x['module']
 for m,h in x['deps']:
  rel=Path(m.replace('.','/')+'.olean');d=next(d/rel for d in paths if (d/rel).exists())
  assert hashlib.sha256(d.read_bytes()).hexdigest()==h,(x['module'],m)
 rows.append(dict(module=x['module'],source_sha256=x['source_sha256'],object_sha256=hashlib.sha256(o.read_bytes()).hexdigest(),object_bytes=o.stat().st_size,dependency_object_pins_current=True))
P=Path('/home/dombarker/project-offloads/codex-cx-prover-commit16-20261021/sampler16/target/release/aspis-ser-join-probe')
print(json.dumps(dict(lean=rows,sampler_binary=dict(sha256=hashlib.sha256(P.read_bytes()).hexdigest(),bytes=P.stat().st_size)),indent=2))
'''%inputs
out=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True,check=True).stdout
(E/'object-pins.json').write_text(out)
print('Current source and dependency object pins agree for',len(latest),'modules.')
