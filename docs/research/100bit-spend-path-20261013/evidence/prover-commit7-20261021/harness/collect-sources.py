#!/usr/bin/env python3
import subprocess,json,hashlib,base64
from pathlib import Path
E=Path(__file__).resolve().parent.parent
rows=[json.loads(p.read_text()) for p in sorted((E/'lean').glob('lean-*.json'))]
request=[(r['attempt'],r['module'],r['source_sha256']) for r in rows]
code="""import json,hashlib,base64
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit7-20261021')
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019/sources')
out={}
for a,m,h in %r:
 candidates=[J/m]+list((H/'snapshots').glob('*/'+m))
 for p in candidates:
  b=p.read_bytes()
  if hashlib.sha256(b).hexdigest()==h:
   out[str(a)]=base64.b64encode(b).decode();break
 else:raise AssertionError((a,m,h))
print(json.dumps(out))
"""%request
out=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True))
S=E/'lean/sources';S.mkdir(exist_ok=True)
for a,b in out.items():(S/(a+'.lean')).write_bytes(base64.b64decode(b))
print(json.dumps(dict(exact_sources=len(out))))
