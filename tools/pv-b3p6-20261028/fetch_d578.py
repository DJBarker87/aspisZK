"""Fetch immutable receipts and audit walks, never objects."""
from pathlib import Path
import subprocess,json,base64
R=Path('evidence/pv-b3p6-20261028/resume18');H='/home/dombarker/project-offloads/codex-pv-b3p6-20261028'
code="""from pathlib import Path
import json,base64
H=Path(HOST)
paths=(H/'resume18/D578-collect-paths.txt').read_text().splitlines()
print(json.dumps({n:base64.b64encode((H/n).read_bytes()).decode()for n in paths}))
""".replace('HOST',repr(H))
x=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True))
for n,s in x.items():
 b=base64.b64decode(s);p=R/n.removeprefix('resume18/')
 if n.startswith('source/NEP_'):p=R/'nep-reachable'/Path(n).name
 if '/'not in n:p=R/('D578-'+n)
 p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==b,('never overwrite differing receipt',str(p))
 else:p.write_bytes(b)
print('fetched',len(x),'immutable artifacts')
