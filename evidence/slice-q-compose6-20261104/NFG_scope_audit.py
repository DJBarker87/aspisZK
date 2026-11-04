"""Read-only final audit of the recorded lane scopes."""
from NFG_remote import *
rows=[json.loads(p.read_text()) for p in E.glob('NFG_*/receipt.json') if p.parent.name.startswith(('NFG_L','NFG_K','NFG_E'))]
paths=sorted({r['cgroup'] for r in rows})
r=ssh('NFG_FINAL_SCOPE_AUDIT','python3',f'''from pathlib import Path
import json
out=[]
for n in {paths!r}:
 p=Path(n)/'cgroup.procs'
 if p.exists() and p.read_text().strip():out.append(dict(cgroup=n,pids=p.read_text().split()))
print(json.dumps(dict(recorded_scopes={len(paths)},active=out),indent=1))
''');assert r.returncode==0,r.stderr
out=json.loads(r.stdout);assert out['active']==[],out
(E/'NFG_SCOPE_AUDIT.json').write_text(r.stdout)
