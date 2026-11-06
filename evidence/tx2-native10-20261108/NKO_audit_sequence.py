"""One combined audit campaign, one admitted capped scope at a time."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
assert not (E/'NKO_AUDIT_PLAN.json').exists(),'Do not repeat unchanged combined campaign'
free=[f'NKO_L{i:03}' for i in range(1,121) if not any(E.glob(f'NKO_L{i:03}*'))]
scopes=['fixtures','scan']+['batch'+str(i) for i in range(len(json.loads((E/'NKO_AUDIT_ROOTS.json').read_text())['groups']))]
plan=[dict(attempt=a,target=t) for a,t in zip(free,scopes)];assert len(plan)==len(scopes)
(E/'NKO_AUDIT_PLAN.json').write_text(json.dumps(dict(campaign=1,scopes=plan),indent=2)+'\n')
for row in plan:
 r=subprocess.run([sys.executable,str(E/'NKO_run.py'),row['attempt'],'audit',row['target']])
 if r.returncode:sys.exit(r.returncode)
