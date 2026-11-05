"""One admitted scope at a time; stop on unexpected exit, never retry a timeout."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
jobs=[(44,'lean','NGQ_QueryBudget'),(45,'lean','NGQ_COMBINED_IMPORT'),(46,'lean','NGQ_ProofDriver'),(47,'link','NGQ_ProofDriver'),(48,'audit','fixtures')]
ng=len(json.loads((E/'NGQ_AUDIT_ROOTS.json').read_text())['groups'])
jobs += [(49+i,'audit','batch'+str(i)) for i in range(ng)]
jobs += [(49+ng,'audit','scan')]
assert max(x[0] for x in jobs)<=60
for n,kind,target in jobs:
 a=f'NGQ_L{n:03}';p=E/a/'receipt.json'
 if p.exists():
  if json.loads(p.read_text())['exit_status']!=0:raise SystemExit('prior failed attempt: '+a)
  continue
 r=subprocess.run(['python3',str(E/'NGQ_run.py'),a,kind,target],capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 if not p.exists():raise SystemExit('no receipt: '+a)
 rec=json.loads(p.read_text());print(a,kind,target,rec['exit_status'],rec['wall_seconds'],rec['peak_rss_kib'],flush=True)
 if rec['exit_status']!=0:raise SystemExit('failed: '+a)
