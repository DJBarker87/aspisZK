from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=[(2,'lean','NLS_OwnerStatements'),(3,'lean','NLS_Driver'),(4,'lean','NLS_ProofDriver'),(5,'link','NLS_Driver'),(6,'link','NLS_ProofDriver'),(7,'audit','fixtures'),(8,'audit','scan')]
if len(sys.argv)>1 and sys.argv[1]=='raw':jobs=[(9+i,'audit','batch'+str(i))for i in range(30)]
for i,k,t in jobs:
 r=subprocess.run([sys.executable,str(E/'NLS_run.py'),f'NLS_L{i:03}',k,t],capture_output=True,text=True)
 with (E/'NLS_QUEUE.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=i,exit=r.returncode,summary=r.stdout[-1500:],error=r.stderr[-2000:]))+'\n')
 print(json.dumps(dict(attempt=i,exit=r.returncode,summary=r.stdout[-350:])),flush=True)
 if r.returncode:
  q=E/f'NLS_audit/{t}/proof{t[5:]}.json' if t.startswith('batch')else None
  if not q or not q.exists():sys.exit(r.returncode)
  x=json.loads(q.read_text());bad=[v for v in x['results']if not v['equal']]
  if len(bad)!=1 or bad[0]['root'] not in ['NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition'] or set(bad[0]['walked_axioms'])!={'Classical.choice','Quot.sound','propext'}:sys.exit(r.returncode)
