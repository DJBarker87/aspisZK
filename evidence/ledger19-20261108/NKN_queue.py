from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=[(2,'lean','NKN_OwnerStatements'),(3,'lean','NKN_Driver'),(4,'lean','NKN_ProofDriver'),(5,'link','NKN_Driver'),(6,'link','NKN_ProofDriver'),(7,'audit','fixtures'),(8,'audit','scan')]
if len(sys.argv)>1 and sys.argv[1]=='raw':jobs=[(9+i,'audit','batch'+str(i))for i in range(30)]
for i,k,t in jobs:
 r=subprocess.run([sys.executable,str(E/'NKN_run.py'),f'NKN_L{i:03}',k,t],capture_output=True,text=True)
 with (E/'NKN_QUEUE.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=i,exit=r.returncode,summary=r.stdout[-1500:],error=r.stderr[-2000:]))+'\n')
 print(json.dumps(dict(attempt=i,exit=r.returncode,summary=r.stdout[-350:])),flush=True)
 if r.returncode:
  q=E/f'NKN_audit/{t}/proof{t[5:]}.json' if t.startswith('batch')else None
  if not q or not q.exists():sys.exit(r.returncode)
  x=json.loads(q.read_text());bad=[v for v in x['results']if not v['equal']]
  if len(bad)!=1 or bad[0]['root']!='NHC_DecodeModel.decoder_error' or set(bad[0]['walked_axioms'])!={'Classical.choice','Quot.sound','propext'}:sys.exit(r.returncode)
