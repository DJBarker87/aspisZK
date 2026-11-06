"""Remaining authorized serial scopes; retains completed raw groups."""
from pathlib import Path
import subprocess,sys,json,time
E=Path(__file__).resolve().parent
while (E/'NKH_CLIENT_ACTIVE').exists():time.sleep(5)
assert json.loads((E/'NKH_L026/receipt.json').read_text())['exit_status']==0
jobs=[(i+10,'audit','batch'+str(i))for i in range(17,28)]+[(38,'audit','batch28-29'),(39,'lean','NKH_HypothesisReview'),(40,'audit','close')]
for i,k,t in jobs:
 r=subprocess.run([sys.executable,str(E/'NKH_run.py'),f'NKH_L{i:03}',k,t],capture_output=True,text=True)
 x=dict(attempt=i,target=t,exit=r.returncode,summary=r.stdout[-1200:],error=r.stderr[-2000:])
 with (E/'NKH_RESUME_QUEUE.jsonl').open('a')as f:f.write(json.dumps(x)+'\n')
 print(json.dumps(dict(attempt=i,target=t,exit=r.returncode)),flush=True)
 if r.returncode:
  paths=list((E/'NKH_audit'/t).glob('proof*.json'))
  if not paths:sys.exit(r.returncode)
  bad=[v for p in paths for v in json.loads(p.read_text())['results']if not v['equal']]
  if len(bad)!=1 or bad[0]['root']!='NHC_DecodeModel.decoder_error' or set(bad[0]['walked_axioms'])!={'Classical.choice','Quot.sound','propext'}:sys.exit(r.returncode)
