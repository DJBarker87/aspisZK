from pathlib import Path
import time,subprocess,sys,json
E=Path(__file__).resolve().parent
while not(E/'NLG_L038/receipt.json').exists()or(E/'NLG_CLIENT_ACTIVE').exists():time.sleep(3)
assert json.loads((E/'NLG_L038/receipt.json').read_text())['exit_status']==0
for a,k,t in [('NLG_L039','lean','NLG_HypothesisReview'),('NLG_L040','audit','close')]:
 r=subprocess.run([sys.executable,str(E/'NLG_run.py'),a,k,t],capture_output=True,text=True)
 with(E/'NLG_CLOSE_QUEUE.jsonl').open('a')as f:f.write(json.dumps(dict(attempt=a,exit=r.returncode,summary=r.stdout[-1000:],error=r.stderr[-2000:]))+'\n')
 print(json.dumps(dict(attempt=a,exit=r.returncode,summary=r.stdout[-350:])),flush=True)
 if r.returncode:sys.exit(r.returncode)
