"""One Kani gate, full admission cooldowns and a receipt-derived run budget."""
from pathlib import Path
from run import H
import json,subprocess,sys,time
kind=sys.argv[1]
for retry in range(11):
 p=H/'admission-not-before.json'
 while p.exists():
  delay=json.loads(p.read_text())['epoch']-time.time()
  if delay<=0:break
  print(json.dumps(dict(gate=kind,cooldown_seconds=round(delay),retry=retry)),flush=True)
  time.sleep(min(60,delay+0.1))
 receipts=[]
 for p in H.glob('*/receipt/receipt.json'):
  r=json.loads(p.read_text())
  if 'kani' in r['command']:receipts.append(str(p))
 assert len(receipts)<12,receipts
 r=subprocess.run(['python3',str(H/'gates.py'),kind])
 if r.returncode!=78 or retry==10:
  actual=sum('kani' in json.loads(p.read_text())['command'] for p in H.glob('*/receipt/receipt.json'))
  t=json.loads((H/'TALLY.json').read_text());t['kani_runs']=actual
  (H/'TALLY.json').write_text(json.dumps(t,indent=2)+'\n')
  print(json.dumps(dict(gate=kind,exit=r.returncode,kani_runs=actual)),flush=True)
  sys.exit(r.returncode)
