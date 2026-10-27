"""Serial proof queue. Refusals consume IDs, not Lean budget; never retry a compile error."""
from pathlib import Path
import subprocess,time,sys,json,datetime
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027'
# Honor an outstanding refusal before the first queued request.
refusals=sorted(out.glob('*-refusal.json'),key=lambda p:p.stat().st_mtime)
if refusals:
 record=json.loads(refusals[-1].read_text())
 body=record.get('output',record.get('reason',''))
 try: utc=json.loads(body)['utc']; instant=datetime.datetime.fromisoformat(utc).timestamp()
 except (ValueError,KeyError,TypeError): instant=refusals[-1].stat().st_mtime
 delay=30 if 'FileNotFoundError' in body else 180
 seconds=max(0,instant+delay-time.time())
 while seconds>0:
  step=min(60,seconds);time.sleep(step);seconds=max(0,instant+delay-time.time())
for module in sys.argv[1:]:
 refused=0; transient_refusals=0
 while True:
  start=json.loads((out/'TALLY.json').read_text())['next_id']
  p=subprocess.run([sys.executable,str(root/'tools/pv-cblib-20261027/lean.py'),module])
  if p.returncode==0:break
  if p.returncode!=78:sys.exit(p.returncode)
  refused+=1
  if refused>10:sys.exit(78)
  record=json.loads((out/f'{start}-refusal.json').read_text())
  transient='FileNotFoundError' in record.get('output',record.get('reason',''))
  if transient:
   transient_refusals+=1
   if transient_refusals>1:sys.exit(78)
  seconds=30 if transient else 180
  print('reservation refusal',start,'next unused ID after',seconds,'seconds',flush=True)
  with (out/'queue-waits.jsonl').open('a') as f:f.write(json.dumps({'attempt':start,'module':module,'seconds':seconds,'reason':record})+'\n')
  while seconds:
   step=min(60,seconds);time.sleep(step);seconds-=step
