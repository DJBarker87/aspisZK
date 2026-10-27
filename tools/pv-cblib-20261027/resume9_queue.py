"""Serial proof queue. Refusals consume IDs, not Lean budget; never retry a compile error."""
from pathlib import Path
import subprocess,time,sys,json,datetime
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027'
# Honor the latest refused admission from this job, including native gates.
refused_admissions=[]
for path in out.glob('*-refusal.json'):
 record=json.loads(path.read_text());body=record.get('output',record.get('reason',''))
 try: data=json.loads(body);instant=datetime.datetime.fromisoformat(data['utc']).timestamp()
 except (ValueError,KeyError,TypeError): instant=path.stat().st_mtime
 refused_admissions.append((instant,body))
for path in out.glob('*/admission-transport.log'):
 try:data=json.loads(path.read_text())
 except ValueError:continue
 if not data.get('allowed',True):refused_admissions.append((datetime.datetime.fromisoformat(data['utc']).timestamp(),json.dumps(data)))
for path in out.glob('*/collected-receipt.json'):
 data=json.loads(path.read_text()).get('admissions',{}).get('admission-barrier.json',{})
 if data and not data.get('allowed',True):refused_admissions.append((datetime.datetime.fromisoformat(data['utc']).timestamp(),json.dumps(data)))
if refused_admissions:
 instant,body=max(refused_admissions)
 delay=30 if 'FileNotFoundError' in body else 209
 seconds=max(0,instant+delay-time.time())
 while seconds>0:
  step=min(60,seconds);time.sleep(step);seconds=max(0,instant+delay-time.time())
for module in sys.argv[1:]:
 refused=0; transient_refusals=0
 while True:
  subprocess.run([sys.executable,str(root/'tools/pv-cblib-20261027/wait_capacity.py')],check=True)
  start=json.loads((out/'TALLY-resume9.json').read_text())['next_id']
  p=subprocess.run([sys.executable,str(root/'tools/pv-cblib-20261027/resume9_lean.py'),module])
  if p.returncode==0:break
  if p.returncode!=78:sys.exit(p.returncode)
  refused+=1
  if refused>10:sys.exit(78)
  record=json.loads((out/f'{start}-refusal.json').read_text())
  transient='FileNotFoundError' in record.get('output',record.get('reason',''))
  if transient:
   transient_refusals+=1
   if transient_refusals>1:sys.exit(78)
  seconds=30 if transient else 180+19+(start%43)
  print('reservation refusal',start,'next unused ID after',seconds,'seconds',flush=True)
  with (out/'queue-waits.jsonl').open('a') as f:f.write(json.dumps({'attempt':start,'module':module,'seconds':seconds,'reason':record})+'\n')
  while seconds:
   step=min(60,seconds);time.sleep(step);seconds-=step
