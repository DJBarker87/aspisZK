"""Serial proof-batch orchestration; uses the unchanged lead-owned host runner."""
from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent;start=int(sys.argv[1]);number=int(sys.argv[2])
plan=json.loads((E.parent/'native-reconcile-20261028/NDO_RETARGET_PLAN.json').read_text())
while start<len(plan):
 attempt=f'NDR_B{number:03d}';end=min(start+120,len(plan))
 assert not (E/(attempt+'.json')).exists(),'Do not resubmit an existing attempt'
 print(f'{attempt}: [{start},{end})',flush=True)
 p=subprocess.run([sys.executable,str(E/'NDR_chunk.py'),attempt,str(start),str(end)],capture_output=True,text=True)
 (E/(attempt+'-transport.log')).write_text(p.stdout+p.stderr)
 if p.returncode:print(p.stdout[-1000:]+p.stderr[-2000:],flush=True);sys.exit(p.returncode)
 r=json.loads((E/attempt/'receipt.json').read_text())
 print(json.dumps({k:r[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps']}),flush=True)
 assert r['exit_status']==0
 start=end;number+=1
