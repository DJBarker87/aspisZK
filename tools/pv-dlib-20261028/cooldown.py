"""Local input guard for this job only; no host launcher or barrier changes."""
from pathlib import Path
import json,time,datetime
E=Path(__file__).resolve().parents[2]/'evidence/pv-dlib-20261028'
P=E/'COOLDOWN.json'
def check_ready():
 if P.exists():
  j=json.loads(P.read_text());remaining=j['ready_epoch']-time.time()
  if remaining>0:
   print('LOCAL COOLDOWN HOLD; no host admission, no ID consumed; seconds remaining',round(remaining,3),flush=True)
   raise SystemExit(75)
def refuse(context,detail=None):
 received=time.time();ready=received+180
 if P.exists():ready=max(ready,json.loads(P.read_text())['ready_epoch'])
 j=dict(context=context,received_epoch=received,received_utc=datetime.datetime.fromtimestamp(received,datetime.timezone.utc).isoformat(),ready_epoch=ready,ready_utc=datetime.datetime.fromtimestamp(ready,datetime.timezone.utc).isoformat(),detail=detail)
 P.write_text(json.dumps(j,indent=2)+'\n')
 with (E/'cooldown-history.jsonl').open('a') as f:f.write(json.dumps(j)+'\n')
 print('FULL180SECOND COOLDOWN starts after refusal receipt; ready',j['ready_utc'],flush=True)
