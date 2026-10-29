"""Task-local refusal timing guard; does not change host infrastructure."""
from pathlib import Path
import json,time,datetime,sys
E=Path(__file__).resolve().parents[2]/'evidence/pv-rdb2e-20261029'
def refuse(where,detail):
 with (E/'refusals.jsonl').open('a')as f:f.write(json.dumps(dict(epoch=time.time(),utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),where=where,detail=detail))+'\n')
def check_ready():
 p=E/'refusals.jsonl'
 if p.exists():
  latest=max(json.loads(x)['epoch'] for x in p.read_text().splitlines() if x)
  remaining=180-(time.time()-latest)
  if remaining>0:
   print(f'LOCAL COOLDOWN HOLD {remaining:.1f}s; no host call or scope launched',flush=True);sys.exit(78)
