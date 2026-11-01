"""Resume the mandatory real ten-minute polls; never fabricate missed checks."""
from pathlib import Path
import json,time,datetime
B=Path(__file__).resolve().parent
flag=Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/pv-host-restored.flag')
out=B/'gate-polls.jsonl'
rows=[json.loads(s) for s in out.read_text().splitlines()] if out.exists() else []
assert [r['poll'] for r in rows]==list(range(len(rows)))
if rows and rows[-1]['exists']:raise SystemExit('Restoration already recorded; read that row')
previous=rows[-1]['epoch'] if rows else time.time()-600
for n in range(len(rows),25):
 while time.time()<previous+600:time.sleep(min(30,previous+600-time.time()))
 row={'poll':n,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'epoch':time.time(),'flag':str(flag),'exists':flag.exists(),'scope_launched':False}
 if flag.exists():row['contents']=flag.read_text()
 with out.open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row),flush=True)
 if row['exists']:break
 previous=row['epoch']
