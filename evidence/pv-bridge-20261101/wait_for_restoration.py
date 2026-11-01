"""Implement pv-common (g)'s 24 ten-minute polls; never launch anything."""
from pathlib import Path
import json,time,datetime
B=Path(__file__).resolve().parent
flag=Path('/private/tmp/claude-501/-Users-dominic-ZK/4dec4925-8c43-447e-9333-6147c1c7863b/scratchpad/pv-host-restored.flag')
out=B/'gate-polls.jsonl'
assert not out.exists(), 'Recover existing poll history rather than restart it'
for n in range(25):
 if n:
  for _ in range(20):time.sleep(30)
 row={'poll':n,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'epoch':time.time(),'flag':str(flag),'exists':flag.exists(),'scope_launched':False}
 if flag.exists():row['contents']=flag.read_text()
 with out.open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row),flush=True)
 if row['exists']:break
