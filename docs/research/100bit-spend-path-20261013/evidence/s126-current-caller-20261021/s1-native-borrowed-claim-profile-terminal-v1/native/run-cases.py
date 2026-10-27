#!/usr/bin/env python3
"""Sequential rejected-prefix checks; each child performs fresh admission."""
from pathlib import Path
import json,subprocess,sys,time
W=Path(sys.argv[1]).resolve()
record=W/'rejection-sequence.json'
assert not record.exists()
rows=[]
for case in ['point'+str(i)for i in range(6)]+['negative']:
 start=time.monotonic()
 command=['python3',str(W/'nuc.py'),case]
 print(json.dumps({'case':case,'state':'starting'}),flush=True)
 status=subprocess.call(command)
 row={'case':case,'command':command,'exit_status':status,'wall_seconds':time.monotonic()-start}
 rows.append(row);record.write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','runs':rows},indent=2)+'\n')
 print(json.dumps(row),flush=True)
 if case!='negative'and status:raise SystemExit(status)
 if case=='negative'and status==0:raise SystemExit('Negative control unexpectedly passed')
