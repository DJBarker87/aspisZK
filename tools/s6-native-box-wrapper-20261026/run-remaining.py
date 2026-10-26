#!/usr/bin/env python3
"""Sequential remaining native field families: fresh scope admission each time."""
from pathlib import Path
import json,subprocess,time
W=Path(__file__).resolve().parent
PREVIOUS=W.parent/'native-box-wrapper-20261026-v7'
for i in range(14):assert json.loads((PREVIOUS/('run-family'+str(i))/'terminal.json').read_text())['exit_status']==0
out=W/'family-sequence.jsonl'
assert not out.exists()
for family in range(14,25):
 case='family'+str(family)
 assert not (W/('run-'+case)).exists()
 status=subprocess.call(['/usr/bin/python3','-I','-S','-B',str(W/'nuc.py'),case])
 record={'case':case,'exit_status':status,'time':time.time()}
 if status==0:
  r=json.loads((W/('run-'+case)/'verify-receipt.json').read_text())
  record.update({k:r[k] for k in ['wall_seconds','peak_rss_kib','swaps']})
 with out.open('a') as f:f.write(json.dumps(record)+'\n')
 print(json.dumps(record),flush=True)
 if status:raise SystemExit(status)
