"""Replay only missing focused dependencies, one module and capped scope at a time."""
from pathlib import Path
import json,subprocess,sys
E=Path('evidence/pv-batch2-20261027/batch2d')
queue=json.loads((E/'SAMPLER-DEPENDENT-QUEUE.json').read_text())
for m in queue:
 t=json.loads((E/'TALLY.json').read_text())
 if any(a['module']==m and a.get('exit')==0 for a in t['attempts']):continue
 used={a['id'] for a in t['attempts']}|set(json.loads((E/'ID-PREFLIGHT.json').read_text())['used'])
 n=next(n for n in range(39800,39897) if n not in used)
 print('focused dependency',n,m,flush=True)
 r=subprocess.run([sys.executable,'tools/pv-batch2-20261027/lean-batch2d.py',str(n),m])
 if r.returncode:raise SystemExit(r.returncode)
