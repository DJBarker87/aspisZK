#!/usr/bin/env python3
"""Read-only audit of explicitly assigned attempt receipts."""
from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent.parent
code='''from pathlib import Path
import json,hashlib
p=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
out=[]
for lo,hi in [(8100,8399),(9187,9199),(9200,9399)]:
 entries=[]
 for i in range(lo,hi+1):
  q=p/f'out-{i}.log'
  if q.exists():
   entries.append(dict(attempt=i,receipt_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),source_pin=(p/f'sha-{i}.txt').read_text() if (p/f'sha-{i}.txt').exists() else None))
 out.append(dict(start=lo,end=hi,used=len(entries),unused=[i for i in range(lo,hi+1) if not (p/f'out-{i}.log').exists()],entries=entries))
print(json.dumps(out,indent=2))
'''
out=subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True)
(E/'assigned-range-inventory.json').write_text(out)
