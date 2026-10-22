#!/usr/bin/env python3
from pathlib import Path
import json,sys,time,subprocess
items=[]
for p in Path('/sys/fs/cgroup').rglob('memory.max'):
 try:
  v=p.read_text().strip()
  if v!='max' and (p.parent/'cgroup.events').read_text().startswith('populated 1'):
   items.append({'cgroup':str(p.parent),'max':int(v),'current':int((p.parent/'memory.current').read_text())})
 except (OSError,PermissionError):pass
s=sum(x['max'] for x in items)
r={'timestamp':time.time(),'populated_finite_memory_max':items,'sum_bytes':s,'safe_limit_bytes':55*2**30,'headroom_for_one_new_scope':s+8*2**30<55*2**30,'free':subprocess.check_output(['free','-b'],text=True),'loadavg':Path('/proc/loadavg').read_text(),'caveat':'Finite caps only; uncapped OS and VM workloads remain visible in free and process inventory. Nested finite caps would conservatively double count.'}
Path(sys.argv[1]).write_text(json.dumps(r,indent=2)+'\n');assert r['headroom_for_one_new_scope']
