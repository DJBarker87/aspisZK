from pathlib import Path
import subprocess,json,time,resource,hashlib
w=Path(__file__).resolve().parent
cg=Path('/sys/fs/cgroup')/next(x.split('::',1)[1].strip().lstrip('/') for x in Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::'))
limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max']};assert limits=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0'}
rt=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0')
obj=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/bridge/objects/AspisFormal/CircleGroupOrder.olean')
cmd=[str(rt/'bin/lake'),'--no-cache','env',str(rt/'bin/lean'),'-j1','-M0','--run',str(w/'HistoricalLakeHash.lean'),str(w/'historical-source.lean'),str(obj)]
start=time.monotonic()
with (w/'output.log').open('w') as f:r=subprocess.run(cmd,cwd='/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/backend',stdout=f,stderr=subprocess.STDOUT,timeout=60)
ru=resource.getrusage(resource.RUSAGE_CHILDREN);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
x={'scope':'Read/hash utility only; no theorem/dependency compilation or replay','command':cmd,'limits':limits,'cgroup':str(cg),'exit_status':r.returncode,'wall_seconds':round(time.monotonic()-start,3),'peak_process_rss_kib':ru.ru_maxrss,'process_swaps':ru.ru_nswap,'cgroup_memory_peak':(cg/'memory.peak').read_text().strip(),'cgroup_swap_current':(cg/'memory.swap.current').read_text().strip(),'input_sha256':{str(p):sha(p) for p in [w/'HistoricalLakeHash.lean',w/'historical-source.lean',obj,rt/'bin/lean',rt/'lib/lean/libleanshared.so']},'axioms':'not applicable: no proof declarations requested'}
(w/'receipt.json').write_text(json.dumps(x,indent=2)+'\n');print((w/'output.log').read_text());print(json.dumps(x,indent=2));raise SystemExit(r.returncode)
