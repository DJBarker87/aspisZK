# Executes only the two measured commands, sequentially inside the caller's single scope.
from pathlib import Path
import sys,json,subprocess,time
D=Path(sys.argv[1]);rows=json.loads((D/'phases.json').read_text())
for row in rows:
 O=Path(row['directory']);O.mkdir();(O/'target.json').write_text(json.dumps(row,indent=2));start=time.monotonic()
 with (O/'output.log').open('w') as out:
  r=subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),*row['target']],cwd=row['cwd'],stdout=out,stderr=subprocess.STDOUT)
 (O/'receipt.json').write_text(json.dumps(dict(exit=r.returncode,wall_seconds=time.monotonic()-start,revision=row['revision'],print_axioms='N/A extraction',time_log=(O/'time.log').read_text(),shared_capped_scope=str(D)),indent=2))
 print(O.name,r.returncode,flush=True)
 if r.returncode:break

# Scope-level aggregate memory peak, in addition to per-phase GNU peak RSS.
cgroup=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
resource={k:(cgroup/k).read_text().strip() for k in ['memory.peak','memory.max','memory.high','memory.swap.max','memory.swap.peak','pids.max'] if (cgroup/k).exists()}
(D/'cgroup-final.json').write_text(json.dumps(resource,indent=2))
sys.exit(r.returncode)
