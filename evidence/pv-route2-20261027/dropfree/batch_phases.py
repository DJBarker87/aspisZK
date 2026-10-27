# All roots run sequentially in one 6G/8G/no-swap scope; no nested scope or Lean invocation.
from pathlib import Path
import sys,json,subprocess,time
D=Path(sys.argv[1]);rows=json.loads((D/'phases.json').read_text());failed=set();errors=[]
for row in rows:
 if row['key'] in failed:continue
 O=Path(row['directory']);O.mkdir();(O/'target.json').write_text(json.dumps(row,indent=2));start=time.monotonic()
 with (O/'output.log').open('w') as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),*row['target']],cwd=row['cwd'],stdout=out,stderr=subprocess.STDOUT)
 (O/'receipt.json').write_text(json.dumps(dict(exit=r.returncode,wall_seconds=time.monotonic()-start,revision=row['revision'],print_axioms='N/A extraction',time_log=(O/'time.log').read_text(),shared_capped_scope=str(D)),indent=2))
 print(O.name,r.returncode,flush=True)
 if r.returncode:failed.add(row['key']);errors.append(dict(key=row['key'],phase=row['phase'],exit=r.returncode))
 cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
 (D/'cgroup-latest.json').write_text(json.dumps({k:(cg/k).read_text().strip() for k in ['memory.peak','memory.current','memory.max','memory.high','memory.swap.max','memory.swap.peak','pids.max'] if (cg/k).exists()},indent=2))
(D/'outcomes.json').write_text(json.dumps(dict(errors=errors,completed=True),indent=2));sys.exit(2 if errors else 0)
