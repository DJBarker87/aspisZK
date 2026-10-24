"""Verify own scope and aggregate before executing one extraction."""
from pathlib import Path
import json,runpy,subprocess,sys,hashlib
O=Path(sys.argv[1]);cmd=sys.argv[2:]
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
limits={k:(cg/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'},limits
scan=runpy.run_path(str(Path(__file__).resolve().parent/'reservation.py'))
r=scan['admission'](requested=0);r.update(own_cgroup=str(cg),limits=limits,command=cmd)
(O/'admission-barrier.json').write_text(json.dumps(r,indent=2)+'\n');assert r['allowed']
pre=json.loads((O/'preflight.json').read_text())
for p,h in pre['source_sha256'].items():
 assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h,p
raise SystemExit(subprocess.run(['/usr/bin/time','-v','-o',str(O/'time.log'),*cmd]).returncode)
