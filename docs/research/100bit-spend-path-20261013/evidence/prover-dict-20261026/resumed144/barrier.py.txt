"""Read-only admission and exact own limits before executing a capped job."""
from pathlib import Path
import json,runpy,subprocess,sys
out=Path(sys.argv[1]);cmd=sys.argv[2:]
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
limits={k:(cg/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert limits=={'memory.high':str(5*2**30),'memory.max':str(7*2**30),'memory.swap.max':'0','pids.max':'64'},limits
scanner=runpy.run_path(str(Path(__file__).with_name('reservation.py')))
result=scanner['admission'](requested=0)
result.update(own_cgroup=str(cg),own_limits=limits,command=cmd)
out.write_text(json.dumps(result,indent=2)+'\n')
assert result['allowed'],result
raise SystemExit(subprocess.run(cmd).returncode)
