#!/usr/bin/env python3
from pathlib import Path
import json,time,sys,subprocess
root=Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice');rows=[]
for p in root.glob('*.scope'):
 if not (p/'cgroup.procs').read_text().strip():continue
 limit=(p/'memory.max').read_text().strip()
 rows.append(dict(scope=str(p),memory_max=int(limit) if limit!='max' else None,processes=[subprocess.run(['ps','-p',pid,'-o','args='],text=True,capture_output=True).stdout.strip() for pid in (p/'cgroup.procs').read_text().split()],memory_high=(p/'memory.high').read_text().strip(),memory_swap_max=(p/'memory.swap.max').read_text().strip(),memory_current=int((p/'memory.current').read_text())))
assert all(r['memory_max'] is not None for r in rows), 'Unbounded populated scope'
total=sum(r['memory_max'] or 0 for r in rows)
out=dict(requested_bytes=8*2**30,allowed=total+8*2**30<=55*2**30,utc=time.time(),populated_scopes=rows,bounded_reserved_bytes=total,all_populated_scopes_bounded=all(r['memory_max'] is not None for r in rows),safe_limit_bytes=55*2**30,print_axioms='N/A: read-only resource preflight')
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))

if not out["allowed"]: raise SystemExit(78)
