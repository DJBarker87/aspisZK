#!/usr/bin/env python3
"""Run only at the final timing boundary. Refuse other capped user jobs."""
from pathlib import Path
import json,os,subprocess,sys,time
root=Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice')
self_group=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
rows=[]
for p in root.iterdir():
    if not p.is_dir() or not (p/'memory.max').exists():continue
    maximum=(p/'memory.max').read_text().strip()
    if maximum=='max' or p==self_group:continue
    ids=set((p/'cgroup.procs').read_text().split())
    for child in p.rglob('cgroup.procs'):ids.update(child.read_text().split())
    if not ids:continue
    rows.append(dict(cgroup=str(p),memory_max=int(maximum),processes=[dict(pid=pid,args=subprocess.run(['ps','-p',pid,'-o','args='],capture_output=True,text=True).stdout.strip()) for pid in sorted(ids,key=int)]))
x=dict(utc=time.time(),loadavg=Path('/proc/loadavg').read_text().strip(),load=os.getloadavg(),self_cgroup=str(self_group),other_capped_user_jobs=rows,quiet=not rows,inspection='All populated finite-memory top-level user app scopes/services, including descendant processes; OS services are not build jobs')
Path(sys.argv[1]).write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x,indent=2));raise SystemExit(0 if x['quiet'] else 78)
