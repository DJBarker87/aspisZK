#!/usr/bin/env python3
"""Run only at the final timing boundary. Refuse other capped user jobs."""
from pathlib import Path
import json,os,subprocess,sys,time
root=Path('/sys/fs/cgroup/user.slice')
self_group=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
rows=[]
for maximum_file in root.rglob('memory.max'):
    p=maximum_file.parent
    if p==self_group or p in self_group.parents or self_group in p.parents:continue
    try:
        maximum=maximum_file.read_text().strip()
        if maximum=='max':continue
        ids=set((p/'cgroup.procs').read_text().split())
        for child in p.rglob('cgroup.procs'):ids.update(child.read_text().split())
    except FileNotFoundError:
        # A completed scope may disappear during inventory.
        continue
    if not ids:continue
    rows.append(dict(cgroup=str(p),memory_max=int(maximum),processes=[dict(pid=pid,args=subprocess.run(['ps','-p',pid,'-o','args='],capture_output=True,text=True).stdout.strip()) for pid in sorted(ids,key=int)]))
units=subprocess.run(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--plain','--no-pager'],capture_output=True,text=True,check=True).stdout
foreign_units=[line for line in units.splitlines() if line.split()[0].startswith(('cx-','pv-')) and not line.split()[0].startswith('pv-gate6-d358-measurement.scope')]
x=dict(running_scopes=units,foreign_cx_pv_scopes=foreign_units,utc=time.time(),loadavg=Path('/proc/loadavg').read_text().strip(),load=os.getloadavg(),self_cgroup=str(self_group),other_capped_user_jobs=rows,quiet=not rows and not foreign_units,inspection='All users: populated finite-memory cgroups under user.slice, including descendants, excluding only this timing scope and its ancestors; OS services are not build jobs')
Path(sys.argv[1]).write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x,indent=2));raise SystemExit(0 if x['quiet'] else 78)
