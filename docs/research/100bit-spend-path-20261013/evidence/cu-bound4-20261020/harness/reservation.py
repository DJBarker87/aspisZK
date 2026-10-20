"""Snapshot populated systemd scope memory reservations; fail above 55 GiB."""
import json,sys,time
from pathlib import Path
rows=[]
for root in [Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice')]:
 for p in root.glob('*.scope'):
  try:
   ev=(p/'cgroup.events').read_text();m=(p/'memory.max').read_text().strip()
   if 'populated 1' not in ev or m=='max':continue
   rows.append(dict(scope=p.name,memory_max=int(m),memory_high=(p/'memory.high').read_text().strip(),swap_max=(p/'memory.swap.max').read_text().strip(),pids_max=(p/'pids.max').read_text().strip()))
  except FileNotFoundError:pass
out=dict(utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),populated_scopes=rows,total_reserved_bytes=sum(r['memory_max'] for r in rows),safe_limit_bytes=55*2**30)
assert out['total_reserved_bytes']<=out['safe_limit_bytes'],out
Path(sys.argv[1]).write_text(json.dumps(out,indent=1));print(out['total_reserved_bytes']/2**30,'GiB reserved')
