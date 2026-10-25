#!/usr/bin/env python3
"""Bounded read-only NUC inventory. No build, admission marker or mutation."""
import os,json,time,signal,resource,pathlib
resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20))
signal.alarm(25)
started=time.monotonic();root=pathlib.Path('/sys/fs/cgroup');reads=0;rows=[]
def read(p):
 global reads
 with p.open('rb') as f:
  data=f.read(131073)
 if len(data)>131072:raise RuntimeError('file bound exceeded')
 reads+=len(data)
 if reads>8*2**20:raise RuntimeError('total read bound exceeded')
 return data.decode().strip()
def walk(p):
 if len(rows)>=8192:raise RuntimeError('cgroup bound exceeded')
 row={'path':str(p.relative_to(root))}
 for name in ['cgroup.events','memory.current','memory.max','memory.high','memory.swap.max']:
  if (p/name).exists():row[name]=read(p/name)
 rows.append(row)
 entries=sorted(p.iterdir())
 for q in entries:
  if q.is_dir():
   if q.is_symlink():raise RuntimeError('symlink cgroup')
   walk(q)
try:
 mem={}
 for line in read(pathlib.Path('/proc/meminfo')).splitlines():
  k,v=line.split(':',1)
  if k in ['MemTotal','MemAvailable','SwapTotal','SwapFree']:mem[k]=v.strip()
 walk(root)
 print(json.dumps(dict(status='INVENTORY_ONLY',timestamp=time.time(),memory=mem,cgroups=rows,bytes_read=reads,wall_seconds=time.monotonic()-started,build_launched=False)))
except Exception as e:
 print(json.dumps(dict(status='DENY_INCOMPLETE_INVENTORY',error=repr(e),groups_seen=len(rows),build_launched=False)))
 raise SystemExit(2)
