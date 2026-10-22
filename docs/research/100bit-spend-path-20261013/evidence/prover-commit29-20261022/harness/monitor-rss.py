"""Read-only live scope RSS sampling; never includes another task's scope."""
import sys,time,json,hashlib,os
from pathlib import Path
pid,name=sys.argv[1:3]
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit29-20261022')
proc=Path('/proc')/pid;cmd=proc.joinpath('cmdline').read_bytes()
assert str(H).encode() in cmd
cg=Path('/sys/fs/cgroup'+proc.joinpath('cgroup').read_text().split('0::',1)[1].strip())
out=H/'monitor'/name;out.mkdir(parents=True,exist_ok=False)
programs={}
for arg in cmd.split(b'\0'):
 p=Path(os.fsdecode(arg))
 if arg.endswith(b'.out') and p.exists():programs[str(p)]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size_bytes':p.stat().st_size}
start=time.monotonic();peak=0;swap_peak=0;count=0;memory_peak=0
with (out/'samples.jsonl').open('w') as f:
 while proc.exists() and proc.joinpath('cmdline').read_bytes()==cmd:
  rss=swap=0
  try:
   for member in (cg/'cgroup.procs').read_text().split():
    try:
     status=(Path('/proc')/member/'status').read_text()
     for line in status.splitlines():
      if line.startswith('VmRSS:'):rss+=int(line.split()[1])
      if line.startswith('VmSwap:'):swap+=int(line.split()[1])
    except OSError:pass
   memory_peak=max(memory_peak,int((cg/'memory.peak').read_text()))
  except OSError:break
  peak=max(peak,rss);swap_peak=max(swap_peak,swap);count+=1
  f.write(json.dumps(dict(elapsed_seconds=round(time.monotonic()-start,3),scope_rss_kib=rss,scope_swap_kib=swap,cgroup_memory_peak_bytes=memory_peak))+'\n');f.flush()
  if count==1 or count%60==0:print(name, count, rss,flush=True)
  time.sleep(1)
result=dict(pid=int(pid),command=cmd.decode().replace('\0',' '),cgroup=str(cg),programs=programs,observed_peak_scope_rss_kib=peak,observed_peak_swap_kib=swap_peak,observed_cgroup_memory_peak_bytes=memory_peak,samples=count,scope='from monitor attachment until exit; observed RSS is a lower bound for full-lifetime peak')
(out/'summary.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
