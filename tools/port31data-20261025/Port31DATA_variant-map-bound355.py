#!/usr/bin/env python3
"""Measured noncompiler supervisor:512MiB aggregate,540s, no Lean invocation."""
import json,os,pathlib,re,signal,subprocess,sys,time
from Port31DATA_run import T,E,pin
mode='variant-map';assert len(sys.argv)==1
src=T/f'Port31DATA_{mode}355.py';rec=E/f'Port31DATA_{mode}-processor355.json';assert not rec.exists()
cmd=['/usr/bin/time','-l',sys.executable,'-B',str(src)]
r=dict(command=cmd,source=pin(src),launcher=pin(__file__),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),lean_calls=0,axioms='N/A: noncompiler')
start=time.monotonic();peak=0;stop=None
with (E/f'Port31DATA_{mode}-processor355.stdout.log').open('xb') as o,(E/f'Port31DATA_{mode}-processor355.time.log').open('xb') as e:
 p=subprocess.Popen(cmd,stdout=o,stderr=e,start_new_session=True)
 while p.poll() is None:
  rows=[tuple(map(int,l.split())) for l in subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True).splitlines()];ids={p.pid}
  while True:
   nxt=ids|{pid for pid,parent,rss in rows if parent in ids}
   if nxt==ids:break
   ids=nxt
  rss=sum(rss*1024 for pid,parent,rss in rows if pid in ids);peak=max(peak,rss)
  if rss>=512*1024**2 or time.monotonic()-start>=540:
   stop='512MiB/540s';os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.1)
 code=p.wait()
tim=(E/f'Port31DATA_{mode}-processor355.time.log').read_text()
r.update(exit_status=code,wall_seconds=time.monotonic()-start,aggregate_peak_rss_bytes=peak,stopped=stop)
for suffix,key in [('maximum resident set size','peak_process_rss_bytes'),('swaps','swaps')]:
 m=re.search(r'^\s*(\d+)\s+'+suffix+r'\s*$',tim,re.M);r[key]=int(m[1]) if m else None
r['logs']=[pin(E/f'Port31DATA_{mode}-processor355.stdout.log'),pin(E/f'Port31DATA_{mode}-processor355.time.log')]
rec.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r));sys.exit(code)
