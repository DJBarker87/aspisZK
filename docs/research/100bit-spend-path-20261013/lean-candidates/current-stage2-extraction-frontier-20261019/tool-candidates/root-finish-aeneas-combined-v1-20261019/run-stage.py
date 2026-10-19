from pathlib import Path
import hashlib,json,os,signal,subprocess,time
W=Path(__file__).resolve().parent;G=2**30
name='aspis-finish-combined-build-v1-20261019';image='sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7'
E=W/'build-evidence';E.mkdir();cidfile=E/'cid';stopped=False
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().strip()[3:].lstrip('/')
assert (cg/'memory.max').read_text().strip()==str(G) and (cg/'memory.swap.max').read_text().strip()=='0'
args=['docker','run','--rm','--name',name,'--cidfile',str(cidfile),'--memory',str(4*G),'--memory-swap',str(4*G),'--cpus','2','--pids-limit','256','--user','1000:1000','--mount','type=bind,src='+str(W)+',dst=/work','--workdir','/work/src','--entrypoint','opam',image,'exec','--','dune','build','--profile','release','-j','2','main.exe']
(E/'command.json').write_text(json.dumps({'argv':args,'expected_time':'incremental optimized OCaml compilation of isolated existing source fixes; no arithmetic/proof gate','own_scope_memory_max':G,'docker_memory_max':4*G,'docker_swap_max':0,'image':image},indent=2)+'\n')
def onstop(*_):
 global stopped
 stopped=True
signal.signal(signal.SIGTERM,onstop);signal.signal(signal.SIGINT,onstop)
start=time.monotonic();peak=sw=0;ext=None;timeout=False
with (E/'stdout.log').open('x') as log:
 p=subprocess.Popen(['/usr/bin/time','-v','-o',str(E/'time.log'),*args],stdout=log,stderr=subprocess.STDOUT)
 try:
  while p.poll() is None:
   if ext is None and cidfile.exists():
    cid=cidfile.read_text().strip()
    if cid:
     r=subprocess.run(['docker','inspect','--format','{{.State.Pid}}',cid],text=True,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
     if r.returncode==0 and r.stdout.strip().isdigit() and int(r.stdout)>0:
      pcg=Path('/proc')/r.stdout.strip()/'cgroup'
      if pcg.exists():
       ext=Path('/sys/fs/cgroup')/pcg.read_text().strip()[3:].lstrip('/')
       limits={n:(ext/n).read_text().strip() for n in ['memory.max','memory.swap.max']};assert limits=={'memory.max':str(4*G),'memory.swap.max':'0'},limits
       (W/'docker-registered.json').write_text(json.dumps({'cgroup':str(ext),'limits':limits,'container':cid,'registered_ns':time.time_ns()},indent=2)+'\n')
   if ext is not None and ext.exists():
    peak=max(peak,int((ext/'memory.peak').read_text()));sw=max(sw,int((ext/'memory.swap.current').read_text()))
   if stopped or time.monotonic()-start>180:
    timeout=not stopped;subprocess.run(['docker','kill',name],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL);break
   time.sleep(.1)
 finally:
  if p.poll() is None:
   try:p.wait(timeout=5)
   except subprocess.TimeoutExpired:subprocess.run(['docker','kill',name],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL);p.terminate();p.wait()
status=p.wait();obj=W/'src/_build/default/main.exe';rec={'exit_status':status,'wall_seconds':round(time.monotonic()-start,3),'docker_memory_peak_bytes':peak,'docker_swap_peak_bytes':sw,'timeout':timeout,'stopped':stopped,'object_sha256':hashlib.sha256(obj.read_bytes()).hexdigest() if status==0 and obj.exists() else None}
(E/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True);raise SystemExit(status)
