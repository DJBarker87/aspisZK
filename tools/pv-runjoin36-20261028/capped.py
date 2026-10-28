"""Run exactly one extraction phase in the admitted scope and retain its metrics."""
import pathlib,sys,json,subprocess,time,resource,hashlib,os
w=pathlib.Path(sys.argv[1]);phase=sys.argv[2];spec=json.load(open(w/(phase+'-command.json')));out=w/phase;out.mkdir(exist_ok=False)
cg=pathlib.Path('/sys/fs/cgroup')/pathlib.Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
controls={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']};assert controls==dict(zip(controls,[str(6*2**30),str(8*2**30),'0','64']))
start=time.monotonic();env=dict(os.environ,**spec.get('env',{}));rss=0
with (out/'out.log').open('w') as f:
 p=subprocess.Popen(spec['command'],cwd=spec['cwd'],env=env,stdout=f,stderr=subprocess.STDOUT)
 while p.poll() is None:
  total=0
  for n in (cg/'cgroup.procs').read_text().split():
   try:
    for line in pathlib.Path('/proc',n,'status').read_text().splitlines():
     if line.startswith('VmRSS:'):total+=int(line.split()[1])*1024
   except (FileNotFoundError,ProcessLookupError):pass
  rss=max(rss,total);time.sleep(.1)
u=resource.getrusage(resource.RUSAGE_CHILDREN)
receipt=dict(**spec,exit=p.returncode,wall_seconds=time.monotonic()-start,peak_aggregate_rss_bytes=rss,peak_child_rss_bytes=u.ru_maxrss*1024,swaps=u.ru_nswap,cgroup_memory_peak_bytes=(cg/'memory.peak').read_text().strip(),swap_peak_bytes=(cg/'memory.swap.peak').read_text().strip(),controls=controls,axioms='N/A: extraction/metadata, no theorem accepted',output_sha256=hashlib.sha256((out/'out.log').read_bytes()).hexdigest())
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['exit','wall_seconds','peak_aggregate_rss_bytes','swaps']}));sys.exit(p.returncode)
