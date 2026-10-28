#!/usr/bin/env python3
"""Record one already-capped native verification command inside its scope."""
import datetime,hashlib,json,os,pathlib,re,resource,subprocess,sys,time
out=pathlib.Path(sys.argv[1]); command=sys.argv[2:];out.mkdir(parents=True,exist_ok=True)
os.chdir(os.environ['PV8_SOURCE_DIR'])
cgroup=pathlib.Path('/sys/fs/cgroup')/pathlib.Path('/proc/self/cgroup').read_text().strip().split('::',1)[1].lstrip('/')
controls={n:(cgroup/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max']}
assert controls=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'},controls
temporary=out/'tmp';temporary.mkdir(exist_ok=True);os.environ['TMPDIR']=str(temporary.resolve())
expected=os.environ.get('PV_L2C_EXPECTED_TIME','Optimized compilation, then bounded scalar control verification')
started=time.monotonic()
peak_rss=0
with (out/'out.log').open('w') as log:
 r=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT)
 while True:
  aggregate=0
  for pid in (cgroup/'cgroup.procs').read_text().split():
   try:
    status=pathlib.Path('/proc',pid,'status').read_text()
    m=re.search(r'^VmRSS:\s+(\d+) kB',status,re.M)
    if m:aggregate+=int(m[1])*1024
   except (FileNotFoundError,ProcessLookupError):pass
  peak_rss=max(peak_rss,aggregate)
  if r.poll() is not None:break
  time.sleep(.1)
wall=time.monotonic()-started;u=resource.getrusage(resource.RUSAGE_CHILDREN)
peak=int((cgroup/'memory.peak').read_text());swap=(cgroup/'memory.swap.peak').read_text().strip() if (cgroup/'memory.swap.peak').exists() else None
files=os.environ.get('PV_L2C_PIN_FILES','Cargo.toml:Cargo.lock:lib.rs:control_cut.rs:host_forest.rs').split(':')
pins={p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest() for p in files}
record=dict(target=command,exit=r.returncode,wall_seconds=wall,peak_rss_bytes=peak_rss,rusage_child_rss_max_bytes=u.ru_maxrss*1024,cgroup_peak_bytes=peak,swaps=u.ru_nswap,scope_swap_peak_bytes=swap,controls=controls,cgroup=str(cgroup),expected_time=expected,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_sha256=pins,axioms=os.environ.get('PV_L2C_EVIDENCE_CLASS','N/A: Kani source verification'),stubs=[])
removed=[]
for p in temporary.rglob('*'):
 if p.is_file() and (p.name.startswith(('external-sat','smt2_dec_problem')) or p.suffix in ['.cnf','.smt2']):
  removed.append(dict(name=p.name,size=p.stat().st_size));p.unlink()
record['removed_owned_solver_temps']=removed
(out/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
sys.exit(r.returncode)
