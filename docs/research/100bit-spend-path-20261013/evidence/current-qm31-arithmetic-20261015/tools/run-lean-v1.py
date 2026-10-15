import hashlib,json,os,re,signal,subprocess,sys,time
from pathlib import Path
root=Path('/tmp/aspis-r1-qm31-arithmetic-20261015');base=root/'attempt-a'
backend=Path('/Users/dominic/ZK/external/aeneas/aeneas-verif-workspace/aeneas/backends/lean')
objects=root/'objects';objects.mkdir(exist_ok=True)
attempts=root/'lean-attempts';attempts.mkdir(exist_ok=True)
module,label=sys.argv[1:];assert re.fullmatch(r'[A-Za-z0-9.]+',module);assert re.fullmatch(r'[a-z0-9-]+',label)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
src=base/'generated'/(module.replace('.','/')+'.lean');obj=objects/(module.replace('.','/')+'.olean')
assert src.is_file();assert not obj.exists();assert not list(attempts.glob(label+'.*'))
obj.parent.mkdir(parents=True,exist_ok=True)
(attempts/(label+'.source.lean')).write_bytes(src.read_bytes())
imports=[]
for imp in re.findall(r'^import (\S+)',src.read_text(),re.M):
 rel=imp.replace('.','/')+'.olean'
 candidates=[objects/rel,backend/'.lake/build/lib/lean'/rel,backend/'.lake/packages/mathlib/.lake/build/lib/lean'/rel]
 pin=next((p for p in candidates if p.is_file()),None);assert pin,('missing direct import',imp)
 imports.append({'module':imp,'path':str(pin),'sha256':sha(pin)})
cmd=['/Users/dominic/.elan/bin/lake','env','python3','/tmp/aspis-root-local-semantic-20261015/lean-with-cache.py',str(objects),'-M3000','-R',str(base/'generated'),'-o',str(obj),str(src)]
pre={'target':module,'label':label,'source_sha256':sha(src),'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd='/Users/dominic/ZK/.worktrees/100bit-spend-path',text=True).strip(),'direct_imports':imports,'lean_toolchain':(backend/'lean-toolchain').read_text().strip(),'command':cmd,'runner_sha256':sha(Path(__file__))}
(attempts/(label+'.preflight.json')).write_text(json.dumps(pre,indent=2)+'\n')
start=time.monotonic();peak=0;killed=False
with (attempts/(label+'.log')).open('x') as log:
 p=subprocess.Popen(['/usr/bin/time','-l',*cmd],cwd=backend,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  ps=subprocess.check_output(['ps','-axo','pid=,pgid=,rss='],text=True)
  rss=sum(int(z[2]) for line in ps.splitlines() if len(z:=line.split())==3 and int(z[1])==p.pid);peak=max(peak,rss)
  if rss>4*1024*1024 or time.monotonic()-start>300:
   killed=True;os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(.1)
 code=p.wait()
rec={**pre,'exit_status':code,'wall_seconds':round(time.monotonic()-start,3),'peak_aggregate_process_group_rss_kib_sampled':peak,'lean_memory_limit_mb':3000,'stop_threshold_kib':4*1024*1024,'timeout_seconds':300,'killed_for_memory_or_timeout':killed,'object_sha256':sha(obj) if obj.exists() else None,'note':'Focused local cached-library check, no lake build/dependency replay, no cgroup. Process swaps in log.'}
(attempts/(label+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec));raise SystemExit(code)
