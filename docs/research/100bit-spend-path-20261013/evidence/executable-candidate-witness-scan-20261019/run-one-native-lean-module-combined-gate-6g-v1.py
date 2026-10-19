import datetime, hashlib, json, pathlib, subprocess, sys, time, shlex
from zoneinfo import ZoneInfo
G=1024**3; HOST_MIN=62*G; FINITE_LIMIT=48*G; OS_GROWTH_RESERVE=8*G
CFG=pathlib.Path(sys.argv[1]); c=json.loads(CFG.read_text())
UNIT=c['unit']; CAP=6*G; ATT=pathlib.Path(c['attempt']); SRC=pathlib.Path(c['source']); SRC_SHA=c['source_sha256']; MODULE=c['module']; ROOT=ATT/'objects'
ENVIRONMENT=pathlib.Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/environment-base.json')
LEAN=pathlib.Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'); COLLECTOR=pathlib.Path('/tmp/collect-nuc-cgroups-review.py'); COLLECTOR_SHA='4fc152ea4f88742fb460c301ae17446f1d1ba9162acdaafb37d80e60c4907800'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def need(ok,msg):
 if not ok: raise SystemExit('preflight refused: '+msg)
def inventory():
 d=json.loads(subprocess.run(['python3',str(COLLECTOR)],check=True,capture_output=True,text=True).stdout)
 effective=[r for r in d['effective_reservation_nodes'] if pathlib.Path(r['path']).name!=UNIT+'.scope']; finite=[pathlib.Path(r['path']) for r in effective]
 unbounded=[r for r in d['all_populated_cgroups'] if r['scope'] and r['max']=='max' and pathlib.Path(r['path']).name!=UNIT+'.scope']; outer=[]
 for r in unbounded:
  p=pathlib.Path(r['path'])
  if any(q==p or q in p.parents for q in finite): continue
  if any(p in pathlib.Path(s['path']).parents for s in unbounded if s is not r): continue
  outer.append(r)
 return {'timestamp_utc':d['timestamp_utc'],'MemTotal_bytes':int(d['MemTotal_kB'])*1024,'MemAvailable_bytes':int(d['MemAvailable_kB'])*1024,'effective_finite_sum_bytes':sum(int(r['max']) for r in effective),'candidate_job_cap_bytes':CAP,'finite_plus_job_bytes':sum(int(r['max']) for r in effective)+CAP,'uncapped_outermost_current_bytes':sum(int(r['current_bytes'] or 0) for r in outer),'uncapped_outermost_scopes':outer,'effective_reservation_nodes':effective,'excluded_own_scope':UNIT+'.scope','collector_source_sha256':COLLECTOR_SHA}
def gate(d,start):
 need(d['MemTotal_bytes']>=HOST_MIN,'host MemTotal <62 GiB'); need(d['finite_plus_job_bytes']<=FINITE_LIMIT,'finite caps+job >48 GiB'); need(d['finite_plus_job_bytes']+d['uncapped_outermost_current_bytes']+OS_GROWTH_RESERVE<=d['MemTotal_bytes'],'combined finite caps + uncapped current + 8 GiB reserve > MemTotal'); need(d['MemAvailable_bytes']>=(14 if start else 6)*G,'MemAvailable below gate'); d['combined_host_reservation_bytes']=d['finite_plus_job_bytes']+d['uncapped_outermost_current_bytes']+OS_GROWTH_RESERVE; d['OS_growth_reserve_bytes']=OS_GROWTH_RESERVE; return d
def cgown():
 for p in pathlib.Path('/sys/fs/cgroup').rglob('memory.max'):
  if p.parent.name==UNIT+'.scope': return p.parent
def resolve(m,roots):
 rel=pathlib.Path(*m.split('.'))
 for root in roots:
  q=(root/rel).with_suffix('.olean')
  if q.is_file(): return q
 return None
def main():
 mins=datetime.datetime.now(ZoneInfo('Europe/London')).hour*60+datetime.datetime.now(ZoneInfo('Europe/London')).minute
 need(mins>=1350 or mins<360,'overnight authorization window closed'); need(sha(SRC)==SRC_SHA,'frozen source mismatch '+str(SRC)); need(sha(COLLECTOR)==COLLECTOR_SHA,'collector mismatch')
 env=json.loads(ENVIRONMENT.read_text()); need(env['LEAN_GITHASH']=='8c9756b28d64dab099da31a4c09229a9e6a2ef35','Lean commit mismatch')
 attempt_roots=[pathlib.Path(x) for x in c['import_roots']]; roots=[ROOT]+attempt_roots+[pathlib.Path(x) for x in env['LEAN_PATH'].split(':')]
 direct={}
 for dep,expected in c['direct_imports'].items():
  p=resolve(dep,roots); need(p is not None,'direct import missing '+dep); actual=sha(p); need(actual==expected,'direct import hash mismatch '+dep+': '+actual); direct[dep]={'path':str(p),'sha256':actual}
 pre=gate(inventory(),True); need(not ATT.exists(),'attempt already exists: '+str(ATT)); ATT.mkdir(mode=0o700); ROOT.mkdir(mode=0o700)
 lp=':'.join([str(ROOT)]+[str(x) for x in attempt_roots]+env['LEAN_PATH'].split(':'))
 obj=ROOT/(MODULE+'.olean'); argv=['/usr/bin/env','LEAN_PATH='+lp,str(LEAN),'-M','5500','-DElab.async=false','-R','/tmp','-o',str(obj),str(SRC)]
 doc={'target':MODULE,'source':str(SRC),'source_sha256':SRC_SHA,'source_revision':c['source_revision'],'object':str(obj),'Lean':str(LEAN),'Lean_sha256':sha(LEAN),'Lean_commit':env['LEAN_GITHASH'],'environment_sha256':sha(ENVIRONMENT),'LEAN_PATH':lp,'direct_imports':direct,'resource_policy':{'MemoryHigh':'4G','MemoryMax':'6G','MemorySwapMax':'0','Lean_MiB':5500,'timeout_seconds':120,'admission_inventory':pre}}
 (ATT/'preflight.json').write_text(json.dumps(doc,indent=2)+'\n'); (ATT/'import-pins.json').write_text(json.dumps(direct,indent=2)+'\n')
 timed=['/usr/bin/time','-v','-o',str(ATT/'time.log')]+argv; shell=shlex.join(timed)+' > '+shlex.quote(str(ATT/'lean.log'))+' 2>&1'
 wrapped=['systemd-run','--user','--scope','--quiet','--unit='+UNIT,'-p','MemoryHigh=4G','-p','MemoryMax=6G','-p','MemorySwapMax=0','-p','TasksMax=128','/bin/bash','-lc',shell]
 (ATT/'command.json').write_text(json.dumps({'argv':wrapped,'lean_argv':argv,'timeout_seconds':120},indent=2)+'\n')
 start=time.monotonic(); proc=subprocess.Popen(wrapped); peak=swpeak=0; last=0; aborted=None
 with (ATT/'watcher.jsonl').open('x') as f:
  while proc.poll() is None:
   try:
    cg=cgown(); cur=cp=sw=None
    if cg: cur=int((cg/'memory.current').read_text()); cp=int((cg/'memory.peak').read_text()); sw=int((cg/'memory.swap.current').read_text()); peak=max(peak,cp); swpeak=max(swpeak,sw)
    row={'elapsed_s':round(time.monotonic()-start,3),'own_memory_current':cur,'own_memory_peak':cp,'own_swap_current':sw}
    if time.monotonic()-last>=.5: row['inventory']=gate(inventory(),False); last=time.monotonic()
    f.write(json.dumps(row)+'\n'); f.flush()
   except BaseException as e:
    aborted='watcher_gate_or_error:'+repr(e); subprocess.run(['systemctl','--user','kill','--kill-who=all',UNIT+'.scope'],check=False); break
   if time.monotonic()-start>120: aborted='timeout_120s'; subprocess.run(['systemctl','--user','kill','--kill-who=all',UNIT+'.scope'],check=False); break
   time.sleep(.05)
  status=proc.wait(); cg=cgown()
  if cg: peak=max(peak,int((cg/'memory.peak').read_text())); swpeak=max(swpeak,int((cg/'memory.swap.current').read_text()))
 receipt={'target':MODULE,'source_sha256':SRC_SHA,'source_revision':c['source_revision'],'exit_status':status,'wall_seconds':round(time.monotonic()-start,3),'watchdog_abort':aborted,'object_sha256':sha(obj) if obj.exists() else None,'cgroup_memory_peak_bytes_sampled':peak,'cgroup_swap_peak_bytes_sampled':swpeak,'attempt':str(ATT),'admission_inventory':pre,'controller_sha256':sha(pathlib.Path(__file__))}
 (ATT/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n'); print(json.dumps(receipt),flush=True); raise SystemExit(status)
if __name__=='__main__': main()
