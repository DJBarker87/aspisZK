"""Single authorized local359; text/data --check never invokes a compiler."""
import datetime,fcntl,hashlib,json,os,pathlib,re,resource,signal,subprocess,sys,time
from zoneinfo import ZoneInfo
T=pathlib.Path(__file__).resolve().parent;ROOT=T.parents[1];E=ROOT/'evidence/port33interface-20261025'
def pin(p):
 p=pathlib.Path(p);h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return dict(path=str(p),bytes=p.stat().st_size,sha256=h.hexdigest())
def safe(p):
 p=pathlib.Path(p)
 for a in [p,*p.parents]: assert not a.is_symlink(),str(a)
 assert p.is_file() and p.stat().st_uid==501
 return p
def validate():
 start=time.monotonic();assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/cx-port33-interface-20261025'
 plan=json.loads((E/'Port33INTERFACE_plan.json').read_text());pre=json.loads((E/'Port33INTERFACE_reused-preflight.json').read_text())
 inputs=[]
 for f in plan['files']:
  x=pin(safe(f['path']));assert all(x[k]==f[k] for k in x);inputs.append(x)
 runtime=pre['runtime']
 for f in runtime:assert pin(safe(f['path']))==f
 base=pathlib.Path(pre['sysroot'])/'src/lean'
 api=[pin(base/p) for p in ['Lean/Environment.lean','Lean/Replay.lean','Lean/Declaration.lean','Lean/Expr.lean','Lean/Data/SMap.lean','Lean/Util/FoldConsts.lean']]
 src=(T/'Port33INTERFACE_Diagnostic.lean').read_text()
 assert [l for l in src.splitlines() if l.startswith('import ')]==['import Lean']
 for banned in ['#eval!','unsafeCast','doCheck := false','maxHeartbeats','maxRecDepth','region.free','setEnv ','addDeclWithoutChecking','sorry','admit','native_decide']:
  assert banned not in src,banned
 assert 'k.addDeclCore 0' in src and 'strictDeclaration c check.1.constants[i]!' in src
 assert 'PORT33_COMPLETE' in src
 files=[pin(p) for p in sorted(T.iterdir()) if p.is_file()]+[pin(E/('Port33INTERFACE_'+n)) for n in ['CRITERIA.md','DESIGN.md','plan.json']]
 r=dict(status='PASS text/data preflight; no compiler',inputs=inputs,runtime=runtime,api=api,files=files,sysroot=pre['sysroot'],inventory_assessment='355 inventory SHA reused; no new identity gate',lean_calls=0,exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap)
 assert r['peak_rss_bytes']<512*1024**2
 return r
if sys.argv[1:]==['--check']:
 r=validate();(E/'Port33INTERFACE_preflight.json').write_text(json.dumps(r,indent=2)+'\n');print({k:r[k] for k in ['status','wall_seconds','peak_rss_bytes']});sys.exit()
assert sys.argv[1:]==['359']
receipt=E/'Port33INTERFACE_attempt-359.json';assert not receipt.exists()
lock=pathlib.Path('/private/tmp/aspis-local-lean.lock.d')
try:lock.mkdir(mode=0o700)
except FileExistsError:print('WAIT local lock busy; uncharged');sys.exit(2)
gl=None
try:
 (lock/'Port33INTERFACE-owner.json').write_text(json.dumps(dict(pid=os.getpid(),branch='codex/cx-port33-interface-20261025')))
 assert not subprocess.run(['pgrep','-ifl','(^|/)(lean|lake)( |$)'],capture_output=True,text=True).stdout.strip(),'other Lean/lake; no charge'
 now=datetime.datetime.now(ZoneInfo('Europe/London'))
 if 14<=now.hour<22 or now.hour==22 and now.minute<30:
  gl=open('/private/tmp/aspis-r0-lean.lock','a');fcntl.flock(gl,fcntl.LOCK_EX|fcntl.LOCK_NB)
 fresh=validate();old=json.loads((E/'Port33INTERFACE_preflight.json').read_text())
 for k in ['inputs','runtime','api','files']:assert fresh[k]==old[k],k
 assert not subprocess.check_output(['git','status','--porcelain','--',str(T)],text=True).strip(),'source not committed'
 paths=[x['path'] for x in fresh['inputs']+fresh['runtime']+fresh['api']]
 lf=subprocess.run(['/usr/sbin/lsof','-F','pan','--',*paths],capture_output=True,text=True)
 (E/'Port33INTERFACE_lsof-359.log').write_text(lf.stdout+lf.stderr)
 assert lf.returncode in [0,1] and not any(l in ['aw','au'] for l in lf.stdout.splitlines()),'writer'
 src=T/'Port33INTERFACE_Diagnostic.lean';cmd=['/usr/bin/time','-l',fresh['sysroot']+'/bin/lean','-j1','-M4400','-DElab.async=false','-R',str(T),str(src)]
 env=os.environ.copy();env['LEAN_PATH']=fresh['sysroot']+'/lib/lean'
 r=dict(status='CHARGED BEFORE LAUNCH',actual_after_charge=359,global_ceiling=368,remaining=9,reserved_consumers=2,carry=7,job_calls=1,job_max=1,private_budgets_unchanged=True,other_budgets=0,command=cmd,environment=dict(LEAN_PATH=env['LEAN_PATH']),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source=pin(src),preflight=pin(E/'Port33INTERFACE_preflight.json'),fresh=fresh,admission=dict(owned_local_lock=True,no_other_lean=True,global_lock_required=gl is not None,host='N/A no host authority'),default_heartbeat_recDepth=True,deadline_seconds=540,aggregate_limit_bytes=8*1024**3)
 receipt.write_text(json.dumps(r,indent=2)+'\n');start=time.monotonic();peak=0;stop=None
 with (E/'Port33INTERFACE_stdout-359.log').open('xb') as o,(E/'Port33INTERFACE_time-359.log').open('xb') as e:
  p=subprocess.Popen(cmd,env=env,cwd=T,stdout=o,stderr=e,start_new_session=True)
  while p.poll() is None:
   rows=[tuple(map(int,l.split())) for l in subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True).splitlines()];ids={p.pid}
   while True:
    nxt=ids|{pid for pid,parent,rss in rows if parent in ids}
    if nxt==ids:break
    ids=nxt
   rss=sum(rss*1024 for pid,parent,rss in rows if pid in ids);peak=max(peak,rss)
   if rss>=8*1024**3 or time.monotonic()-start>=540:
    stop='aggregate8GiB/deadline540s';os.killpg(p.pid,signal.SIGKILL);break
   time.sleep(.1)
  code=p.wait()
 log=(E/'Port33INTERFACE_stdout-359.log').read_text();tim=(E/'Port33INTERFACE_time-359.log').read_text()
 r.update(exit_status=code,wall_seconds=time.monotonic()-start,sampled_aggregate_peak_rss_bytes=peak,stopped=stop,post_hash_unchanged=all(pin(x['path'])==x for x in fresh['inputs']+fresh['runtime']+fresh['api']),stdout=pin(E/'Port33INTERFACE_stdout-359.log'),time_log=pin(E/'Port33INTERFACE_time-359.log'),axioms='Raw IO N/A. Synthetic kernel walk in complete stdout. Query31 not checked.')
 for suffix,k in [('maximum resident set size','peak_process_rss_bytes'),('swaps','swaps')]:
  m=re.search(r'^\s*(\d+)\s+'+suffix+r'\s*$',tim,re.M);r[k]=int(m[1]) if m else None
 out=pathlib.Path('/private/tmp/Port33INTERFACE-20261025')
 r['outputs']=[pin(x) for x in sorted(out.iterdir()) if x.is_file()] if out.exists() else []
 r['accepted_diagnostic']=code==0 and 'error:' not in log and 'PANIC' not in log and 'PORT33_COMPLETE' in log and r['post_hash_unchanged']
 r['status']='FINISHED; NO SECOND CALL';receipt.write_text(json.dumps(r,indent=2)+'\n')
 print({k:r[k] for k in ['exit_status','wall_seconds','sampled_aggregate_peak_rss_bytes','peak_process_rss_bytes','swaps','accepted_diagnostic']})
finally:
 if gl:gl.close()
 (lock/'Port33INTERFACE-owner.json').unlink();lock.rmdir()
