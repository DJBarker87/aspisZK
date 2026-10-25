"""Two charged focused local calls at most. No host/remote/build-system use."""
import datetime,fcntl,hashlib,json,os,pathlib,re,resource,signal,subprocess,sys,time
from zoneinfo import ZoneInfo
T=pathlib.Path(__file__).resolve().parent;ROOT=T.parents[1];E=ROOT/'evidence/port35anchor-20261025';O=pathlib.Path('/private/tmp/Port35ANCHOR-20261025')
def pin(p):
 p=pathlib.Path(p);h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return dict(path=str(p),bytes=p.stat().st_size,sha256=h.hexdigest())
def validate():
 start=time.monotonic();assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/cx-port35-anchor-20261025'
 j=json.loads((E/'Port35ANCHOR_inputs.json').read_text())
 for k in ['inputs','runtime','api']:
  for p in j[k]:assert pin(p['path'])==p,p['path']
 for k in ['selection','groups']:assert pin(j[k]['path'])==j[k]
 s=(T/'Port35ANCHOR_Repair.lean').read_text()
 assert [l for l in s.splitlines() if l.startswith('import ')]==['import Lean']
 for b in ['#eval','unsafeCast','doCheck := false','maxRecDepth','maxHeartbeats','setEnv','ofKernelEnv','addDeclWithoutChecking','native_decide','sorry','admit','region.free','mkPrivateName','addDeclCore 0']:
  assert b not in s,b
 assert 'Lean.Elab.Command.liftIO (Port35ANCHOR.run core)' in s
 assert not re.search(r'`[^\s,]*\.\d',s)
 assert s.count('addDeclCore (Core.getMaxHeartbeats {}).toUSize')==3
 r=dict(status='PASS scoped source/API/data preflight; no CLI',inputs=j['inputs'],runtime=j['runtime'],api=j['api'],sysroot=j['sysroot'],files=[pin(p) for p in sorted(T.iterdir()) if p.is_file()]+[pin(E/f) for f in ['Port35ANCHOR_inputs.json','Port35ANCHOR_selection.json','Port35ANCHOR_groups.json','Port35ANCHOR_CRITERIA.md']],wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,lean_calls=0)
 assert r['peak_rss_bytes']<512*1024**2
 return r
if sys.argv[1:]==['--check']:
 r=validate();(E/'Port35ANCHOR_preflight.json').write_text(json.dumps(r,indent=2)+'\n');print({k:r[k] for k in ['status','wall_seconds','peak_rss_bytes']});sys.exit()
assert len(sys.argv)==2 and sys.argv[1] in ['362','363'];call=int(sys.argv[1]);receipt=E/f'Port35ANCHOR_attempt-{call}.json';assert not receipt.exists()
if call==363:
 prev=json.loads((E/'Port35ANCHOR_attempt-362.json').read_text());assert prev['exit_status']!=0 or not (O/'Port35ANCHOR-result.json').exists()
 assert pin(T/'Port35ANCHOR_Repair.lean')['sha256']!=prev['source']['sha256'],'no unchanged rerun'
lock=pathlib.Path('/private/tmp/aspis-local-lean.lock.d');lock.mkdir(mode=0o700);gl=None
try:
 (lock/'Port35ANCHOR-owner.json').write_text(json.dumps(dict(pid=os.getpid(),branch='codex/cx-port35-anchor-20261025')))
 assert not subprocess.run(['pgrep','-ifl','(^|/)(lean|lake)( |$)'],capture_output=True,text=True).stdout.strip(),'other Lean/lake; no charge'
 now=datetime.datetime.now(ZoneInfo('Europe/London'))
 if 14<=now.hour<22 or now.hour==22 and now.minute<30:
  gl=open('/private/tmp/aspis-r0-lean.lock','a');fcntl.flock(gl,fcntl.LOCK_EX|fcntl.LOCK_NB)
 fresh=validate();old=json.loads((E/'Port35ANCHOR_preflight.json').read_text())
 for k in ['inputs','runtime','api','files']:assert fresh[k]==old[k],k
 assert not subprocess.check_output(['git','status','--porcelain','--',str(T)],text=True).strip(),'uncommitted tools'
 paths=[x['path'] for x in fresh['inputs']+fresh['runtime']+fresh['api']]
 lf=subprocess.run(['/usr/sbin/lsof','-F','pan','--',*paths],capture_output=True,text=True);(E/f'Port35ANCHOR_lsof-{call}.log').write_text(lf.stdout+lf.stderr)
 assert lf.returncode in [0,1] and not any(l in ['aw','au'] for l in lf.stdout.splitlines()),'writer'
 src=T/'Port35ANCHOR_Repair.lean';cmd=['/usr/bin/time','-l',fresh['sysroot']+'/bin/lean','-j1','-M4400','-DElab.async=false','-R',str(T),str(src)]
 env=os.environ.copy();env['LEAN_PATH']=fresh['sysroot']+'/lib/lean'
 r=dict(status='CHARGED BEFORE LAUNCH',actual_after_charge=call,global_ceiling=368,remaining=368-call,reserved_consumers=2,carry=366-call,job_calls=call-361,job_max=2,private_budgets_unchanged=True,other_budgets=0,command=cmd,environment=dict(LEAN_PATH=env['LEAN_PATH']),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source=pin(src),preflight=pin(E/'Port35ANCHOR_preflight.json'),fresh=fresh,admission=dict(owned_local_lock=True,no_other_lean=True,global_lock_required=gl is not None,host='NONE; zero host budget'),default_limits=True,deadline_seconds=540,aggregate_limit_bytes=8*1024**3)
 receipt.write_text(json.dumps(r,indent=2)+'\n');(E/f'Port35ANCHOR_executed-{call}.lean.txt').write_bytes(src.read_bytes());start=time.monotonic();peak=0;stop=None
 with (E/f'Port35ANCHOR_stdout-{call}.log').open('xb') as o,(E/f'Port35ANCHOR_time-{call}.log').open('xb') as e:
  p=subprocess.Popen(cmd,env=env,cwd=T,stdout=o,stderr=e,start_new_session=True)
  while p.poll() is None:
   rows=[tuple(map(int,l.split())) for l in subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True).splitlines()];ids={p.pid}
   while True:
    nxt=ids|{pid for pid,parent,rss in rows if parent in ids}
    if nxt==ids:break
    ids=nxt
   own=next(rss*1024 for pid,parent,rss in rows if pid==os.getpid());assert own<512*1024**2
   rss=sum(rss*1024 for pid,parent,rss in rows if pid in ids);peak=max(peak,rss)
   if rss>=8*1024**3 or time.monotonic()-start>=540:
    stop='aggregate8GiB/deadline540s';os.killpg(p.pid,signal.SIGKILL);break
   time.sleep(.1)
  code=p.wait()
 log=(E/f'Port35ANCHOR_stdout-{call}.log').read_text();tim=(E/f'Port35ANCHOR_time-{call}.log').read_text()
 r.update(exit_status=code,wall_seconds=time.monotonic()-start,sampled_aggregate_peak_rss_bytes=peak,stopped=stop,post_hash_unchanged=all(pin(x['path'])==x for x in fresh['inputs']+fresh['runtime']+fresh['api']),stdout=pin(E/f'Port35ANCHOR_stdout-{call}.log'),time_log=pin(E/f'Port35ANCHOR_time-{call}.log'),full_axiom_lines=[l for l in log.splitlines() if '#print axioms' in l],errors=[l for l in log.splitlines() if 'error:' in l or 'PANIC' in l])
 for suffix,k in [('maximum resident set size','peak_process_rss_bytes'),('swaps','swaps')]:
  m=re.search(r'^\s*(\d+)\s+'+suffix+r'\s*$',tim,re.M);r[k]=int(m[1]) if m else None
 r['outputs']=[pin(x) for x in sorted(O.iterdir()) if x.is_file()];r['accepted']=code==0 and 'PORT35_COMPLETE' in log and not r['errors'] and r['post_hash_unchanged'];r['axioms_status']='full walk recorded' if r['full_axiom_lines'] else 'NOT REACHED; no theorem audit'
 r['status']='FINISHED';receipt.write_text(json.dumps(r,indent=2)+'\n');print({k:r[k] for k in ['exit_status','wall_seconds','sampled_aggregate_peak_rss_bytes','peak_process_rss_bytes','swaps','accepted']})
finally:
 if gl:gl.close()
 (lock/'Port35ANCHOR-owner.json').unlink();lock.rmdir()
