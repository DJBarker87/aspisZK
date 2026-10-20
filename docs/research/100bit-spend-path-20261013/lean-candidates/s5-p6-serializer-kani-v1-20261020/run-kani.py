from pathlib import Path
import subprocess,json,hashlib,os,time,re,sys,fcntl
w=Path(__file__).resolve().parent;stage=sys.argv[1] if len(sys.argv)>1 else 'v1';e=w/('kani-'+stage);e.mkdir(exist_ok=False)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
collector=w/'collect-cgroups.py'
with open('/tmp/aspis-global-extraction-admission-20261019.lock','a') as lock:
 try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 except BlockingIOError:
  (e/'admission.json').write_text(json.dumps({'allowed':False,'reason':'global admission busy','not_started':True})+'\n');raise SystemExit(75)
 raw=subprocess.check_output(['python3',str(collector)],text=True);inv=json.loads(raw);(e/'reservation-inventory.json').write_text(raw)
 reserved=inv['effective_sum_bytes'];finite=[Path(x['path']) for x in inv['effective_reservation_nodes']]
 uncapped=[]
 for row in inv['unbounded_populated_scopes']:
  p=Path(row['path'])
  if any(p==f or f in p.parents for f in finite):continue
  if any(Path(other['path']) in p.parents for other in inv['unbounded_populated_scopes']):continue
  uncapped.append(row)
 uncapped_current=sum(x['current_bytes'] or 0 for x in uncapped)
 requested=2*2**30;physical=inv['MemTotal_kB']*1024
 allowed=reserved+requested<=48*2**30 and reserved+requested+uncapped_current+8*2**30<=physical and inv['MemAvailable_kB']*1024>=14*2**30
 admission={'allowed':allowed,'not_started':not allowed,'reserved_bytes':reserved,'requested_bytes':requested,'safe_reservation_limit_bytes':48*2**30,'uncapped_current_bytes':uncapped_current,'os_reserve_bytes':8*2**30,'physical_bytes':physical,'available_bytes':inv['MemAvailable_kB']*1024,'minimum_available_bytes':14*2**30,'source_binding_sha256':sha(w/'source-binding.json'),'collector_sha256':sha(collector)}
 (e/'admission.json').write_text(json.dumps(admission,indent=2)+'\n');print(json.dumps(admission),flush=True)
 if not allowed:raise SystemExit(78)
 cmd=['systemd-run','--user','--scope','--quiet','-p','MemoryHigh=1536M','-p','MemoryMax=2G','-p','MemorySwapMax=0','python3',str(w/'in-scope.py'),str(e)]
 (e/'scope-command.json').write_text(json.dumps(cmd,indent=2)+'\n')
 p=subprocess.Popen(cmd,cwd=w)
 started=time.monotonic()
 while p.poll() is None and not (e/'preflight.json').exists():
  if time.monotonic()-started>20:break
  time.sleep(.1)
 # The capped scope is visible to the collector before releasing admission.
 if (e/'preflight.json').exists():fcntl.flock(lock,fcntl.LOCK_UN)
 raise SystemExit(p.wait())
