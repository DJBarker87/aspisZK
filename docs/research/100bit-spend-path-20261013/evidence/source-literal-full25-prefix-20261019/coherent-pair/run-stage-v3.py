from pathlib import Path
import hashlib,json,os,re,signal,subprocess,sys,time
W=Path(__file__).resolve().parent; CFG=json.loads((W/'config.json').read_text()); phase=sys.argv[1]
G=1024**3; sha=lambda b:hashlib.sha256(b).hexdigest()
def need(ok,msg):
 if not ok: raise SystemExit(msg)
target=next(x for x in CFG['targets'] if x['phase']==phase); src=W/target['source']; need(sha(src.read_bytes())==target['source_sha256'],'frozen source mismatch')
A=W/'attempt'; O=A/'objects'; O.mkdir(parents=True,exist_ok=True)
roots=[O,Path(CFG['roots']['trace14']),Path(CFG['roots']['terminal']),Path(CFG['roots']['step16']),Path(CFG['roots']['coalesced'])]+[Path(x) for x in CFG['package_roots']]
uniq=[]; seen=set()
for p in roots:
 if str(p) not in seen: uniq.append(p); seen.add(str(p))
leanpath=':'.join(map(str,uniq)); imports={}
for m,expected in target['direct_imports'].items():
 if expected=='PENDING_OBJECT_FROM_INITIAL': expected=CFG['initial_object_sha256']
 rel=Path(*m.split('.')).with_suffix('.olean'); found=next((p/rel for p in uniq if (p/rel).is_file()),None)
 need(found is not None,'missing direct import '+m)
 got=sha(found.read_bytes()); need(got==expected,'direct owner hash mismatch '+m+': '+got+' != '+expected)
 imports[m]={'path':str(found),'sha256':got}
lean=Path(CFG['lean']); need(sha(lean.read_bytes())==CFG['lean_sha256'],'Lean compiler pin mismatch')
obj=O/(target['module']+'.olean'); ev=A/(phase+'-evidence'); ev.mkdir(exist_ok=False)
line=Path('/proc/self/cgroup').read_text().strip(); need(line.startswith('0::'),'unexpected cgroup '+line); cg=Path('/sys/fs/cgroup')/line[3:].lstrip('/')
limits={k:(cg/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')}
need(limits=={'memory.high':str(4*G),'memory.max':str(6*G),'memory.swap.max':'0'},'unexpected scope limits '+repr(limits))
pre={'target':target['module'],'source':str(src),'source_sha256':target['source_sha256'],'source_revision':CFG['source_revision'],'object':str(obj),'lean':str(lean),'lean_sha256':CFG['lean_sha256'],'lean_path':leanpath,'direct_imports':imports,'limits':limits,'phase':phase,'runner_sha256':sha(Path(__file__).read_bytes())}
(ev/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
argv=[str(lean),'-j1','-M','5500','-DElab.async=false','-R',str(W/'sources'),'-o',str(obj),str(src)]
cmd=['/usr/bin/time','-v','-o',str(ev/'time.log'),'/usr/bin/env','LEAN_PATH='+leanpath,*argv]
(ev/'command.json').write_text(json.dumps({'argv':cmd,'scope':'MemoryHigh4G/MemoryMax6G/SwapMax0; one focused Lean target'},indent=2)+'\n')
before=(cg/'memory.events').read_text(); start=time.monotonic(); peak=sw=0; killed=None
with (ev/'lean.log').open('x') as log:
 proc=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 while proc.poll() is None:
  peak=max(peak,int((cg/'memory.peak').read_text())); sw=max(sw,int((cg/'memory.swap.current').read_text()))
  if time.monotonic()-start>120:
   killed='timeout_120s'; os.killpg(proc.pid,signal.SIGTERM)
   try: proc.wait(timeout=3)
   except subprocess.TimeoutExpired: os.killpg(proc.pid,signal.SIGKILL)
   break
  time.sleep(.1)
 status=proc.wait()
peak=max(peak,int((cg/'memory.peak').read_text())); sw=max(sw,int((cg/'memory.swap.current').read_text()))
txt=(ev/'time.log').read_text() if (ev/'time.log').exists() else ''; m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',txt)
rec={'exit_status':status,'wall_seconds':round(time.monotonic()-start,3),'peak_process_rss_kib':int(m[1]) if m else None,'scope_memory_peak_bytes':peak,'scope_swap_peak_bytes':sw,'memory_events_before':before,'memory_events_after':(cg/'memory.events').read_text(),'watchdog_abort':killed,'object_sha256':sha(obj.read_bytes()) if obj.exists() else None,'source_sha256':target['source_sha256']}
(ev/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n'); print(json.dumps(rec),flush=True); raise SystemExit(status)
