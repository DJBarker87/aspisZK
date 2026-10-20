from pathlib import Path
import hashlib,json,os,re,signal,subprocess,sys,time
W=Path(__file__).resolve().parent; C=json.loads((W/'config.json').read_text()); phase=sys.argv[1]
G=1024**3
sha=lambda b:hashlib.sha256(b).hexdigest()
def need(ok,msg):
 if not ok: raise SystemExit(msg)
st=next(x for x in C['stages'] if x['phase']==phase)
src=W/st['source']; need(sha(src.read_bytes())==st['source_sha256'], 'source hash mismatch')
A=W/'attempt'; O=A/'objects'; O.mkdir(parents=True,exist_ok=True)
roots=[O]+[Path(x) for x in C['lean_path']]
uniq=[]; seen=set()
for p in roots:
 if str(p) not in seen: uniq.append(p); seen.add(str(p))
imports={}
for m,expected in st['direct_imports'].items():
 if expected.startswith('FROM_STAGE_'):
  stage_name=expected.removeprefix('FROM_STAGE_')
  previous=next(x for x in C['stages'] if x['phase']==stage_name)
  owner=O/Path(*previous['module'].split('.')).with_suffix('.olean')
  need(owner.is_file(),'missing preceding built owner '+m)
 else:
  rel=Path(*m.split('.')).with_suffix('.olean')
  owner=next((p/rel for p in uniq if (p/rel).is_file()),None)
  need(owner is not None,'missing direct import '+m)
  got=sha(owner.read_bytes()); need(got==expected,'direct owner hash mismatch '+m+': '+got+' != '+expected)
 imports[m]={'path':str(owner),'sha256':sha(owner.read_bytes())}
lean=Path(C['lean']);need(sha(lean.read_bytes())==C['lean_sha256'],'Lean compiler hash mismatch')
obj=O/Path(*st['module'].split('.')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
ev=A/(phase+'-evidence');ev.mkdir(exist_ok=False)
cgline=Path('/proc/self/cgroup').read_text().strip();need(cgline.startswith('0::'),'unexpected cgroup')
cg=Path('/sys/fs/cgroup')/cgline[3:].lstrip('/')
limits={k:(cg/k).read_text().strip() for k in ('memory.high','memory.max','memory.swap.max')}
need(limits=={'memory.high':str(C['scope_memory_high_bytes']),'memory.max':str(C['scope_memory_max_bytes']),'memory.swap.max':'0'},'unexpected scope limits '+repr(limits))
leanpath=':'.join(map(str,uniq)); runnerhash=sha(Path(__file__).read_bytes())
pre={'target':st['module'],'source':str(src),'source_sha256':st['source_sha256'],'source_revision':C['source_revision'],'object':str(obj),'lean':str(lean),'lean_sha256':C['lean_sha256'],'lean_path':leanpath,'direct_imports':imports,'limits':limits,'phase':phase,'runner_sha256':runnerhash}
(ev/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
argv=[str(lean),'-j1','-M','6000','-R',str(W/'sources'),'-o',str(obj),str(src)]
cmd=['/usr/bin/time','-v','-o',str(ev/'time.log'),'/usr/bin/env','LEAN_PATH='+leanpath,*argv]
(ev/'command.json').write_text(json.dumps({'argv':cmd,'scope':'MemoryHigh='+str(C['scope_memory_high_bytes'])+'/MemoryMax='+str(C['scope_memory_max_bytes'])+'/MemorySwapMax0; focused Lean owner'},indent=2)+'\n')
before=(cg/'memory.events').read_text();start=time.monotonic();peak=sw=0;killed=None
with (ev/'lean.log').open('x') as log:
 p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 while p.poll() is None:
  peak=max(peak,int((cg/'memory.peak').read_text()));sw=max(sw,int((cg/'memory.swap.current').read_text()))
  if time.monotonic()-start>120:
   killed='timeout_120s';os.killpg(p.pid,signal.SIGTERM)
   try:p.wait(timeout=3)
   except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL)
   break
  time.sleep(.1)
 status=p.wait()
peak=max(peak,int((cg/'memory.peak').read_text()));sw=max(sw,int((cg/'memory.swap.current').read_text()))
txt=(ev/'time.log').read_text() if (ev/'time.log').exists() else '';m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',txt)
rec={'exit_status':status,'wall_seconds':round(time.monotonic()-start,3),'peak_process_rss_kib':int(m[1]) if m else None,'scope_memory_peak_bytes':peak,'scope_swap_peak_bytes':sw,'memory_events_before':before,'memory_events_after':(cg/'memory.events').read_text(),'watchdog_abort':killed,'object_sha256':sha(obj.read_bytes()) if obj.exists() else None,'source_sha256':st['source_sha256']}
(ev/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True)
if status==0:
 C['stages'][[i for i,x in enumerate(C['stages']) if x['phase']==phase][0]]['object_sha256']=rec['object_sha256'];(W/'config.json').write_text(json.dumps(C,indent=2,sort_keys=True)+'\n')
raise SystemExit(status)
