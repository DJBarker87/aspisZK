from pathlib import Path
import json,hashlib,subprocess,os,time,signal,re,shutil
w=Path('/tmp/root-s4-n8-canonical-v2-20261020');(w/'sources').mkdir(parents=True,exist_ok=True)
n='S4FromFnP6InnerN8ActualCanonicalV1';src=w/'sources'/f'{n}.lean';assert src.is_file()
ev=w/'evidence';ev.mkdir(exist_ok=False);obj=w/'objects'/f'{n}.olean';obj.parent.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lean=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');cache=Path('/tmp/root-s4-n8-canonical-cache-20261020');repair=Path('/tmp/s4-p6-formatter-repair-closure');legacy=Path('/tmp/lean432-gather-array-objects')
imports={}
for name in ['S4FromFnP6InnerN8ArrayFieldV1','ExtractedCurrentReducer']:
 f=next(p for p in [repair/(name.replace('.','/')+'.olean'),cache/(name.replace('.','/')+'.olean'),legacy/(name.replace('.','/')+'.olean')] if p.is_file());imports[name]={'path':str(f),'sha256':sha(f)}
pre={'target':n,'source':str(src),'source_sha256':sha(src),'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd='/Users/dominic/ZK').strip(),'lean':str(lean),'lean_sha256':sha(lean),'direct_imports':imports,'warm_cache_manifest':'/tmp/root-s4-n8-canonical-cache-closure.json','warm_cache_manifest_sha256':sha(Path('/tmp/root-s4-n8-canonical-cache-closure.json')),'host':'local macOS','limits':{'threads':1,'lean_memory_mb':4400,'aggregate_rss_stop_bytes':int(7.5*1024**3),'timeout_seconds':120},'no_dependency_builds':True}
(ev/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
lock=Path('/tmp/aspis-local-lean.lock.d');waitstart=time.monotonic()
while True:
 try:lock.mkdir();break
 except FileExistsError:
  if time.monotonic()-waitstart>55:raise SystemExit('local lock timeout; no Lean started')
  time.sleep(1)
try:
 active=[]
 for line in subprocess.check_output(['ps','-axo','pid=,comm='],text=True).splitlines():
  parts=line.strip().split(None,1)
  if len(parts)==2 and Path(parts[1]).name=='lean':active.append(int(parts[0]))
 if active:
  (ev/'concurrency-denied.json').write_text(json.dumps({'live_lean_pids':active,'status':'no root Lean started'})+'\n')
  raise SystemExit('another Lean is live; no root process started')
 pre['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd='/Users/dominic/ZK').strip()
 (ev/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
 argv=['/usr/bin/time','-l','-o',str(ev/'time.log'),'/usr/bin/env','LEAN_PATH='+str(repair)+':'+str(cache)+':'+str(legacy),str(lean),'-j1','-M','4400','-R',str(w/'sources'),'-o',str(obj),str(src)]
 (ev/'command.json').write_text(json.dumps({'argv':argv,'atomic_mkdir_lock':str(lock)},indent=2)+'\n')
 def rss_tree(pid):
  rows={}
  for line in subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True).splitlines():
   a,b,c=map(int,line.split());rows[a]=(b,c*1024)
  selected={pid};change=True
  while change:
   add={p for p,(parent,rss) in rows.items() if parent in selected}-selected;change=bool(add);selected|=add
  return sum(rows.get(p,(0,0))[1] for p in selected)
 peak=0;start=time.monotonic();reason=None
 with (ev/'lean.log').open('w') as log:
  p=subprocess.Popen(argv,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  while p.poll() is None:
   peak=max(peak,rss_tree(p.pid))
   if peak>=int(7.5*1024**3) or time.monotonic()-start>120:
    reason='aggregate RSS approaching8GiB' if peak>=int(7.5*1024**3) else 'timeout120s'
    os.killpg(p.pid,signal.SIGTERM)
    try:p.wait(timeout=3)
    except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL)
    break
   time.sleep(.1)
  code=p.wait()
 txt=(ev/'time.log').read_text();extract=lambda expr: int(re.search(expr,txt).group(1)) if re.search(expr,txt) else None
 receipt={'exit_status':code,'wall_seconds':round(time.monotonic()-start,3),'peak_aggregate_rss_bytes':peak,'peak_process_rss_bytes':extract(r'(\d+)\s+maximum resident set size'),'process_swaps':extract(r'(\d+)\s+swaps'),'watchdog_abort':reason,'source_sha256':sha(src),'object_sha256':sha(obj) if obj.is_file() else None}
 (ev/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
finally:lock.rmdir()
raise SystemExit(code)
