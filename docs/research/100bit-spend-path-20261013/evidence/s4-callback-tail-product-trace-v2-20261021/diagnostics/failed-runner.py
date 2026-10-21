from pathlib import Path
import hashlib,json,subprocess,os,time,signal,re,sys
repo=Path('/Users/dominic/ZK');kit=Path('/tmp/query-s4-callback-tail-product-v1');src=kit/'sources/S4CallbackTailProductTraceV1.lean';obj=kit/'objects/S4CallbackTailProductTraceV1.olean';ev=kit/'evidence';ev.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lean=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
selected=Path('/tmp/query-s4-callback-tail-product-cache-20261021')
roots=[str(kit/'objects'),str(selected),str(lean.parent.parent/'lib/lean')]
leanpath=':'.join(dict.fromkeys(roots))
imports={
 'FourDotsActualTailInputMeaningRootV1':Path('/tmp/root-s4-tail-input-meaning-v1-20261021/objects/FourDotsActualTailInputMeaningRootV1.olean'),
 'FourDotsTailAcceptedTraceRootV1':Path('/tmp/root-s4-tail-accepted-trace-v4-20261021/objects/FourDotsTailAcceptedTraceRootV1.olean'),
 'FourDotsPushProductTraceRootV1':Path('/tmp/root-s4-push-product-trace-v1-20261021/objects/FourDotsPushProductTraceRootV1.olean'),
 'EbyKPowerValueCanonicalToPushV5':Path('/tmp/prepared-local-warm-cache-20261020/EbyKPowerValueCanonicalToPushV5.olean'),
 'S4TailCoefficientCanonicalV1':Path('/tmp/query-s4-tail-coeff-canonical-v1/objects/S4TailCoefficientCanonicalV1.olean'),
}
closure=Path('/tmp/query-s4-callback-tail-product-cache-closure.json')
pre={'target':'S4CallbackTailProductTraceV1','source':str(src),'source_sha256':sha(src),'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=repo).strip(),'lean':str(lean),'lean_sha256':sha(lean),'lean_path':leanpath,'selected_closure_manifest':str(closure),'selected_closure_sha256':sha(closure),'selected_closure_modules':5148,'direct_imports':{n:{'path':str(p),'sha256':sha(p)} for n,p in imports.items()},'limits':{'threads':1,'lean_MiB':4400,'aggregate_rss_stop_bytes':8053063680,'timeout_seconds':120},'no_dependency_builds':True}
(ev/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
lock=Path('/tmp/aspis-local-lean.lock.d');started=time.monotonic()
while True:
 try:lock.mkdir();break
 except FileExistsError:
  if time.monotonic()-started>55:raise SystemExit('mutex timeout; no Lean started')
  time.sleep(1)
(lock/'owner.json').write_text(json.dumps({'pid':os.getpid(),'target':'S4CallbackTailProductTraceV1'})+'\n')
try:
 active=[]
 for line in subprocess.check_output(['ps','-axo','pid=,comm='],text=True).splitlines():
  parts=line.strip().split(None,1)
  if len(parts)==2 and Path(parts[1]).name=='lean':active.append(int(parts[0]))
 if active:
  (ev/'concurrency-denied.json').write_text(json.dumps({'live_lean_pids':active,'status':'no Lean started'})+'\n');raise SystemExit('live Lean PID detected; no target started')
 pre['source_sha256']=sha(src);pre['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=repo).strip();(ev/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
 argv=['/usr/bin/time','-l','-o',str(ev/'time.log'),'/usr/bin/env','LEAN_PATH='+leanpath,str(lean),'-j1','-M','4400','-R',str(kit/'sources'),'-o',str(obj),str(src)]
 (ev/'command.json').write_text(json.dumps({'argv':argv,'cwd':str(repo),'mutex':str(lock)},indent=2)+'\n')
 def rss_tree(pid):
  rows={}
  for line in subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True).splitlines():
   a,b,c=map(int,line.split());rows[a]=(b,c*1024)
  sel={pid};changed=True
  while changed:
   add={p for p,(pp,_) in rows.items() if pp in sel}-sel;changed=bool(add);sel|=add
  return sum(rows.get(p,(0,0))[1] for p in sel)
 start=time.monotonic();peak=0;reason=None
 with (ev/'lean.log').open('w') as log:
  p=subprocess.Popen(argv,cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  while p.poll() is None:
   peak=max(peak,rss_tree(p.pid))
   if peak>=8053063680 or time.monotonic()-start>120:
    reason='aggregate RSS safety stop' if peak>=8053063680 else '120s timeout';os.killpg(p.pid,signal.SIGTERM)
    try:p.wait(timeout=3)
    except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL)
    break
   time.sleep(.1)
  code=p.wait()
 txt=(ev/'time.log').read_text();m=lambda pat:int(re.search(pat,txt).group(1)) if re.search(pat,txt) else None
 rec={'target':'S4CallbackTailProductTraceV1','exit_status':code,'wall_seconds':round(time.monotonic()-start,3),'peak_aggregate_rss_bytes':peak,'peak_process_rss_bytes':m(r'(\d+)\s+maximum resident set size'),'process_swaps':m(r'(\d+)\s+swaps'),'watchdog_abort':reason,'source_sha256':sha(src),'object_sha256':sha(obj) if obj.is_file() else None,'source_revision_at_launch':pre['source_revision'],'axioms_output':(ev/'lean.log').read_text()[-6000:]};(ev/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True)
 if code!=0:sys.exit(code)
finally:
 (lock/'owner.json').unlink(missing_ok=True);lock.rmdir()
