from pathlib import Path
import json,hashlib,subprocess,os,time,signal,re
w=Path('/tmp/s4-query-returned-model-v1'); ev=w/'evidence'; ev.mkdir(exist_ok=True)
n='S4QueryReturnedModelV1'; src=w/'sources'/f'{n}.lean'; obj=w/'objects'/f'{n}.olean';obj.parent.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lean=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
profile=Path(w/'LEAN_PATH.txt').read_text().strip()
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd='/Users/dominic/ZK').strip()
pre={'target':n,'source':str(src),'source_sha256':sha(src),'source_revision':rev,'lean':str(lean),'lean_sha256':sha(lean),'lean_path_file':str(w/'LEAN_PATH.txt'),'lean_path_sha256':sha(w/'LEAN_PATH.txt'),'resource':{'threads':1,'lean_memory_mb':4400,'aggregate_rss_stop_bytes':int(7.5*1024**3),'timeout_seconds':120},'no_dependency_builds':True,'host':'local macOS'}
(ev/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
lock=Path('/tmp/aspis-local-lean.lock.d'); deadline=time.monotonic()+55
while True:
 try: lock.mkdir(); break
 except FileExistsError:
  if time.monotonic()>deadline: raise SystemExit('local mutex timeout; no Lean launched')
  time.sleep(.25)
inode=lock.stat().st_ino;(lock/'owner.json').write_text(json.dumps({'pid':os.getpid(),'target':n,'inode':inode})+'\n')
try:
 live=[]
 for line in subprocess.check_output(['ps','-axo','pid=,comm='],text=True).splitlines():
  z=line.strip().split(None,1)
  if len(z)==2 and Path(z[1]).name=='lean': live.append(int(z[0]))
 if live: raise SystemExit('live Lean process present after lock acquisition: '+repr(live))
 argv=['/usr/bin/time','-l','-o',str(ev/'time.log'),'/usr/bin/env','LEAN_PATH='+profile,str(lean),'-j1','-M','4400','-R',str(w/'sources'),'-o',str(obj),str(src)]
 (ev/'command.json').write_text(json.dumps({'argv':argv,'atomic_mkdir_lock':str(lock),'lock_inode':inode},indent=2)+'\n')
 def rss_tree(pid):
  rows={}
  for line in subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True).splitlines():
   a,b,c=map(int,line.split());rows[a]=(b,c*1024)
  sel={pid};change=True
  while change:
   add={p for p,(par,_) in rows.items() if par in sel}-sel;change=bool(add);sel|=add
  return sum(rows.get(p,(0,0))[1] for p in sel)
 peak=0;start=time.monotonic();reason=None
 with (ev/'lean.log').open('w') as log:
  proc=subprocess.Popen(argv,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  while proc.poll() is None:
   peak=max(peak,rss_tree(proc.pid))
   if peak>=int(7.5*1024**3) or time.monotonic()-start>120:
    reason='aggregate RSS watchdog' if peak>=int(7.5*1024**3) else '120s timeout'
    os.killpg(proc.pid,signal.SIGTERM)
    try: proc.wait(timeout=3)
    except subprocess.TimeoutExpired: os.killpg(proc.pid,signal.SIGKILL)
    break
   time.sleep(.1)
  code=proc.wait()
 txt=(ev/'time.log').read_text() if (ev/'time.log').exists() else ''
 get=lambda pat:int(re.search(pat,txt).group(1)) if re.search(pat,txt) else None
 receipt={'source_revision_at_launch':rev,'exit_status':code,'wall_seconds':round(time.monotonic()-start,3),'peak_aggregate_rss_bytes':peak,'peak_process_rss_bytes':get(r'(\d+)\s+maximum resident set size'),'process_swaps':get(r'(\d+)\s+swaps'),'watchdog_abort':reason,'source_sha256':sha(src),'object_sha256':sha(obj) if obj.is_file() else None}
 (ev/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
finally:
 if lock.exists() and lock.stat().st_ino==inode:
  owner=json.loads((lock/'owner.json').read_text());assert owner['pid']==os.getpid() and owner['inode']==inode
  (lock/'owner.json').unlink();lock.rmdir()
raise SystemExit(code)
