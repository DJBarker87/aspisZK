from pathlib import Path
import json,hashlib,subprocess,os,time,signal,re
repo=Path('/Users/dominic/ZK')
base=Path('/tmp/s4-p6-clean-repair-compile')
repair=Path('/tmp/s4-p6-formatter-repair-closure')
source=Path('/tmp/S4GeneratedCallbackClosurePreservationV28.lean')
lean=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
ev=Path('/tmp/s4-p6-callback-v28-evidence-rerun')
ev.mkdir(exist_ok=False)
obj=ev/'S4GeneratedCallbackClosurePreservationV28.olean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
imports={}
for mod,owner in [('S4FourDotsP6ArrayOperationV1',base/'S4FourDotsP6ArrayOperationV1.olean'),('AspisR1FastDotsCurrent.FunsOpsV4',base/'AspisR1FastDotsCurrent/FunsOpsV4.olean'),('AspisR1FastDotsCurrent.Types',base/'AspisR1FastDotsCurrent/Types.olean'),('Aeneas',repair/'Aeneas.olean'),('Aeneas.Std.Array.Array',repair/'Aeneas/Std/Array/Array.olean')]:
 imports[mod]={'path':str(owner),'sha256':sha(owner)}
leanpath=':'.join(map(str,[base,repair,Path('/tmp/lean432-nuc-aeneas-cache'),*[(Path('/Users/dominic/ZK/AspisFormal/.lake/packages')/p/'.lake/build/lib/lean') for p in ['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']],Path('/Users/dominic/ZK/AspisFormal/.lake/build/lib/lean'),lean.parent/'../lib/lean']))
pre={'target':'S4GeneratedCallbackClosurePreservationV28','source':str(source),'source_sha256':sha(source),'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True,cwd=repo).strip(),'compiler':str(lean),'compiler_sha256':sha(lean),'lean_path':leanpath,'direct_imports':imports,'limits':{'threads':1,'lean_memory_mb':4400,'timeout_seconds':120,'aggregate_rss_stop_bytes':int(7.5*1024**3)},'host':'local macOS','purpose':'single evidence-completeness rerun; prior proof green, import metadata/source revision omitted at launch'}
(ev/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
lock=Path('/tmp/aspis-local-lean.lock.d');startwait=time.monotonic()
while True:
 try: lock.mkdir();break
 except FileExistsError:
  if time.monotonic()-startwait>180: raise SystemExit('lock wait timeout; no compiler started')
  time.sleep(1)
own={'target':pre['target'],'pid':os.getpid()};owner=lock/'owner.json';owner.write_text(json.dumps(own))
code=125
try:
 active=[]
 for line in subprocess.check_output(['ps','-axo','pid=,comm='],text=True).splitlines():
  a=line.strip().split(None,1)
  if len(a)==2 and Path(a[1]).name=='lean':active.append(a[0])
 if active:
  (ev/'denied.json').write_text(json.dumps({'live_lean_pids':active,'status':'no Lean started'})+'\n');raise SystemExit('live Lean process; abort')
 argv=['/usr/bin/time','-l','-o',str(ev/'time.log'),'/usr/bin/env','LEAN_PATH='+leanpath,str(lean),'-j1','-M','4400','-R','/tmp',str(source),'-o',str(obj)]
 (ev/'command.json').write_text(json.dumps({'argv':argv,'revision_at_launch':pre['source_revision'],'source_sha256_at_launch':pre['source_sha256'],'import_pins_at_launch':imports},indent=2)+'\n')
 def rss_tree(pid):
  rows={}
  for line in subprocess.check_output(['ps','-axo','pid=,ppid=,rss='],text=True).splitlines():
   a,b,c=map(int,line.split());rows[a]=(b,c*1024)
  selected={pid};change=True
  while change:
   new={p for p,(pp,_) in rows.items() if pp in selected}-selected;change=bool(new);selected|=new
  return sum(rows.get(p,(0,0))[1] for p in selected)
 peak=0;t=time.monotonic();reason=None
 with (ev/'lean.log').open('w') as f:
  proc=subprocess.Popen(argv,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
  while proc.poll() is None:
   peak=max(peak,rss_tree(proc.pid))
   if peak>=int(7.5*1024**3) or time.monotonic()-t>120:
    reason='RSS watchdog' if peak>=int(7.5*1024**3) else '120s timeout';os.killpg(proc.pid,signal.SIGTERM)
    try:proc.wait(timeout=3)
    except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL)
    break
   time.sleep(.1)
  code=proc.wait()
 time_log=(ev/'time.log').read_text()
 get=lambda pat:int(re.search(pat,time_log).group(1)) if re.search(pat,time_log) else None
 receipt={'exit_status':code,'wall_seconds':round(time.monotonic()-t,3),'peak_aggregate_rss_bytes':peak,'peak_process_rss_bytes':get(r'(\d+)\s+maximum resident set size'),'process_swaps':get(r'(\d+)\s+swaps'),'watchdog_abort':reason,'source_sha256':sha(source),'object_sha256':sha(obj) if obj.exists() else None,'source_revision_at_launch':pre['source_revision'],'compiler_sha256':pre['compiler_sha256'],'direct_imports':imports}
 (ev/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
finally:
 try:
  if json.loads(owner.read_text())==own: owner.unlink();lock.rmdir()
 except (OSError,ValueError):pass
raise SystemExit(code)
