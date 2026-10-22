from pathlib import Path
import sys,json,hashlib,subprocess,os,time,signal,re
w=Path(sys.argv[1]).resolve();n=sys.argv[2];profilefile=Path(sys.argv[3]).resolve()
ev=w/'evidence';ev.mkdir(parents=True,exist_ok=True);src=w/'sources'/(n+'.lean');obj=w/'objects'/(n+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lean=Path('/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
profile=profilefile.read_text().strip();roots=profile.split(':');imports={}
for name in re.findall(r'(?m)^import ([A-Za-z0-9_.]+)',src.read_text()):
 f=next((Path(r)/(name.replace('.','/')+'.olean') for r in roots if (Path(r)/(name.replace('.','/')+'.olean')).is_file()),None)
 if f is None:raise SystemExit('missing direct import '+name)
 imports[name]={'path':str(f),'sha256':sha(f)}
pre={'target':n,'source':str(src),'source_sha256':sha(src),'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd='/Users/dominic/ZK',text=True).strip(),'lean':str(lean),'lean_sha256':sha(lean),'profile':str(profilefile),'profile_sha256':sha(profilefile),'direct_imports':imports,'limits':{'threads':1,'lean_memory_mb':4400,'aggregate_rss_stop_bytes':int(7.5*1024**3),'timeout_seconds':120},'no_dependency_builds':True,'controller_sha256':sha(Path(__file__))}
(ev/'preflight.json').write_text(json.dumps(pre,indent=2)+'\n')
lock=Path('/tmp/aspis-local-lean.lock.d')
try:lock.mkdir()
except FileExistsError:raise SystemExit('mutex busy; no compiler launched')
inode=lock.stat().st_ino;owner={'pid':os.getpid(),'target':n,'inode':inode};(lock/'owner.json').write_text(json.dumps(owner)+'\n')
p=None;reason=None;peak=0;globalpeak=0;observations=[];foreign=[];code=None;start=time.monotonic()
def processes():
 rows={}
 for line in subprocess.check_output(['ps','-axo','pid=,ppid=,rss=,comm='],text=True).splitlines():
  a=line.split(None,3)
  if len(a)==4:rows[int(a[0])]=(int(a[1]),int(a[2])*1024,Path(a[3]).name)
 return rows
try:
 rows=processes();live=[pid for pid,row in rows.items() if row[2]=='lean']
 if live:raise SystemExit('foreign Lean live; no compiler launched: '+str(live))
 argv=['/usr/bin/time','-l','-o',str(ev/'time.log'),'/usr/bin/env','LEAN_PATH='+profile,str(lean),'-j1','-M','4400','-R',str(w/'sources'),'-o',str(obj),str(src)]
 (ev/'command.json').write_text(json.dumps({'argv':argv,'atomic_mkdir_lock':str(lock),'owner':owner},indent=2)+'\n')
 start=time.monotonic()
 with (ev/'lean.log').open('w') as log:
  p=subprocess.Popen(argv,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  while p.poll() is None:
   rows=processes();owned={p.pid}
   while True:
    add={pid for pid,row in rows.items() if row[0] in owned}-owned
    if not add:break
    owned|=add
   leanpids={pid:row[1] for pid,row in rows.items() if row[2]=='lean'}
   peak=max(peak,sum(rows[pid][1] for pid in owned if pid in rows));globalpeak=max(globalpeak,sum(leanpids.values()))
   elapsed=round(time.monotonic()-start,3)
   observations.append({'seconds':elapsed,'lean_pids_rss':leanpids,'own_process_tree_rss':sum(rows[pid][1] for pid in owned if pid in rows)})
   outside=set(leanpids)-owned
   outside_commands={pid:subprocess.run(['ps','-p',str(pid),'-o','command='],text=True,capture_output=True).stdout.strip() for pid in outside}
   metadata_only={pid:cmd for pid,cmd in outside_commands.items() if len(cmd.split())==2 and cmd.split()[-1] in ['--print-prefix','--version']}
   if metadata_only:observations[-1]['metadata_only_lean_commands']=metadata_only
   outside={pid for pid in outside if outside_commands[pid] and pid not in metadata_only}
   if outside:foreign.append({'seconds':elapsed,'pids':sorted(outside),'commands':{pid:outside_commands[pid] for pid in outside}});reason='foreign Lean detected'
   try:valid=lock.stat().st_ino==inode and json.loads((lock/'owner.json').read_text())==owner
   except (FileNotFoundError,json.JSONDecodeError):valid=False
   if not valid:reason='mutex ownership changed'
   if max(peak,globalpeak)>=pre['limits']['aggregate_rss_stop_bytes']:reason='aggregate RSS stop'
   if elapsed>120:reason='timeout120s'
   if reason:
    os.killpg(p.pid,signal.SIGTERM)
    try:p.wait(timeout=3)
    except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL)
    break
   time.sleep(.2)
  code=p.wait()
 raw=(ev/'time.log').read_text();extract=lambda expr:int(re.search(expr,raw).group(1)) if re.search(expr,raw) else None
 assert sha(src)==pre['source_sha256']
 receipt={'source_revision_at_launch':pre['source_revision'],'exit_status':code,'wall_seconds':round(time.monotonic()-start,3),'peak_aggregate_rss_bytes':peak,'peak_global_lean_rss_bytes':globalpeak,'peak_process_rss_bytes':extract(r'(\d+)\s+maximum resident set size'),'process_swaps':extract(r'(\d+)\s+swaps'),'watchdog_abort':reason,'foreign_lean_samples':foreign,'source_sha256':sha(src),'object_sha256':sha(obj) if obj.is_file() else None,'mutex_owner':owner,'controller_sha256':pre['controller_sha256']}
 (ev/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');(ev/'concurrency-observations.json').write_text(json.dumps(observations,indent=2)+'\n');print(json.dumps(receipt),flush=True)
finally:
 try:valid=lock.stat().st_ino==inode and json.loads((lock/'owner.json').read_text())==owner
 except (FileNotFoundError,json.JSONDecodeError):valid=False
 if valid:(lock/'owner.json').unlink();lock.rmdir()
 else:(ev/'mutex-release-declined.json').write_text(json.dumps({'reason':'not confirmed owned; left untouched','expected_owner':owner})+'\n')
if reason:raise SystemExit(2)
raise SystemExit(code if code is not None else 1)
