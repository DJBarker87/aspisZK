#!/usr/bin/env python3
"""R427 focused pinned Charon release build. Unlaunched, fail-closed remote worker."""
import hashlib,json,os,pathlib,re,signal,subprocess,threading,time,queue
if os.environ.get('R427_ALLOW_BUILD')!='1': raise SystemExit('build launch gate closed: require R427_ALLOW_BUILD=1 after lead review')
SRC=pathlib.Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon')
ROOT=pathlib.Path('/home/dombarker/project-offloads/aspis-r427-raw-mir-observer-20261002-a')
AUDIT=ROOT/'candidate-audit/build-attempt-v2'
STAGE=pathlib.Path('/tmp/aspis-r427-raw-mir-observer-20261002-a/build-attempt-v2')
PIN={'revision':'cb50ff16b9f1066b8a97dc06da704de2da2fa41c','draft':'246d1fec2223d8ad5755e4aa9f24e647af7c16a18a8a2d893d9085213bf8a9ab','base_get_mir':'e6461421d16dc4e9e1a7e5f097e8aab455513b1a290b780c90afc4f3f5765964','wrapper':'b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c','driver_before':'4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938','cargo_toml':'a31bab7d34638f8c2a43f14263184a3328ab17366c2f9acf201d86b922c4176f','cargo_lock':'c755a326679e9b3dbce560ff15130bdc83ae16178f2c1af568e391b8470d2e67','nested_toolchain':'27e050e8fc5ac827e1264abf38c27fcaf18e73f4305104c866179cb84721898c','rustc_commit':'14210df0e27ccd7d9e6a05b8085cbd438e4bbc65'}

def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def tracked_sha(p):
 raw=os.fsencode(os.readlink(p)) if p.is_symlink() else p.read_bytes()
 return hashlib.sha256(raw).hexdigest()
def git(*args,**kw):return subprocess.check_output(['git','-C',str(SRC),*args],**kw)
def meminfo():
 keys={'MemTotal','MemAvailable','SwapTotal','SwapFree'};out={}
 for line in pathlib.Path('/proc/meminfo').read_text().splitlines():
  k,v=line.split(':',1)
  if k in keys:out[k]=v.strip()
 return out
def cgroup():
 line=next((x for x in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::')),None)
 if not line:return {'path':None}
 p=pathlib.Path('/sys/fs/cgroup')/line.split('::',1)[1].lstrip('/');d={'path':str(p)}
 for n in ('memory.current','memory.peak','memory.high','memory.max','memory.swap.current','memory.swap.peak','memory.swap.max','memory.events','pids.current','pids.max'):
  try:d[n]=(p/n).read_text().strip()
  except OSError:pass
 return d
def assert_effective_caps():
 d=cgroup();expected={'memory.high':str(5*1024**3),'memory.max':str(7*1024**3),'memory.swap.max':'0','pids.max':'128'}
 actual={k:d.get(k) for k in expected}
 assert actual==expected,{'expected':expected,'actual':actual,'cgroup':d}
 return d
def assert_effective_caps():
 d=cgroup();expected={'memory.high':str(5*1024**3),'memory.max':str(7*1024**3),'memory.swap.max':'0','pids.max':'128'}
 actual={k:d.get(k) for k in expected}
 assert actual==expected,{'expected':expected,'actual':actual,'cgroup':d}
 return d
def cache_manifest(root):
 rows=[]
 for cur,dirs,files in os.walk(root,topdown=True,followlinks=False):
  dirs.sort();files.sort();base=pathlib.Path(cur)
  for name in list(dirs):
   p=base/name
   if p.is_symlink():rows.append({'path':p.relative_to(root).as_posix(),'kind':'symlink','target':os.readlink(p),'mode':p.lstat().st_mode & 0o777});dirs.remove(name)
  for name in files:
   p=base/name;rel=p.relative_to(root).as_posix()
   if p.is_symlink():rows.append({'path':rel,'kind':'symlink','target':os.readlink(p),'mode':p.lstat().st_mode & 0o777})
   elif p.is_file():rows.append({'path':rel,'kind':'file','size':p.stat().st_size,'sha256':sha(p),'mode':p.stat().st_mode & 0o777})
   else:raise RuntimeError(f'unexpected cache entry {p}')
 return rows
def tree_sha(root,expected_rows):
 result={}
 for row in expected_rows:
  rel=row['path'];p=root/rel
  if p.is_file() or p.is_symlink():result[rel]=tracked_sha(p)
  else:raise RuntimeError(f'missing tracked source file: {rel}')
 return result

def active_aspis_reservations():
 units=subprocess.check_output(['systemctl','--user','list-units','--all','--type=service','--no-legend'],text=True).splitlines();out=[];summax=0
 for line in units:
  name=line.split()[0]
  if not name.startswith('aspis') or name=='aspisr427-build.service':continue
  props=subprocess.check_output(['systemctl','--user','show',name,'-p','ControlGroup','-p','MemoryMax','-p','MemoryCurrent'],text=True)
  d=dict(x.split('=',1) for x in props.splitlines() if '=' in x);cg=pathlib.Path('/sys/fs/cgroup')/d.get('ControlGroup','').lstrip('/');pids=[]
  if cg.exists():
   for f in cg.rglob('cgroup.procs'):
    try:pids.extend(x.strip() for x in f.read_text().splitlines() if x.strip())
    except OSError:pass
  maxv=int(d.get('MemoryMax','0')) if d.get('MemoryMax','0').isdigit() else 0
  if pids:summax+=maxv
  out.append({'unit':name,'pids':pids,'memory_max_bytes':maxv,'memory_current_bytes':int(d.get('MemoryCurrent','0') or 0)})
 return out,summax

assert ROOT.is_dir() and not AUDIT.exists(),f'clone missing or build evidence already exists: {AUDIT}'
clone_record=json.loads((ROOT/'candidate-audit/clone/clone-audit.json').read_text())
assert clone_record['status'].startswith('ordinary pinned archive and copy completed')
assert clone_record['source_head']==PIN['revision'] and clone_record['candidate_get_mir_sha256']==PIN['draft']
assert clone_record['only_tracked_source_difference']==['charon/src/bin/charon-driver/translate/get_mir.rs']
assert git('rev-parse','HEAD',text=True).strip()==PIN['revision']
subprocess.run(['git','-C',str(SRC),'diff','--quiet','HEAD','--'],check=True)
subprocess.run(['git','-C',str(SRC),'diff','--cached','--quiet','HEAD','--'],check=True)
tracked=json.loads((ROOT/'candidate-audit/clone/tracked-tree.json').read_text())
symlink_paths=[r['path'] for r in tracked if r['mode']=='120000']
expected_symlink_paths=['doc-ml.html','doc-rust.html','rust-toolchain']
assert symlink_paths==expected_symlink_paths,{'actual_tracked_symlinks':symlink_paths,'expected_tracked_symlinks':expected_symlink_paths}
assert clone_record.get('tracked_symlink_paths')==expected_symlink_paths,clone_record.get('tracked_symlink_paths')
source_before=tree_sha(SRC,tracked);candidate_before=tree_sha(ROOT,tracked)
assert source_before==clone_record['tracked_source_sha256_before']
assert candidate_before==clone_record['tracked_candidate_sha256_after_overlay']
base=ROOT/'charon/src/bin/charon-driver/translate/get_mir.rs'
assert sha(base)==PIN['draft']
for root in (SRC,ROOT):
 assert sha(root/'charon/Cargo.toml')==PIN['cargo_toml']
 assert sha(root/'charon/Cargo.lock')==PIN['cargo_lock']
 assert sha(root/'charon/rust-toolchain')==PIN['nested_toolchain']
 assert sha(root/'charon/target/release/charon')==PIN['wrapper']
assert sha(SRC/'bin/charon')==PIN['wrapper'] and sha(ROOT/'bin/charon')==PIN['wrapper']
assert sha(SRC/'charon/target/release/charon-driver')==PIN['driver_before']
assert sha(ROOT/'charon/target/release/charon-driver')==PIN['driver_before']
cache_copy=json.loads((ROOT/'candidate-audit/clone/target-cache-clone-sha256.json').read_text())
# Ensure the cloned cache was not changed between clone audit and this build start.
def portable(rows):return [{k:v for k,v in r.items() if k not in ('dev','ino')} for r in rows]
cache_source=json.loads((ROOT/'candidate-audit/clone/target-cache-sha256.json').read_text())
assert len(cache_copy)>=1494
assert portable(cache_copy)==portable(cache_source),'source and copied target cache differ in saved clone-time manifests'
current_cache=cache_manifest(ROOT/'charon/target')
assert portable(current_cache)==portable(cache_copy),'candidate target cache changed after clone audit and before build'
mem=meminfo();avail=int(mem['MemAvailable'].split()[0])*1024;total=int(mem['MemTotal'].split()[0])*1024
cap=7*1024**3;reserve=24*1024**3;safe=min(40*1024**3,total-16*1024**3)
assert avail-cap>=reserve,{'meminfo':mem,'candidate_cap':cap,'reserve':reserve}
assert cap<=safe,{'candidate_cap':cap,'safe_working_limit':safe}
worker_cgroup=assert_effective_caps()
worker_cgroup=assert_effective_caps()
other_units,other_max=active_aspis_reservations();assert not any(x['pids'] for x in other_units),other_units
assert other_max+cap<=safe,{'other_active_aspis_max':other_max,'candidate_cap':cap,'safe':safe}
processes=subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines()
heavy=[line.strip() for line in processes if len(line.split())>=2 and line.split()[1] in ('cargo','rustc','rustc_driver','charon','charon-driver','aeneas','lean','lean4')]
assert not heavy,heavy
RUSTUP='/home/dombarker/.cargo/bin/rustup';CARGO='/home/dombarker/.cargo/bin/cargo';CHANNEL='nightly-2026-06-01'
rustc=subprocess.check_output([RUSTUP,'run',CHANNEL,'rustc','--version','--verbose'],text=True)
cargo=subprocess.check_output([RUSTUP,'run',CHANNEL,'cargo','--version'],text=True)
assert PIN['rustc_commit'] in rustc,rustc
sysroot=subprocess.check_output([RUSTUP,'run',CHANNEL,'rustc','--print','sysroot'],text=True).strip()
# Check exact typed cache folder and compiler version before entering Cargo.
assert os.path.isdir(sysroot) and '1.98.0-nightly' in rustc
AUDIT.mkdir(parents=True)
command=[CARGO,'+'+CHANNEL,'build','--manifest-path',str(ROOT/'charon/Cargo.toml'),'--release','--offline','--locked','--jobs','1','--bin','charon-driver']
pre={'status':'pre-build gates passed','target':str(ROOT/'charon/target/release/charon-driver'),'source_revision':PIN['revision'],'candidate_draft_sha256':sha(base),'cargo_command':command,'CARGO_TARGET_DIR':str(ROOT/'charon/target'),'CARGO_HOME':'/home/dombarker/.cargo','rustc_version':rustc,'cargo_version':cargo,'sysroot':sysroot,'parent_get_mir_sha256':sha(SRC/'charon/src/bin/charon-driver/translate/get_mir.rs'),'parent_wrapper_sha256':sha(SRC/'bin/charon'),'parent_driver_before_sha256':sha(SRC/'charon/target/release/charon-driver'),'clone_wrapper_sha256':sha(ROOT/'bin/charon'),'clone_driver_before_sha256':sha(ROOT/'charon/target/release/charon-driver'),'available_memory_before':mem,'effective_worker_cgroup_before':worker_cgroup,'memory_caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'other_aspis_active_units':other_units,'other_aspis_reserved_max_bytes':other_max,'safe_working_limit_bytes':safe,'heavy_processes':heavy,'allowed_local_compiling_packages':['charon','hax-adt-into','macros','rustc_trait_elaboration'],'stop_conditions':['any non-workspace Compiling package (cold external dependency build)','10 minutes without compiler output/new target event','cgroup OOM/OOM-kill event','source/cache/wrapper/toolchain mismatch']}
(AUDIT/'build-command.json').write_text(json.dumps(pre,indent=2,sort_keys=True)+'\n')
(AUDIT/'build-host-reservation-before.json').write_text(json.dumps({'meminfo':mem,'other_aspis_units':other_units,'other_aspis_reserved_max_bytes':other_max,'candidate_memory_max_bytes':cap,'safe_working_limit_bytes':safe,'cgroup_at_worker_start':cgroup()},indent=2,sort_keys=True)+'\n')
# The transient systemd unit caps this whole process tree. Parse Cargo's ordinary output and stop immediately if it must rebuild an external dependency.
started=time.monotonic();last_event=started;allowed={'charon','hax-adt-into','macros','rustc_trait_elaboration'};unexpected=[];timed_out=False;lines=[];sampler_stop=threading.Event();samples=[]
def sampler():
 while not sampler_stop.is_set():
  snap={'monotonic':time.monotonic(),**cgroup()};samples.append(snap)
  ev=snap.get('memory.events','')
  vals=dict((z.split() if len(z.split())==2 else (z.split()[0],'0')) for z in ev.splitlines()) if ev else {}
  if int(vals.get('oom',0)) or int(vals.get('oom_kill',0)): sampler_stop.set();break
  sampler_stop.wait(.5)
thread=threading.Thread(target=sampler,daemon=True);thread.start()
log_path=AUDIT/'build.log';time_path=AUDIT/'cargo-gnu-time.txt';execution=['/usr/bin/time','-v','-o',str(time_path),*command]
proc=subprocess.Popen(execution,cwd=ROOT,env={**os.environ,'PATH':'/home/dombarker/.cargo/bin:'+os.environ.get('PATH',''),'CARGO_HOME':'/home/dombarker/.cargo','CARGO_TARGET_DIR':str(ROOT/'charon/target'),'CARGO_NET_OFFLINE':'true'},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,bufsize=1,start_new_session=True)
messages=queue.Queue();
def stdout_reader():
 for item in proc.stdout:messages.put(item)
 messages.put(None)
reader=threading.Thread(target=stdout_reader,daemon=True);reader.start();eof=False
with log_path.open('w') as log:
 while not eof:
  if sampler_stop.is_set():break
  try:line=messages.get(timeout=.5)
  except queue.Empty:
   if time.monotonic()-last_event>600:timed_out=True;break
   continue
  if line is None:eof=True;break
  else:
   log.write(line);log.flush();lines.append(line.rstrip('\n'));last_event=time.monotonic()
   m=re.search(r'^\s*Compiling\s+([A-Za-z0-9_-]+)\s',line)
   if m and m.group(1) not in allowed:
    unexpected.append({'package':m.group(1),'line':line.rstrip('\n')});break
 if unexpected or timed_out or sampler_stop.is_set():
  try:os.killpg(proc.pid,signal.SIGTERM)
  except ProcessLookupError:pass
  try:proc.wait(timeout=10)
  except subprocess.TimeoutExpired:
   try:os.killpg(proc.pid,signal.SIGKILL)
   except ProcessLookupError:pass
   proc.wait()
 reader.join(timeout=5)
 while True:
  try:item=messages.get_nowait()
  except queue.Empty:break
  if item is not None:log.write(item);log.flush();lines.append(item.rstrip('\n'))
status=proc.wait()
sampler_stop.set();thread.join()
post_source=tree_sha(ROOT,tracked)
expected_post={r['path']:PIN['draft'] if r['path']=='charon/src/bin/charon-driver/translate/get_mir.rs' else source_before[r['path']] for r in tracked}
changed=[p for p in expected_post if post_source[p]!=expected_post[p]]
source_head_after=git('rev-parse','HEAD',text=True).strip()
source_clean=subprocess.run(['git','-C',str(SRC),'diff','--quiet','HEAD','--'],check=False).returncode==0
parent_pins_after={'get_mir':sha(SRC/'charon/src/bin/charon-driver/translate/get_mir.rs'),'wrapper':sha(SRC/'bin/charon'),'target_charon':sha(SRC/'charon/target/release/charon'),'driver':sha(SRC/'charon/target/release/charon-driver')}
candidate_pins_after={'wrapper':sha(ROOT/'bin/charon'),'target_charon':sha(ROOT/'charon/target/release/charon')}
new_driver=ROOT/'charon/target/release/charon-driver'
gnu_text=time_path.read_text() if time_path.exists() else ''
def metric(pattern):
 m=re.search(pattern,gnu_text,re.M);return m.group(1).strip() if m else None
cg_after=cgroup()
def has_oom(snapshot):
 vals={}
 for part in snapshot.get('memory.events','').splitlines():
  bits=part.split()
  if len(bits)==2:vals[bits[0]]=int(bits[1])
 return vals.get('oom',0)>0 or vals.get('oom_kill',0)>0
oom_detected=any(has_oom(x) for x in samples)
result={'build_exit_status':status,'candidate_target_exists':new_driver.is_file(),'candidate_driver_sha256':sha(new_driver) if new_driver.is_file() else None,'candidate_driver_size_bytes':new_driver.stat().st_size if new_driver.is_file() else None,'source_head_before_after':[PIN['revision'],source_head_after],'candidate_draft_sha256':sha(base),'candidate_source_only_expected_draft_change':not changed,'unexpected_external_compilations':unexpected,'no_output_timeout':timed_out,'oom_or_oom_kill_detected':oom_detected,'wall_seconds_python':time.monotonic()-started,'gnu_time_elapsed':metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(.+)'),'gnu_time_peak_rss_kib':int(metric(r'Maximum resident set size \(kbytes\):\s*(\d+)') or 0),'gnu_time_swaps':int(metric(r'Swaps:\s*(\d+)') or 0),'gnu_time_exit_status':int(metric(r'Exit status:\s*(\d+)') or -1),'compiler_lines':lines,'rustc_version':rustc,'cargo_version':cargo,'sysroot':sysroot,'source_tree_sha256_after':post_source,'source_tree_unexpected_changes':changed,'parent_source_clean_after':source_clean,'parent_pins_after':parent_pins_after,'candidate_pins_after':candidate_pins_after,'cgroup_samples':samples,'cgroup_after':cg_after,'memory_caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'translation_or_extraction_run':False,'lean_run':False}
(AUDIT/'build-result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
(AUDIT/'cgroup-samples.json').write_text(json.dumps(samples,indent=2,sort_keys=True)+'\n')
(AUDIT/'toolchain.txt').write_text('channel='+CHANNEL+'\n'+rustc+cargo+'sysroot='+sysroot+'\n')
(AUDIT/'build-host-reservation-after.json').write_text(json.dumps({'meminfo_after':meminfo(),'cgroup_after':cgroup()},indent=2,sort_keys=True)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('cgroup_samples','compiler_lines','source_tree_sha256_after')},indent=2))
# Compilation evidence is written before these post-run integrity gates.
assert not changed,{'candidate_source_changed_outside_draft':changed}
assert source_head_after==PIN['revision'],source_head_after
assert source_clean, 'parent Charon tracked worktree changed during isolated build'
assert parent_pins_after=={'get_mir':PIN['base_get_mir'],'wrapper':PIN['wrapper'],'target_charon':PIN['wrapper'],'driver':PIN['driver_before']},parent_pins_after
assert candidate_pins_after=={'wrapper':PIN['wrapper'],'target_charon':PIN['wrapper']},candidate_pins_after
if unexpected:raise SystemExit('stopped: unexpected external dependency compilation')
if timed_out:raise SystemExit('stopped: ten minutes without compiler output/new target event')
if status:raise SystemExit(status)
