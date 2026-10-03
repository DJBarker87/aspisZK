#!/usr/bin/env python3
"""Focused direct rustc build of the R440 mono-closure-binding Charon candidate; never run without lead authorization."""
import hashlib,json,os,pathlib,queue,re,shutil,signal,subprocess,threading,time

if os.environ.get('R440_ALLOW_DIRECT_DRIVER_BUILD')!='1':
 raise SystemExit('direct build gate closed; require R440_ALLOW_DIRECT_DRIVER_BUILD=1 after lead review')
SRC=pathlib.Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon')
ROOT=pathlib.Path('/home/dombarker/project-offloads/aspis-r440-mono-closure-binding-20261003-a')
ORIGINAL_TARGET=SRC/'charon/target'
WORKER_DIR=pathlib.Path('/tmp/aspis-r440-mono-closure-binding-20261003-a/direct-driver-build')
AUDIT=ROOT/'candidate-audit/direct-driver-build'
SELECTION=WORKER_DIR/'direct-driver-input-selection.json'
TARGET_CACHE_MANIFEST=WORKER_DIR/'target-cache-sha256.json'
SELECTION_SHA='98cb2179333d9225be055ed61267a09286448b87b3b1e7fafad15de009790d97'
SOURCE_REV='cb50ff16b9f1066b8a97dc06da704de2da2fa41c'  # pinned Charon checkout
CAMPAIGN_REV='3b9e8d7f0122e6dc966a809904adbd722ae3079d'  # R440 candidate provenance
RUSTC_COMMIT='14210df0e27ccd7d9e6a05b8085cbd438e4bbc65'
WRAPPER_SHA='b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c'
DRIVER_BEFORE_SHA='4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938'
CARGO_LOCK_SHA='c755a326679e9b3dbce560ff15130bdc83ae16178f2c1af568e391b8470d2e67'
RUSTUP='/home/dombarker/.cargo/bin/rustup'
CHANNEL='nightly-2026-06-01'
NATIVE_REL=[
 'release/build/psm-0054b740d3e1ad34/out/4f9a91766097c4c5-x86_64.o',
 'release/build/psm-0054b740d3e1ad34/out/libpsm_s.a',
]

def sha(p):
 h=hashlib.sha256()
 with pathlib.Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def tracked_sha(p):
 p=pathlib.Path(p)
 if p.is_symlink():return hashlib.sha256(os.fsencode(os.readlink(p))).hexdigest()
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def digest_or_none(p):
 try:return tracked_sha(p)
 except FileNotFoundError:return None
def file_record(base,relative):
 p=base/relative
 try:return {'name':relative,'sha256':sha(p),'size':p.stat().st_size}
 except FileNotFoundError:return {'name':relative,'sha256':None,'size':None}
def git(*args):return subprocess.check_output(['git','-C',str(SRC),*args],text=True).strip()
def assert_parent_clean():
 assert git('rev-parse','HEAD')==SOURCE_REV
 subprocess.run(['git','-C',str(SRC),'diff','--quiet','HEAD','--'],check=True)
 subprocess.run(['git','-C',str(SRC),'diff','--cached','--quiet','HEAD','--'],check=True)
def tracked_tree_hashes(base,rows):
 return {r['path']:digest_or_none(base/r['path']) for r in rows}
def target_cache_hashes():
 rows=json.loads(TARGET_CACHE_MANIFEST.read_text())
 expected={r['path']:r['sha256'] for r in rows if r['path'].startswith('release/deps/')}
 base=ORIGINAL_TARGET;actual={}
 for p in (base/'release/deps').rglob('*'):
  if p.is_file() or p.is_symlink():actual[p.relative_to(base).as_posix()]=tracked_sha(p)
 return {'expected_count':len(expected),'actual_count':len(actual),'expected_sha256':expected,'observed_sha256':actual}
def cgroup():
 line=next((x for x in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::')),None)
 if not line:return {'path':None}
 p=pathlib.Path('/sys/fs/cgroup')/line.split('::',1)[1].lstrip('/');d={'path':str(p)}
 for n in ('memory.current','memory.peak','memory.high','memory.max','memory.swap.current','memory.swap.peak','memory.swap.max','memory.events','pids.current','pids.max'):
  try:d[n]=(p/n).read_text().strip()
  except OSError:pass
 return d
def assert_caps():
 d=cgroup();e={'memory.high':str(5*1024**3),'memory.max':str(7*1024**3),'memory.swap.max':'0','pids.max':'128'}
 a={k:d.get(k) for k in e};assert a==e,{'expected':e,'actual':a,'cgroup':d};return d
def read_mem():
 wanted={'MemTotal','MemAvailable','SwapTotal','SwapFree'};out={}
 for line in pathlib.Path('/proc/meminfo').read_text().splitlines():
  k,v=line.split(':',1)
  if k in wanted:out[k]=v.strip()
 return out
def reservations(own_unit='aspis-r440-direct-driver.service'):
 rows=[];used=0;counted_cgroups=set()
 for manager in ('--user','--system'):
  listed=subprocess.check_output(['systemctl',manager,'list-units','--all','--plain','--no-legend'],text=True).splitlines()
  for line in listed:
   fields=line.split()
   if not fields:continue
   name=fields[0]
   if not name.startswith('aspis') or not name.endswith(('.service','.scope')) or name==own_unit:continue
   props=subprocess.check_output(['systemctl',manager,'show',name,'-p','ControlGroup','-p','MemoryMax','-p','MemoryCurrent'],text=True)
   d=dict(x.split('=',1) for x in props.splitlines() if '=' in x)
   cgname=d.get('ControlGroup','');cg=pathlib.Path('/sys/fs/cgroup')/cgname.lstrip('/')
   pids=[]
   if cgname and cg.exists():
    for f in cg.rglob('cgroup.procs'):
     try:pids.extend(x.strip() for x in f.read_text().splitlines() if x.strip())
     except OSError:pass
   rawcap=d.get('MemoryMax','')
   finite=rawcap.isdigit() and int(rawcap)>0
   if pids:
    assert finite,{'unit':name,'manager':manager,'control_group':cgname,'MemoryMax':rawcap,'pids':pids}
    if cgname not in counted_cgroups:
     used+=int(rawcap);counted_cgroups.add(cgname)
   rows.append({'manager':manager,'unit':name,'control_group':cgname,'pids':pids,'MemoryMax_raw':rawcap,'MemoryMax_bytes':int(rawcap) if finite else None,'MemoryCurrent':d.get('MemoryCurrent')})
 return rows,used
def safe_sources(selection,tracked):
 return {
  'revision':git('rev-parse','HEAD'),
  'candidate_translate_closures_sha256':digest_or_none(ROOT/'charon/src/bin/charon-driver/translate/translate_closures.rs'),
  'candidate_main_sha256':digest_or_none(ROOT/'charon/src/bin/charon-driver/main.rs'),
  'candidate_Cargo_toml_sha256':digest_or_none(ROOT/'charon/Cargo.toml'),
  'candidate_Cargo_lock_sha256':digest_or_none(ROOT/'charon/Cargo.lock'),
  'candidate_rust_toolchain_sha256':digest_or_none(ROOT/'charon/rust-toolchain'),
  'original_translate_closures_sha256':digest_or_none(SRC/'charon/src/bin/charon-driver/translate/translate_closures.rs'),
  'original_Cargo_lock_sha256':digest_or_none(SRC/'charon/Cargo.lock'),
  'candidate_wrapper_source_sha256':digest_or_none(SRC/'bin/charon'),
  'original_wrapper_sha256':digest_or_none(SRC/'charon/target/release/charon'),
  'original_driver_sha256':digest_or_none(SRC/'charon/target/release/charon-driver'),
  'externs':[{ 'name':x['name'],'relative_path':x['path'],'sha256':digest_or_none(SRC/x['path']),'size':((SRC/x['path']).stat().st_size if (SRC/x['path']).exists() else None)} for x in selection['selected_externs']],
  'native':[{'relative_path':p,**file_record(ORIGINAL_TARGET,p)} for p in NATIVE_REL],
  'release_deps_sha256':target_cache_hashes(),
  'parent_tracked_source_sha256':tracked_tree_hashes(SRC,tracked),
  'candidate_tracked_source_sha256':tracked_tree_hashes(ROOT,tracked),
 }

assert ROOT.is_dir() and not AUDIT.exists(),f'candidate missing or attempt audit already exists: {AUDIT}'
assert not (ROOT/'charon/target').exists(), 'source-only clone unexpectedly contains a copied target cache'
assert SELECTION.is_file() and sha(SELECTION)==SELECTION_SHA,(str(SELECTION),sha(SELECTION) if SELECTION.exists() else None)
selection=json.loads(SELECTION.read_text())
assert selection['classification']=='lead explicit standalone diagnostic compilation inputs; not reconstruction of prior Cargo argv'
assert len(selection['selected_externs'])==46
assert selection['dependency_count']==46 and selection['native_build_output_entries']
assert selection['flags']==['--crate-name','charon_driver','--edition=2024','--crate-type','bin','--cfg','feature="default"','--cfg','feature="rustc"','-C','opt-level=3','-C','codegen-units=16','-C','debuginfo=0','-C','panic=unwind','--emit=link']
assert_parent_clean()
parent_git_before={'head':git('rev-parse','HEAD'),'porcelain':git('status','--porcelain=v1','--untracked-files=no')}
# Compare the complete pinned Charon tracked source tree, preserving symlink target bytes.
clone_audit=ROOT/'candidate-audit/clone'
tracked=json.loads((clone_audit/'tracked-tree.json').read_text())
clone_record=json.loads((clone_audit/'clone-audit.json').read_text())
assert clone_record['source_head']==SOURCE_REV and clone_record['only_tracked_source_differences']==['charon/src/bin/charon-driver/main.rs','charon/src/bin/charon-driver/translate/translate_closures.rs']
expected_source=clone_record['tracked_source_sha256_before'];expected_candidate=clone_record['tracked_candidate_sha256_after_overlay']
changed=clone_record.get('only_tracked_source_differences',clone_record.get('only_tracked_source_difference'))
assert changed==['charon/src/bin/charon-driver/main.rs','charon/src/bin/charon-driver/translate/translate_closures.rs'], changed
assert tracked_tree_hashes(SRC,tracked)==expected_source,'parent tracked source differs from audited source snapshot'
assert tracked_tree_hashes(ROOT,tracked)==expected_candidate,'candidate tracked source differs from audited overlay snapshot'
assert sha(SRC/'bin/charon')==WRAPPER_SHA and sha(SRC/'charon/target/release/charon')==WRAPPER_SHA
assert sha(SRC/'charon/target/release/charon-driver')==DRIVER_BEFORE_SHA
B_PINS=WORKER_DIR/'r440-candidate-b-pins.json'
B_JSON=WORKER_DIR/'candidate-b.json'
B_PATCH=WORKER_DIR/'candidate-b.patch'
assert B_PINS.is_file() and B_JSON.is_file() and B_PATCH.is_file(), 'Candidate B pin/artifact files missing; refuse launch'
bpins=json.loads(B_PINS.read_text())
assert bpins.get('status')=='reviewed-candidate-b-pins'
assert bpins.get('campaign_revision')==CAMPAIGN_REV
assert bpins.get('pinned_charon_revision')==SOURCE_REV
assert sha(B_JSON)==bpins.get('candidate_json_sha256')
assert sha(B_PATCH)==bpins.get('patch_sha256')
B_PINS_SHA=sha(B_PINS)
overlay_paths=['charon/src/bin/charon-driver/main.rs','charon/src/bin/charon-driver/translate/translate_closures.rs']
assert [r['path'] for r in bpins.get('overlays',[])]==overlay_paths, bpins
for row in bpins['overlays']:
 assert row.get('original_sha256') and row.get('candidate_sha256'), row
 assert sha(ROOT/row['path'])==row['candidate_sha256'], row['path']
 assert sha(SRC/row['path'])==row['original_sha256'], row['path']
assert sha(ROOT/'charon/Cargo.lock')==CARGO_LOCK_SHA
for x in selection['selected_externs']:
 p=SRC/x['path'];assert p.is_file() and p.stat().st_size==x['size'] and sha(p)==x['sha256'],x
for x in selection['native_build_output_entries']:
 p=ORIGINAL_TARGET/x['path'];assert p.is_file() and p.stat().st_size==x['size'] and sha(p)==x['sha256'],x
assert [x['path'] for x in selection['native_build_output_entries']]==NATIVE_REL
source_before=safe_sources(selection,tracked)
assert source_before['revision']==SOURCE_REV
pin_by_path={r['path']:r for r in bpins['overlays']}
assert source_before['candidate_main_sha256']==pin_by_path['charon/src/bin/charon-driver/main.rs']['candidate_sha256']
assert source_before['candidate_translate_closures_sha256']==pin_by_path['charon/src/bin/charon-driver/translate/translate_closures.rs']['candidate_sha256']
assert source_before['candidate_wrapper_source_sha256']==WRAPPER_SHA and source_before['original_driver_sha256']==DRIVER_BEFORE_SHA
assert len(source_before['release_deps_sha256']['observed_sha256'])==source_before['release_deps_sha256']['expected_count']
assert source_before['release_deps_sha256']['observed_sha256']==source_before['release_deps_sha256']['expected_sha256']
mem=read_mem();avail=int(mem['MemAvailable'].split()[0])*1024;total=int(mem['MemTotal'].split()[0])*1024;cap=7*1024**3;reserve=24*1024**3;safe=min(40*1024**3,total-16*1024**3)
assert avail-cap>=reserve,{'meminfo':mem,'candidate_cap':cap,'reserve':reserve};assert cap<=safe,{'cap':cap,'safe':safe}
units,othermax=reservations();assert cap+othermax<=safe,{'other_reserved':othermax,'candidate':cap,'safe':safe}
procs=subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines();heavy=[x.strip() for x in procs if len(x.split())>1 and x.split()[1] in ('cargo','rustc','rustc_driver','charon','charon-driver','aeneas','lean','lean4')]
assert not heavy,heavy
rustc=subprocess.check_output([RUSTUP,'run',CHANNEL,'rustc','--version','--verbose'],text=True);assert RUSTC_COMMIT in rustc,rustc
sysroot=subprocess.check_output([RUSTUP,'run',CHANNEL,'rustc','--print','sysroot'],text=True).strip()
assert '1.98.0-nightly' in rustc and pathlib.Path(sysroot).is_dir()
OUT=ROOT/'observer-bin';BIN=OUT/'charon-driver';WRAP=OUT/'charon';assert not OUT.exists(),f'fresh output directory already exists: {OUT}'
AUDIT.mkdir(parents=True)
OUT.mkdir();shutil.copy2(SRC/'bin/charon',WRAP);assert sha(WRAP)==WRAPPER_SHA
assert (WRAP.stat().st_dev,WRAP.stat().st_ino)!=((SRC/'bin/charon').stat().st_dev,(SRC/'bin/charon').stat().st_ino), 'copied wrapper unexpectedly shares source inode'
dependency_dir=ORIGINAL_TARGET/'release/deps';native_dir=ORIGINAL_TARGET/'release/build/psm-0054b740d3e1ad34/out'
flags=list(selection['flags']);command=[RUSTUP,'run',CHANNEL,'rustc',*flags]
for x in selection['selected_externs']:command+=['--extern',f"{x['name']}={SRC/x['path']}"]
command+=['-L',f'dependency={dependency_dir}','-L',f'native={native_dir}','-o',str(BIN),str(ROOT/'charon/src/bin/charon-driver/main.rs')]
pre={'status':'all direct rustc input pins passed; compile not yet started','source_revision':SOURCE_REV,'campaign_source_revision':CAMPAIGN_REV,'overlay_pins':bpins['overlays'],'candidate_b_json_sha256':bpins['candidate_json_sha256'],'candidate_b_patch_sha256':bpins['patch_sha256'],'candidate_b_pin_manifest_sha256':B_PINS_SHA,'candidate_root':str(ROOT),'output_driver':str(BIN),'output_wrapper':str(WRAP),'wrapper_sha256':sha(WRAP),'selection_sha256':SELECTION_SHA,'dependency_count':len(selection['selected_externs']),'native_inputs':source_before['native'],'inputs_before':source_before,'rustc_version':rustc,'rustc_commit':RUSTC_COMMIT,'sysroot':sysroot,'command':command,'working_directory':str(ROOT/'charon'),'no_cargo_invocation':True,'no_dependency_compilation':True,'historical_Cargo_profile_equivalence_claimed':False,'memory_caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'effective_cgroup_before':assert_caps(),'meminfo_before':mem,'other_aspis_units':units,'other_aspis_reserved_max_bytes':othermax,'safe_working_limit_bytes':safe,'heavy_processes':heavy,'expected_work':'one direct rustc driver compilation, codegen, and link using pinned cached libraries','stop_conditions':['10 minutes from compiler start without completion','OOM/OOM-kill','any source or selected input hash drift']}
(AUDIT/'direct-command.json').write_text(json.dumps(pre,indent=2,sort_keys=True)+'\n')
(AUDIT/'direct-input-selection.json').write_text(json.dumps(selection,indent=2,sort_keys=True)+'\n')
(AUDIT/'reservation-before.json').write_text(json.dumps({'meminfo':mem,'other_units':units,'other_reserved_max_bytes':othermax,'cgroup':cgroup()},indent=2,sort_keys=True)+'\n')

started=time.monotonic();lines=[];timed_out=False;oom=False;samples=[];stop=threading.Event();messages=queue.Queue()
def sampler():
 while not stop.is_set():
  d=cgroup();samples.append({'monotonic':time.monotonic(),**d})
  values={}
  for line in d.get('memory.events','').splitlines():
   bits=line.split()
   if len(bits)==2:values[bits[0]]=int(bits[1])
  now_events=values
  if any(now_events.get(k,0)>oom_baseline.get(k,0) for k in ('oom','oom_kill','oom_group_kill')):stop.set();return
  stop.wait(.5)
oom_baseline={}
for _line in cgroup().get('memory.events','').splitlines():
 _bits=_line.split()
 if len(_bits)==2:oom_baseline[_bits[0]]=int(_bits[1])
thread=threading.Thread(target=sampler,daemon=True);thread.start()
timefile=AUDIT/'rustc-gnu-time.txt';log=AUDIT/'rustc.stdout.log'
# GNU time is the process-group leader. The monitor terminates its rustup/rustc descendants on a gate failure, then waits for GNU time to write full accounting.
timed_command=['/usr/bin/time','-v','-o',str(timefile),*command]
proc=subprocess.Popen(timed_command,cwd=ROOT/'charon',env={**os.environ,'PATH':'/home/dombarker/.cargo/bin:'+os.environ.get('PATH',''),'RUSTUP_TOOLCHAIN':CHANNEL},stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,bufsize=1,start_new_session=True)
def reader():
 for line in proc.stdout:messages.put(line)
 messages.put(None)
rt=threading.Thread(target=reader,daemon=True);rt.start();eof=False
def descendants(pid):
 table={}
 for p in pathlib.Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:
   raw=(p/'stat').read_text();parts=raw[raw.rfind(')')+2:].split();table[int(p.name)]=int(parts[1])
  except (OSError,ValueError,IndexError):pass
 found=set();front=[pid]
 while front:
  q=front.pop()
  for child,parent in table.items():
   if parent==q and child not in found:found.add(child);front.append(child)
 return found
with log.open('w') as f:
 while not eof:
  if stop.is_set():oom=True;break
  try:line=messages.get(timeout=.5)
  except queue.Empty:
   if time.monotonic()-started>600:timed_out=True;break
   continue
  if line is None:eof=True;break
  f.write(line);f.flush();lines.append(line.rstrip('\n'))
if timed_out or oom:
 for pid in sorted(descendants(proc.pid),reverse=True):
  try:os.kill(pid,signal.SIGTERM)
  except ProcessLookupError:pass
 try:proc.wait(timeout=10)
 except subprocess.TimeoutExpired:
  for pid in sorted(descendants(proc.pid),reverse=True):
   try:os.kill(pid,signal.SIGKILL)
   except ProcessLookupError:pass
  proc.wait()
else:proc.wait()
rt.join(timeout=5)
with log.open('a') as f:
 while True:
  try:line=messages.get_nowait()
  except queue.Empty:break
  if line is not None:f.write(line);lines.append(line.rstrip('\n'))
status=proc.returncode;stop.set();thread.join();
source_after=safe_sources(selection,tracked);target_exists=BIN.is_file();driver_sha=sha(BIN) if target_exists else None
assert sha(B_PINS)==B_PINS_SHA and sha(B_JSON)==bpins['candidate_json_sha256'] and sha(B_PATCH)==bpins['patch_sha256'], 'Candidate B pin artifacts changed during build'
gnu=timefile.read_text() if timefile.exists() else ''
def metric(pattern):
 m=re.search(pattern,gnu,re.M);return m.group(1).strip() if m else None
oom_seen=False
for s in samples:
 for line in s.get('memory.events','').splitlines():
  p=line.split()
  if len(p)==2 and p[0] in ('oom','oom_kill','oom_group_kill') and int(p[1])>oom_baseline.get(p[0],0):oom_seen=True
result={'rustc_exit_status':status,'target_exists':target_exists,'driver_sha256':driver_sha,'driver_size_bytes':BIN.stat().st_size if target_exists else None,'wrapper_sha256':sha(WRAP),'wall_seconds_worker':time.monotonic()-started,'gnu_time_elapsed':metric(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*(.+)'),'gnu_time_peak_rss_kib':int(metric(r'Maximum resident set size \(kbytes\):\s*(\d+)') or 0),'gnu_time_swaps':int(metric(r'Swaps:\s*(\d+)') or 0),'gnu_time_exit_status':int(metric(r'Exit status:\s*(\d+)') or -1),'no_output_or_target_growth_timeout':timed_out,'oom_detected':oom_seen,'lines':lines,'candidate_b_json_sha256':bpins['candidate_json_sha256'],'candidate_b_patch_sha256':bpins['patch_sha256'],'candidate_b_pin_manifest_sha256':B_PINS_SHA,'inputs_before':source_before,'inputs_after':source_after,'inputs_unchanged':source_before==source_after,'parent_git_before':parent_git_before,'parent_git_after':{'head':git('rev-parse','HEAD'),'porcelain':git('status','--porcelain=v1','--untracked-files=no')},'cgroup_after':cgroup(),'cgroup_samples':samples,'memory_caps':{'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128},'cargo_invocation':False,'dependency_compilation':False,'historical_Cargo_profile_equivalence_claimed':False}
(AUDIT/'direct-result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
(AUDIT/'cgroup-samples.json').write_text(json.dumps(samples,indent=2,sort_keys=True)+'\n')
(AUDIT/'reservation-after.json').write_text(json.dumps({'meminfo_after':read_mem(),'cgroup_after':cgroup()},indent=2,sort_keys=True)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('lines','cgroup_samples','inputs_before','inputs_after')},indent=2))
assert source_before==source_after, 'source/cache input hash drift during direct compile'
assert result['parent_git_after']==parent_git_before, 'parent source checkout changed during direct compile'
assert_parent_clean()
if timed_out:raise SystemExit('stopped: 10 minutes without stdout or target growth')
if oom:raise SystemExit('stopped: cgroup OOM/OOM-kill event')
if status:raise SystemExit(status)
