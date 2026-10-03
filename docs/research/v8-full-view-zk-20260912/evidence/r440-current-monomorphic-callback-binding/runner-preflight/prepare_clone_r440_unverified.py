#!/usr/bin/env python3
"""UNVERIFIED source-only R440 Charon clone preparer; never execute without lead review."""
import hashlib,json,os,pathlib,shutil,stat,subprocess,threading,time
if os.environ.get('R440_ALLOW_CLONE')!='1':raise SystemExit('R440 clone gate closed')
SRC=pathlib.Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon')
DST=pathlib.Path('/home/dombarker/project-offloads/aspis-r440-mono-closure-binding-20261003-a')
STAGE=pathlib.Path('/tmp/aspis-r440-mono-closure-binding-20261003-a/clone')
AUDIT=DST/'candidate-audit/clone'
PINS=STAGE/'r440-candidate-b-pins.json'
META=STAGE/'candidate-b.json'
PATCH=STAGE/'candidate-b.patch'
OVERLAYS={
 'charon/src/bin/charon-driver/main.rs':STAGE/'main.candidate.rs',
 'charon/src/bin/charon-driver/translate/translate_closures.rs':STAGE/'translate_closures.candidate.rs',
}
PIN={'charon_head':'cb50ff16b9f1066b8a97dc06da704de2da2fa41c','campaign_revision':'3b9e8d7f0122e6dc966a809904adbd722ae3079d','wrapper':'b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c','driver':'4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938','cargo_lock':'c755a326679e9b3dbce560ff15130bdc83ae16178f2c1af568e391b8470d2e67'}
CAPS={'memory.high':str(5*1024**3),'memory.max':str(7*1024**3),'memory.swap.max':'0','pids.max':'128'}
def sha(p):
 h=hashlib.sha256()
 with pathlib.Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def tracked_sha(p):
 p=pathlib.Path(p); raw=os.fsencode(os.readlink(p)) if p.is_symlink() else p.read_bytes()
 return hashlib.sha256(raw).hexdigest()
def git(*args,**kw):return subprocess.check_output(['git','-C',str(SRC),*args],**kw)
def tracked_rows():
 rows=[]
 for record in git('ls-tree','-r','-z','HEAD').split(b'\0'):
  if not record:continue
  meta,path=record.split(b'\t',1);mode,kind,oid=meta.decode().split()
  if kind!='blob':raise RuntimeError(f'unexpected git object {kind}: {path!r}')
  rows.append({'path':path.decode(),'mode':mode,'git_blob_sha1':oid})
 return rows
def git_blob_sha1(p):
 raw=os.fsencode(os.readlink(p)) if p.is_symlink() else p.read_bytes()
 h=hashlib.sha1();h.update(f'blob {len(raw)}\0'.encode());h.update(raw);return h.hexdigest()
def tree_hashes(base,rows):return {r['path']:tracked_sha(base/r['path']) for r in rows}
def cgroup():
 line=next((x for x in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::')),None)
 if not line:return {'path':None}
 p=pathlib.Path('/sys/fs/cgroup')/line.split('::',1)[1].lstrip('/');d={'path':str(p)}
 for k in (*CAPS,'memory.current','memory.peak','memory.swap.current','memory.swap.peak','memory.events'):
  try:d[k]=(p/k).read_text().strip()
  except OSError:pass
 return d
def assert_caps():
 d=cgroup();actual={k:d.get(k) for k in CAPS};assert actual==CAPS,{'expected':CAPS,'actual':actual};return d
def meminfo():
 out={}
 for l in pathlib.Path('/proc/meminfo').read_text().splitlines():
  k,v=l.split(':',1)
  if k in ('MemTotal','MemAvailable','SwapTotal','SwapFree'):out[k]=v.strip()
 return out
def active_reservations(own_unit='aspis-r440-source-clone.service'):
 rows=[];total=0;counted_cgroups=set()
 for manager in ('--user','--system'):
  raw=subprocess.check_output(['systemctl',manager,'list-units','--all','--plain','--no-legend'],text=True)
  for line in raw.splitlines():
   fields=line.split()
   if not fields:continue
   unit=fields[0]
   if not unit.startswith('aspis') or not unit.endswith(('.service','.scope')) or unit==own_unit:continue
   props=subprocess.check_output(['systemctl',manager,'show',unit,'-p','ControlGroup','-p','MemoryMax','-p','MemoryCurrent'],text=True)
   d=dict(x.split('=',1) for x in props.splitlines() if '=' in x);cgname=d.get('ControlGroup','');cgpath=pathlib.Path('/sys/fs/cgroup')/cgname.lstrip('/');pids=[]
   if cgname and cgpath.exists():
    for f in cgpath.rglob('cgroup.procs'):
     try:pids += [x.strip() for x in f.read_text().splitlines() if x.strip()]
     except OSError:pass
   rawcap=d.get('MemoryMax','');finite=rawcap.isdigit() and int(rawcap)>0
   if pids:
    assert finite,{'unit':unit,'manager':manager,'control_group':cgname,'MemoryMax':rawcap,'pids':pids}
    if cgname not in counted_cgroups:
     total+=int(rawcap);counted_cgroups.add(cgname)
   rows.append({'manager':manager,'unit':unit,'control_group':cgname,'pids':pids,'MemoryMax_raw':rawcap,'MemoryMax_bytes':int(rawcap) if finite else None,'MemoryCurrent':d.get('MemoryCurrent')})
 return rows,total
assert SRC.is_dir() and STAGE.is_dir() and not DST.exists(), 'missing source/stage or nonfresh R440 candidate root'
assert git('rev-parse','HEAD',text=True).strip()==PIN['charon_head']
subprocess.run(['git','-C',str(SRC),'diff','--quiet','HEAD','--'],check=True)
subprocess.run(['git','-C',str(SRC),'diff','--cached','--quiet','HEAD','--'],check=True)
assert PINS.is_file() and META.is_file() and PATCH.is_file(), 'Candidate B staged inputs missing'
pins=json.loads(PINS.read_text());meta=json.loads(META.read_text())
assert pins.get('status')=='reviewed-candidate-b-pins', 'Candidate B not lead reviewed; stop before any destination creation'
assert pins.get('campaign_revision')==PIN['campaign_revision'] and pins.get('pinned_charon_revision')==PIN['charon_head']
assert sha(META)==pins['candidate_json_sha256'] and sha(PATCH)==pins['patch_sha256']
assert meta.get('status')=='UNBUILT_LOCAL_DIAGNOSTIC_CANDIDATE_B_V2'
rows=pins.get('overlays',[]);expected=sorted(OVERLAYS)
assert [x['path'] for x in rows]==expected,rows
for x in rows:
 p=SRC/x['path'];candidate=OVERLAYS[x['path']]
 assert p.is_file() and sha(p)==x['original_sha256'],x['path']
 assert candidate.is_file() and sha(candidate)==x['candidate_sha256'],x['path']
 assert sha(SRC/'bin/charon')==PIN['wrapper'] and sha(SRC/'charon/target/release/charon')==PIN['wrapper']
assert sha(SRC/'charon/target/release/charon-driver')==PIN['driver']
assert sha(SRC/'charon/Cargo.lock')==PIN['cargo_lock']
source_tracked=tracked_rows();source_hash=tree_hashes(SRC,source_tracked)
# Verify source and candidate output roots have no pre-existing output/cache before allocating.
assert not (DST/'charon/target').exists()
mem=meminfo();avail=int(mem['MemAvailable'].split()[0])*1024;total=int(mem['MemTotal'].split()[0])*1024
cap=7*1024**3;post=24*1024**3;safe=min(40*1024**3,total-16*1024**3)
assert avail-cap>=post and cap<=safe,{'meminfo':mem,'cap':cap,'post_reserve':post,'safe':safe}
units,reserved=active_reservations();assert cap+reserved<=safe,{'reserved':reserved,'cap':cap,'safe':safe}
heavy=subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines();heavy=[x.strip() for x in heavy if len(x.split())>1 and x.split()[1] in ('cargo','rustc','rustc_driver','charon','charon-driver','aeneas','lean','lean4')];assert not heavy,heavy
worker_cgroup=assert_caps();started=time.monotonic()
# Materialize only committed tracked source. No target cache is copied.
DST.mkdir();arc=subprocess.Popen(['git','-C',str(SRC),'archive','--format=tar',PIN['charon_head']],stdout=subprocess.PIPE)
tar=subprocess.Popen(['tar','-xf','-','-C',str(DST)],stdin=arc.stdout,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);arc.stdout.close();tarlog,_=tar.communicate();arc_status=arc.wait()
assert arc_status==0 and tar.returncode==0,{'git_archive':arc_status,'tar':tar.returncode,'log':tarlog}
for r in source_tracked:
 p=DST/r['path'];assert p.exists() or p.is_symlink(),r['path'];assert git_blob_sha1(p)==r['git_blob_sha1'],r['path']
# Candidate-specific copy2 overlays are the only allowed source deltas.
for r in rows:
 dest=DST/r['path'];shutil.copy2(OVERLAYS[r['path']],dest);assert sha(dest)==r['candidate_sha256'],r['path']
candidate_hash=tree_hashes(DST,source_tracked)
changed=[r['path'] for r in source_tracked if candidate_hash[r['path']]!=source_hash[r['path']]]
assert changed==expected,changed
assert tree_hashes(SRC,source_tracked)==source_hash,'pinned parent changed during source-only clone'
assert sha(SRC/'bin/charon')==PIN['wrapper'] and sha(SRC/'charon/target/release/charon-driver')==PIN['driver']
assert sha(SRC/'charon/Cargo.lock')==PIN['cargo_lock']
assert not (DST/'charon/target').exists(), 'R440 is source-only; target cache must stay in original checkout'
# Confirm archive regular source files do not share source inodes.
shared=[]
for r in source_tracked:
 if r['mode']=='120000':continue
 a=SRC/r['path'];b=DST/r['path']
 if (a.stat().st_dev,a.stat().st_ino)==(b.stat().st_dev,b.stat().st_ino):shared.append(r['path'])
assert not shared,shared[:10]
AUDIT.mkdir(parents=True)
report={'status':'source-only pinned archive with two Candidate B driver overlays; NO build','source_root':str(SRC),'candidate_root':str(DST),'source_head':PIN['charon_head'],'campaign_revision':PIN['campaign_revision'],'tracked_entry_count':len(source_tracked),'tracked_symlink_paths':[r['path'] for r in source_tracked if r['mode']=='120000'],'source_tracked_sha256_before':source_hash,'tracked_source_sha256_before':source_hash,'tracked_candidate_sha256_after_overlay':candidate_hash,'only_tracked_source_differences':changed,'candidate_b_pins_sha256':sha(PINS),'candidate_b_json_sha256':sha(META),'candidate_b_patch_sha256':sha(PATCH),'wrapper_sha256_before':PIN['wrapper'],'driver_sha256_before':PIN['driver'],'cargo_lock_sha256_before':PIN['cargo_lock'],'target_cache_copied':False,'target_cache_location_read_only':str(SRC/'charon/target'),'candidate_target_cache_absent':True,'shared_regular_source_inode_count':len(shared),'meminfo_before':mem,'candidate_memory_max_bytes':cap,'post_cap_available_reserve_bytes':post,'safe_working_limit_bytes':safe,'other_aspis_units':units,'other_aspis_reserved_max_bytes':reserved,'heavy_processes_before':heavy,'effective_cgroup_before':worker_cgroup,'wall_seconds':time.monotonic()-started,'pins':PIN}
(AUDIT/'tracked-tree.json').write_text(json.dumps(source_tracked,indent=2,sort_keys=True)+'\n')
(AUDIT/'clone-audit.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('source_tracked_sha256_before','tracked_source_sha256_before','tracked_candidate_sha256_after_overlay')},indent=2))
