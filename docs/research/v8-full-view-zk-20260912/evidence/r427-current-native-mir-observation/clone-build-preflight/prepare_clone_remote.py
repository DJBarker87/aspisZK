#!/usr/bin/env python3
"""R427 remote isolated archive/copy/one-file overlay. Unlaunched preparation."""
import hashlib, json, os, pathlib, shutil, stat, subprocess, threading, time

if os.environ.get('R427_ALLOW_CLONE') != '1':
    raise SystemExit('clone launch gate closed: require R427_ALLOW_CLONE=1 after lead review')
SRC=pathlib.Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon')
DST=pathlib.Path('/home/dombarker/project-offloads/aspis-r427-raw-mir-observer-20261002-a')
STAGE=pathlib.Path('/tmp/aspis-r427-raw-mir-observer-20261002-a')
DRAFT=STAGE/'get_mir.diagnostic.UNVERIFIED.rs'
AUDIT=DST/'candidate-audit/clone'
PIN={
 'revision':'cb50ff16b9f1066b8a97dc06da704de2da2fa41c',
 'draft_sha256':'246d1fec2223d8ad5755e4aa9f24e647af7c16a18a8a2d893d9085213bf8a9ab',
 'base_get_mir_sha256':'e6461421d16dc4e9e1a7e5f097e8aab455513b1a290b780c90afc4f3f5765964',
 'wrapper_sha256':'b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c',
 'driver_before_sha256':'4cb603ad51132f298a63a9c2a8cc8c629c73edeff22516fbf56ba5decee70938',
 'cargo_toml_sha256':'a31bab7d34638f8c2a43f14263184a3328ab17366c2f9acf201d86b922c4176f',
 'cargo_lock_sha256':'c755a326679e9b3dbce560ff15130bdc83ae16178f2c1af568e391b8470d2e67',
 'nested_toolchain_sha256':'27e050e8fc5ac827e1264abf38c27fcaf18e73f4305104c866179cb84721898c',
}

def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''): h.update(b)
 return h.hexdigest()
def tracked_sha(p):
 raw=os.fsencode(os.readlink(p)) if p.is_symlink() else p.read_bytes()
 return hashlib.sha256(raw).hexdigest()
def git(*args,**kw): return subprocess.check_output(['git','-C',str(SRC),*args],**kw)
def expected_tracked():
 rows=[]
 for record in git('ls-tree','-r','-z','HEAD').split(b'\0'):
  if not record: continue
  meta,path=record.split(b'\t',1); mode,kind,oid=meta.decode().split()
  if kind!='blob': raise RuntimeError(f'unexpected tracked non-blob {path!r}: {kind}')
  rows.append({'path':path.decode(),'mode':mode,'git_blob_sha1':oid})
 return rows
def file_manifest(root):
 rows=[]
 for cur,dirs,files in os.walk(root,topdown=True,followlinks=False):
  dirs.sort(); files.sort(); base=pathlib.Path(cur)
  for n in list(dirs):
   p=base/n; st=p.lstat()
   if stat.S_ISLNK(st.st_mode):
    rows.append({'path':p.relative_to(root).as_posix(),'kind':'symlink','target':os.readlink(p),'mode':stat.S_IMODE(st.st_mode)}); dirs.remove(n)
  for n in files:
   p=base/n; st=p.lstat(); rel=p.relative_to(root).as_posix()
   if stat.S_ISLNK(st.st_mode): rows.append({'path':rel,'kind':'symlink','target':os.readlink(p),'mode':stat.S_IMODE(st.st_mode)})
   elif stat.S_ISREG(st.st_mode): rows.append({'path':rel,'kind':'file','size':st.st_size,'sha256':sha(p),'mode':stat.S_IMODE(st.st_mode),'dev':st.st_dev,'ino':st.st_ino})
   else: raise RuntimeError(f'unexpected file type {p}')
 return rows
def git_blob_sha1(p):
 # Git stores symlink blobs as the link-target bytes, not the target contents.
 raw=os.fsencode(os.readlink(p)) if p.is_symlink() else p.read_bytes()
 h=hashlib.sha1(); h.update(f'blob {len(raw)}\0'.encode()); h.update(raw)
 return h.hexdigest()
def read_mem():
 keys={'MemTotal','MemAvailable','SwapTotal','SwapFree'}; out={}
 for line in pathlib.Path('/proc/meminfo').read_text().splitlines():
  k,v=line.split(':',1)
  if k in keys: out[k]=v.strip()
 return out
def cgroup_snapshot():
 line=next((x for x in pathlib.Path('/proc/self/cgroup').read_text().splitlines() if x.startswith('0::')),None)
 if not line: return {'path':None}
 cg=pathlib.Path('/sys/fs/cgroup')/line.split('::',1)[1].lstrip('/'); d={'path':str(cg)}
 for n in ('memory.current','memory.peak','memory.high','memory.max','memory.swap.current','memory.swap.peak','memory.swap.max','memory.events','pids.current','pids.max'):
  try:d[n]=(cg/n).read_text().strip()
  except OSError:pass
 return d
def assert_effective_caps():
 d=cgroup_snapshot(); expected={'memory.high':str(5*1024**3),'memory.max':str(7*1024**3),'memory.swap.max':'0','pids.max':'128'}
 actual={k:d.get(k) for k in expected}
 assert actual==expected,{'expected':expected,'actual':actual,'cgroup':d}
 return d
def sample_start():
 stop=threading.Event(); rows=[]
 def loop():
  while not stop.is_set(): rows.append({'time_monotonic':time.monotonic(),**cgroup_snapshot()}); stop.wait(.5)
 th=threading.Thread(target=loop,daemon=True); th.start(); return stop,th,rows

assert SRC.is_dir() and not DST.exists(), f'source missing or destination already exists: {DST}'
assert DRAFT.is_file() and sha(DRAFT)==PIN['draft_sha256'], 'staged draft missing/hash mismatch'
assert git('rev-parse','HEAD',text=True).strip()==PIN['revision']
subprocess.run(['git','-C',str(SRC),'diff','--quiet','HEAD','--'],check=True)
subprocess.run(['git','-C',str(SRC),'diff','--cached','--quiet','HEAD','--'],check=True)
tracked=expected_tracked()
# Ensure the tracked source set contains the exact build inputs from the pin receipt.
for rel,key in [('charon/src/bin/charon-driver/translate/get_mir.rs','base_get_mir_sha256'),('charon/Cargo.toml','cargo_toml_sha256'),('charon/Cargo.lock','cargo_lock_sha256'),('charon/rust-toolchain','nested_toolchain_sha256')]:
 p=SRC/rel; assert p.is_file() and sha(p)==PIN[key],(rel,sha(p),PIN[key])
assert sha(SRC/'bin/charon')==PIN['wrapper_sha256']
assert sha(SRC/'charon/target/release/charon')==PIN['wrapper_sha256']
assert sha(SRC/'charon/target/release/charon-driver')==PIN['driver_before_sha256']
# Snapshot parent working-tree differences exactly; git archive below includes tracked HEAD only.
untracked=git('status','--porcelain=v1','-z').split(b'\0')
mem=read_mem(); avail=int(mem['MemAvailable'].split()[0])*1024; total=int(mem['MemTotal'].split()[0])*1024
candidate_max=7*1024**3; reserve=24*1024**3; safe=min(40*1024**3,total-16*1024**3)
assert avail-candidate_max>=reserve, {'mem':mem,'candidate_cap':candidate_max,'post_cap_reserve':reserve}
assert candidate_max<=safe, {'candidate_cap':candidate_max,'safe_limit':safe}
worker_cgroup=assert_effective_caps()
processes=subprocess.check_output(['ps','-eo','pid=,comm='],text=True).splitlines()
heavy=[x.strip() for x in processes if len(x.split())>=2 and x.split()[1] in ('cargo','rustc','rustc_driver','charon','charon-driver','aeneas','lean','lean4')]
assert not heavy,heavy
# Fail closed if another Aspis-capped unit is populated or its reservation leaves too little headroom.
units=subprocess.check_output(['systemctl','--user','list-units','--all','--type=service','--no-legend'],text=True).splitlines(); other_units=[]; other_max=0
for line in units:
 name=line.split()[0]
 if not name.startswith('aspis') or name=='aspisr427-clone.service': continue
 props=subprocess.check_output(['systemctl','--user','show',name,'-p','ControlGroup','-p','MemoryMax','-p','MemoryCurrent'],text=True)
 d=dict(x.split('=',1) for x in props.splitlines() if '=' in x); cg=pathlib.Path('/sys/fs/cgroup')/d.get('ControlGroup','').lstrip('/'); pids=[]
 if cg.exists():
  for f in cg.rglob('cgroup.procs'):
   try:pids.extend(x.strip() for x in f.read_text().splitlines() if x.strip())
   except OSError:pass
 maxv=int(d.get('MemoryMax','0')) if d.get('MemoryMax','0').isdigit() else 0
 if pids:other_max+=maxv
 other_units.append({'unit':name,'pids':pids,'memory_max_bytes':maxv,'memory_current_bytes':int(d.get('MemoryCurrent','0') or 0)})
assert not any(x['pids'] for x in other_units),other_units
assert other_max+candidate_max<=safe,{'other_active_aspis_max':other_max,'candidate_cap':candidate_max,'safe_limit':safe}
started=time.monotonic(); stop,th,samples=sample_start()
DST.mkdir()
# Extract precisely the pinned committed tree, excluding all untracked and ignored files.
archive=subprocess.Popen(['git','-C',str(SRC),'archive','--format=tar',PIN['revision']],stdout=subprocess.PIPE)
tar=subprocess.Popen(['tar','-xf','-','-C',str(DST)],stdin=archive.stdout,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
archive.stdout.close(); tarlog, _=tar.communicate(); astatus=archive.wait()
assert astatus==0 and tar.returncode==0, {'git_archive_status':astatus,'tar_status':tar.returncode,'tar_output':tarlog}
# Verify every archived tracked blob against the committed Git object identity.
for row in tracked:
 p=DST/row['path']
 if row['mode']=='120000': assert p.is_symlink(),row['path']
 else: assert p.is_file() and not p.is_symlink(),row['path']
 assert git_blob_sha1(p)==row['git_blob_sha1'], row['path']
# The pinned ignored compiler cache is copied separately, with copy2, never hardlinks.
cache_src=SRC/'charon/target'; cache_dst=DST/'charon/target'
assert cache_src.is_dir() and not cache_dst.exists()
shutil.copytree(cache_src,cache_dst,symlinks=True,copy_function=shutil.copy2)
# `bin/charon` is an ignored runtime wrapper; the archive intentionally omits it.
wrapper_src=SRC/'bin/charon'; wrapper_dst=DST/'bin/charon'
parent_wrapper_inode=(wrapper_src.stat().st_dev,wrapper_src.stat().st_ino)
parent_target_inode=((cache_src/'release/charon').stat().st_dev,(cache_src/'release/charon').stat().st_ino)
assert not wrapper_dst.exists(); wrapper_dst.parent.mkdir(parents=True,exist_ok=True); shutil.copy2(wrapper_src,wrapper_dst)
assert sha(wrapper_dst)==PIN['wrapper_sha256'] and sha(cache_dst/'release/charon')==PIN['wrapper_sha256']
clone_wrapper_inode=(wrapper_dst.stat().st_dev,wrapper_dst.stat().st_ino)
clone_target_inode=((cache_dst/'release/charon').stat().st_dev,(cache_dst/'release/charon').stat().st_ino)
assert clone_wrapper_inode!=parent_wrapper_inode,{'clone_wrapper_inode':clone_wrapper_inode,'parent_wrapper_inode':parent_wrapper_inode}
assert clone_target_inode!=parent_target_inode,{'clone_target_inode':clone_target_inode,'parent_target_inode':parent_target_inode}
assert clone_wrapper_inode!=clone_target_inode,{'clone_wrapper_inode':clone_wrapper_inode,'clone_target_inode':clone_target_inode}
source_cache=file_manifest(cache_src); copied_cache=file_manifest(cache_dst)
def portable(rows):return [{k:v for k,v in r.items() if k not in ('dev','ino')} for r in rows]
assert portable(source_cache)==portable(copied_cache), 'copied target cache content/mode inventory mismatch'
source_regular={x['path']:x for x in source_cache if x['kind']=='file'}; clone_regular={x['path']:x for x in copied_cache if x['kind']=='file'}
shared=[p for p,x in source_regular.items() if (x['dev'],x['ino'])==(clone_regular[p]['dev'],clone_regular[p]['ino'])]
assert not shared,shared[:10]
base=DST/'charon/src/bin/charon-driver/translate/get_mir.rs'
assert sha(base)==PIN['base_get_mir_sha256']
shutil.copy2(DRAFT,base)
assert sha(base)==PIN['draft_sha256']
# Check committed-source tree exactly, allowing only the one approved overlay.
source_hashes={}; clone_hashes={}; changed=[]
for row in tracked:
 p=pathlib.Path(row['path']); source=SRC/p; clone=DST/p
 source_hashes[row['path']]=tracked_sha(source); clone_hashes[row['path']]=tracked_sha(clone)
 expected=PIN['draft_sha256'] if row['path']=='charon/src/bin/charon-driver/translate/get_mir.rs' else source_hashes[row['path']]
 if clone_hashes[row['path']]!=expected: changed.append(row['path'])
assert not changed,changed
AUDIT.mkdir(parents=True,exist_ok=True)
report={'status':'ordinary pinned archive and copy completed; one-file diagnostic draft overlaid; NO build/extraction/translation','source_root':str(SRC),'candidate_root':str(DST),'source_head':PIN['revision'],'tracked_entry_count':len(tracked),'tracked_symlink_paths':[r['path'] for r in tracked if r['mode']=='120000'],'tracked_symlink_count':sum(r['mode']=='120000' for r in tracked),'parent_porcelain_untracked_records':[x.hex() for x in untracked if x],'tracked_worktree_clean':True,'source_draft_sha256':sha(DRAFT),'baseline_get_mir_sha256':PIN['base_get_mir_sha256'],'candidate_get_mir_sha256':sha(base),'only_tracked_source_difference':['charon/src/bin/charon-driver/translate/get_mir.rs'],'source_wrapper_before_sha256':sha(wrapper_src),'candidate_wrapper_sha256':sha(wrapper_dst),'source_target_charon_sha256':sha(cache_src/'release/charon'),'candidate_target_charon_sha256':sha(cache_dst/'release/charon'),'source_target_driver_before_sha256':sha(cache_src/'release/charon-driver'),'candidate_target_driver_before_sha256':sha(cache_dst/'release/charon-driver'),'parent_wrapper_inode':parent_wrapper_inode,'clone_wrapper_inode':clone_wrapper_inode,'parent_target_charon_inode':parent_target_inode,'clone_target_charon_inode':clone_target_inode,'target_file_count':len(source_regular),'target_shared_regular_inode_count':len(shared),'target_content_mode_equal':True,'tracked_source_sha256_before':source_hashes,'tracked_candidate_sha256_after_overlay':clone_hashes,'meminfo_before':mem,'candidate_memory_max_bytes':candidate_max,'required_available_after_cap_bytes':reserve,'safe_working_limit_bytes':safe,'other_aspis_active_units':other_units,'other_aspis_reserved_max_bytes':other_max,'heavy_processes_before':heavy,'effective_worker_cgroup_before':worker_cgroup,'wall_seconds':time.monotonic()-started,'cgroup_samples':samples,'pins':PIN}
(AUDIT/'clone-audit.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
(AUDIT/'tracked-tree.json').write_text(json.dumps(tracked,indent=2,sort_keys=True)+'\n')
(AUDIT/'parent-tracked-sha256.json').write_text(json.dumps(source_hashes,indent=2,sort_keys=True)+'\n')
(CANDIDATE_ROOT:=DST/'candidate-audit/clone').mkdir(parents=True,exist_ok=True)
(CANDIDATE_ROOT/'target-cache-sha256.json').write_text(json.dumps(source_cache,indent=2,sort_keys=True)+'\n')
(CANDIDATE_ROOT/'target-cache-clone-sha256.json').write_text(json.dumps(copied_cache,indent=2,sort_keys=True)+'\n')
stop.set(); th.join(); (AUDIT/'cgroup-samples.json').write_text(json.dumps(samples,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('tracked_source_sha256_before','tracked_candidate_sha256_after_overlay','cgroup_samples')},indent=2))
