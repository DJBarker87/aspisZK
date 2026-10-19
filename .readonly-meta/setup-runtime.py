from pathlib import Path
import hashlib,json,os,shutil,subprocess,tarfile,time
w=Path('/home/dombarker/project-offloads/aspis-r1-readonly-meta-20261016/runtime-check');origin=Path('/home/dombarker/project-offloads/aspis-r1-r18-prefix-20261016/cargo-target')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
cachepins={}
for p in [origin/'release/r18_replay',origin/'release/r18_replay.d']:
 if p.is_file():cachepins[str(p)]={'sha256':sha(p),'bytes':p.stat().st_size,'mtime_ns':p.stat().st_mtime_ns}
assert not (w/'cargo-target').exists()
subprocess.run(['cp','-a','--reflink=auto',str(origin),str(w/'cargo-target')],check=True)
arc=w/'runtime-source-9e6384f29.tar'
with tarfile.open(arc) as t:t.extractall(w/'source',filter='data')
# Git archive epoch mtimes must not make changed sources older than a warm cache.
for p in (w/'source').rglob('*'):
 if p.is_file():os.utime(p,None)
files={'source/'+str(p.relative_to(w/'source')):sha(p) for p in sorted((w/'source').rglob('*')) if p.is_file()}
(w/'inputs.json').write_text(json.dumps({'source_revision':'9e6384f29ce7f482d7477f9adc51d396811bbd3e','source_archive_sha256':sha(arc),'files':files},indent=2)+'\n')
(w/'setup.json').write_text(json.dumps({'cache_origin':str(origin),'private_copy':True,'cache_binary_and_depinfo':cachepins,'source_mtimes_refreshed_after_cache_copy':True,'source_files':len(files),'refreshed_unix_time':time.time(),'scope':'Native optimized cargo check only; no SBF or runtime execution; cached executable is not a newly built candidate'},indent=2)+'\n')
print(json.dumps({'source_files':len(files),'source_archive_sha256':sha(arc),'inputs_sha256':sha(w/'inputs.json')}))
