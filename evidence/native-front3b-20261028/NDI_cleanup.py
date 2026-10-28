from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,hashlib,shutil,os
b=Path('/home/dombarker/project-offloads/codex-cx-native-front3b-20261028');cache=b.parent/'codex-cx-front3-cache-20261028';assert b.is_dir() and cache.is_dir()
# No prover is active for this lane; do not operate on other lanes or shared /tmp.
proc=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:c=(p/'cmdline').read_bytes().replace(b'\\0',b' ').decode(errors='replace')
 except (FileNotFoundError,PermissionError,ProcessLookupError):continue
 if 'S2W_run_host.py NDI_' in c:proc.append(dict(pid=p.name,command=c))
assert not proc,proc
obj=b/'NDI_objects';dest=cache/'NDI_objects';assert not obj.is_symlink() and not dest.exists()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
objects={str(p.relative_to(obj)):sha(p) for p in obj.rglob('*') if p.is_file()}
obj.rename(dest);obj.symlink_to(dest,target_is_directory=True)
assert objects=={str(p.relative_to(dest)):sha(p) for p in dest.rglob('*') if p.is_file()}
removed={}
for name in ['NDI_target','NDI_ref_target','NDI_tmp']:
 p=b/name;assert p.parent==b and not p.is_symlink()
 if p.exists():
  removed[str(p)]=sum(f.stat().st_size for f in p.rglob('*') if f.is_file())
  shutil.rmtree(p)
print(json.dumps(dict(active_lane_scopes=proc,removed_rebuildable_bytes=removed,retained_cache=str(cache),retained_objects=str(dest),object_count=len(objects),object_hashes=objects,object_hashes_unchanged=True,source_and_receipts_retained=True,shared_files_deleted=False,shared_tmp_files_deleted=False,solver_tmp_policy='Own NDI_tmp and target trees removed; no attribution-based license to delete another lane shared /tmp files; no owned shared /tmp solver files identified',keys_created_or_deleted=False)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NDI_CLEANUP.json').write_text(json.dumps(x,indent=2)+'\n');print('retained objects',x['object_count'],'reclaimed bytes',sum(x['removed_rebuildable_bytes'].values()))
