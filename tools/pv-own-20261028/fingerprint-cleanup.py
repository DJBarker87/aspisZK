"""Final read-only closure check, then remove only this job's rebuildable caches."""
from pathlib import Path
import json,hashlib,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-own-20261028')
inputs=json.loads((D/'final-inputs.json').read_text());external=inputs['external']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
objects={}
for m,r in inputs['projects'].items():
 source=D/'lean-sources'/(m+'.lean');obj=D/'lean-objects'/(m+'.olean')
 assert sha(source)==r['source_sha256'],m
 objects[m]=dict(source_path=str(source),source_sha256=sha(source),source_blob=r['source_blob'],source_revision=r['source_revision'],object_sha256=sha(obj),object_bytes=obj.stat().st_size,imports=r['imports'])
for m,r in inputs['projects'].items():
 for dep,h in r['dependency_objects'].items():assert objects[dep.replace('.','/')]['object_sha256']==h,(m,dep)
for r in external:
 p=D/'lean-objects'/(r['module']+'.olean');assert sha(p)==r['object_sha256'],r['module']
result=dict(projects=objects,project_count=len(objects),external_count=len(external),external_ok=True,direct_and_transitive_project_edges_ok=True,environment=json.loads((D/'env-J.json').read_text()),scope='PV_OWN shared model closure, not native privacy endpoint',reused_project_objects=0)
(D/'final-fingerprint.json').write_text(json.dumps(result,indent=2))
# Exact own output roots only. Symlinks are removed without following targets.
root=D/'lean-objects';paths=list(root.rglob('*'));regular=links=bytes_removed=0
for p in paths:
 if p.is_symlink():p.unlink();links+=1
 elif p.is_file():
  assert p.name.endswith(('.olean','.olean.server','.olean.private','.ir','.ilean')),str(p)
  bytes_removed+=p.stat().st_size;p.unlink();regular+=1
for p in sorted(paths,key=lambda p:len(p.parts),reverse=True):
 if p.is_dir():p.rmdir()
root.rmdir()
target=D/'target';target_bytes=sum(p.stat().st_size for p in target.rglob('*')if p.is_file()and not p.is_symlink())
exe=target/'release/own_probe';exe_hash=sha(exe);shutil.rmtree(target)
cleanup=dict(private_object_files_removed=regular,private_object_bytes_removed=bytes_removed,private_links_removed_without_following=links,cargo_target_bytes_removed=target_bytes,native_executable_sha256=exe_hash,keys_created=0,keys_removed=0,other_job_directories_modified=0,retained=['sources','MIR','all raw receipts','final fingerprints'])
(D/'cleanup.json').write_text(json.dumps(cleanup,indent=2));print(json.dumps(dict(project_count=len(objects),external_count=len(external),all_checks=True,cleanup=cleanup)))
