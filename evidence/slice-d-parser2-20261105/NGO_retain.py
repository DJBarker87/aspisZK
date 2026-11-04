"""Retain the admitted canonical exports; clean only this job's rebuildable outputs."""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-slice-d-parser2-20261105';C='/home/dombarker/project-offloads/codex-cx-slice-d-parser2-cache-20261104'
mods=json.loads((E/'NGO_AUDIT_ROOTS.json').read_text())['modules']+['NGO_COMBINED_IMPORT','NGO_ProofDriver','NGO_Driver']
code=f'''from pathlib import Path
import hashlib,json,shutil,subprocess,sys,time
b=Path({B!r});c=Path({C!r});p=b/'NGO_RETAIN-admission.json'
with (b/'NGO_RETAIN-barrier.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
if r.returncode!=0 or not p.exists() or json.loads(p.read_text()).get('allowed') is not True:print(p.read_text()if p.exists()else'MISSING');sys.exit(78)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb')as f:
  while data:=f.read(1048576):h.update(data)
 return h.hexdigest()
export=c/'NGO_exports_20261105';export.mkdir(exist_ok=True);files=[]
for m in {mods!r}:
 stem=m.replace('.','/')
 for ext in ['.olean','.olean.private','.olean.server','.ir']:
  src=b/'NGO_objects'/(stem+ext)
  if not src.is_file():continue
  dst=export/(stem+ext);dst.parent.mkdir(parents=True,exist_ok=True)
  if dst.exists():assert sha(dst)==sha(src)
  else:shutil.copy2(src,dst)
  assert sha(src)==sha(dst)
  files.append(dict(module=m,path=str(dst),sha256=sha(dst),bytes=dst.stat().st_size))
for name in ['NGO_ProofDriver','NGO_Driver']:
 src=b/'NGO_native'/name;dst=export/'native'/name;dst.parent.mkdir(exist_ok=True)
 if dst.exists():assert sha(dst)==sha(src)
 else:shutil.copy2(src,dst)
 assert sha(src)==sha(dst);files.append(dict(path=str(dst),sha256=sha(dst),bytes=dst.stat().st_size))
result=dict(cache_retained=str(c),export=str(export),files=files,export_bytes=sum(x['bytes']for x in files),admission=json.loads(p.read_text()))
(b/'NGO_CACHE_EXPORTS.json').write_text(json.dumps(result,indent=1))
# Record observation-time tool pins, not historical attestations.
tools={{}}
for name in ['/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lake','/home/dombarker/.cargo/bin/cargo-kani']:
 q=Path(name)
 if q.is_file():tools[name]=dict(sha256=sha(q),bytes=q.stat().st_size)
result['observation_time_tool_pins']=tools
removed=[]
for name in ['NGO_target','NGO_ref_target','NGO_tmp','NGO_objects','NGO_native']:
 q=b/name
 if q.exists():
  sizes=sum(p.stat().st_size for p in q.rglob('*')if p.is_file());removed.append(dict(path=str(q),bytes=sizes));shutil.rmtree(q)
result['removed_own_rebuildable_outputs']=removed;result['cache_deleted']=False;result['workspace_source_inputs_retained']=True;result['disk_free_bytes']=shutil.disk_usage(b).free
print(json.dumps(result))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
(E/'NGO_RETAIN-client.log').write_text(r.stderr);assert r.returncode==0,r.stdout+r.stderr
(E/'NGO_CACHE_EXPORTS.json').write_text(r.stdout)
d=json.loads(r.stdout);print(json.dumps(dict(export_files=len(d['files']),export_bytes=d['export_bytes'],own_rebuildable_bytes_removed=sum(x['bytes']for x in d['removed_own_rebuildable_outputs']),host_free_bytes=d['disk_free_bytes'],cache_deleted=d['cache_deleted'])))
