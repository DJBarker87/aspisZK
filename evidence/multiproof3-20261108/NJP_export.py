from pathlib import Path
import subprocess,json,time
E=Path(__file__).resolve().parent
inventory=json.loads((E/'NJP_FINAL_PROOF_INVENTORY.json').read_text())
mods=list(inventory['modules'])+['NJP_COMBINED_IMPORT','NJP_Driver','NJP_ProofDriver']
code='''from pathlib import Path
import hashlib,json,shutil,time
b=Path('/home/dombarker/project-offloads/codex-cx-multiproof3-20261108')
cache=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJP_20261108')
out=cache/'NJP_exports_20261108';out.mkdir(exist_ok=True)
mods=MODS

def pin(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
 return {'sha256':h.hexdigest(),'bytes':p.stat().st_size}
exports={}
for m in mods:
 source=b/'NJP_objects'/(m+'.olean')
 assert source.is_file(),m
 for p in (b/'NJP_objects').glob(m+'.*'):
  if p.is_file():
   dest=out/p.name
   if dest.exists():assert pin(dest)==pin(p),str(dest)
   else:shutil.copy2(p,dest)
   assert pin(dest)==pin(p)
   exports[str(dest)]=pin(dest)
artifacts={}
for directory in [b/'NJP_target',b/'NJP_objects']:
 if directory.exists():
  for p in directory.rglob('*'):
   if p.is_file():artifacts[str(p)]=pin(p)
for p in (b/'NJP_native').iterdir():
 if p.is_file():artifacts[str(p)]=pin(p)
record={'export':str(out),'files':exports,'bytes':sum(x['bytes'] for x in exports.values()),'source_workspace':str(b),'cache_retained':True,'artifacts_before_cleanup':artifacts,'free_before':shutil.disk_usage(b).free}
(b/'NJP_EXPORT.json').write_text(json.dumps(record,indent=2)+'\\n')
# Only task-owned, rebuildable Rust target/Lean objects/native executables.
# No task key was created and no wallet/account key path is touched.
for directory in [b/'NJP_target',b/'NJP_objects']:
 if directory.exists():shutil.rmtree(directory)
for name in ['NJP_Driver','NJP_ProofDriver']:
 (b/'NJP_native'/name).unlink()
record['free_after']=shutil.disk_usage(b).free
record['cleanup']=['NJP_target','NJP_objects','NJP_native/NJP_Driver','NJP_native/NJP_ProofDriver']
record['deleted_keys']=False
(b/'NJP_EXPORT.json').write_text(json.dumps(record,indent=2)+'\\n')
print(json.dumps(record))
'''.replace('MODS',repr(mods))
# Once submitted, never resubmit: recover read-only from NJP_EXPORT.json.
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
if r.returncode:
 raise RuntimeError('Submitted export/cleanup: recover read-only, never resubmit: '+r.stderr)
record=json.loads(r.stdout);(E/'NJP_EXPORT.json').write_text(json.dumps(record,indent=2)+'\n')
print('Retained export: '+str(len(record['files']))+' files, '+str(record['bytes'])+' bytes; owned rebuildable artifacts removed; cache and keys retained')
