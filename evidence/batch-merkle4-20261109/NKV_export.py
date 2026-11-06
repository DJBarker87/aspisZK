from pathlib import Path
import subprocess,json
p=Path(__file__).resolve().parent
mods=sorted(json.loads((p/'NKV_PROOF_SET.json').read_text()))+['NKV_COMBINED_IMPORT']
code='''from pathlib import Path
import json,hashlib,shutil,subprocess
b=Path('/home/dombarker/project-offloads/codex-cx-batch-merkle4-20261109')
e=b/'NKV_exports_final_20261109';e.mkdir(exist_ok=True)
modules='''+repr(mods)+'''
manifest={}
for m in modules:
 stem=b/'NKV_objects'/m.replace('.','/')
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  f=Path(str(stem)+suffix)
  if not f.exists():
   assert suffix!='.olean',str(f)
   continue
  d=e/(m.replace('.','/')+suffix);d.parent.mkdir(parents=True,exist_ok=True)
  if d.exists():assert hashlib.sha256(d.read_bytes()).digest()==hashlib.sha256(f.read_bytes()).digest()
  else:shutil.copy2(f,d)
  manifest[str(d.relative_to(e))]={'sha256':hashlib.sha256(d.read_bytes()).hexdigest(),'bytes':d.stat().st_size,'source':str(f)}
rc=json.loads((b/'NKV_L113/receipt.json').read_text())
pinned=json.loads((b/'NKV_L109/receipt.json').read_text())
assert rc['env']['LEAN_PATH']==pinned['env']['LEAN_PATH']
aeneas={k:v for k,v in pinned['deps_fingerprint']['selected_objects'].items() if '/Aeneas' in k}
assert aeneas
for key,value in aeneas.items():assert hashlib.sha256(Path(value['path']).read_bytes()).hexdigest()==value['sha256'],key
continuity={'pin_attempt':'NKV_L109','binary_audit_attempt':'NKV_L113','identical_LEAN_PATH':True,'all_aeneas_object_hashes_unchanged':True,'pins':aeneas}
(b/'NKV_AUDIT_LIBRARY_CONTINUITY.json').write_text(json.dumps(continuity,indent=2)+chr(10))
out={'export':str(e),'files':manifest,'bytes':sum(x['bytes'] for x in manifest.values()),'module_count':len(modules),'source_revision':rc['source_revision'],'source_proof_set_sha256':hashlib.sha256((b/'NKV_PROOF_SET.json').read_bytes()).hexdigest(),'audit_attempt':'NKV_L113','aeneas_library_pins':aeneas,'aeneas_continuity':continuity,'retained_cargo_target':str(b/'NKV_target'),'free_bytes':shutil.disk_usage(b).free,'own_workspace_bytes':int(subprocess.check_output(['du','-sb',str(b)],text=True).split()[0])}
assert out['own_workspace_bytes']<30000000000
(b/'NKV_EXPORT_MANIFEST.json').write_text(json.dumps(out,indent=2)+chr(10))
print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
x=json.loads(r.stdout)
(p/'NKV_EXPORT_MANIFEST.json').write_text(json.dumps(x,indent=2)+'\n')
print('retained export',x['module_count'],'modules,',x['bytes'],'bytes; own host writes',x['own_workspace_bytes'])
