from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,hashlib,shutil,os
b=Path('/home/dombarker/project-offloads/codex-cx-q-leftovers-20261106');cache=b.parent/'codex-cx-slice-d-field3-cache-20261104'/'NHN_exports_20261106';cache.mkdir(exist_ok=True)
# Terminal-attempt receipts are required before export/cleanup.
assert json.loads((b/'NHN_L011/receipt.json').read_text())['exit_status']==0
files=[]
for folder in ['NHN_objects','NHN_generated']:
 for p in (b/folder).iterdir():
  if p.is_file():
   q=cache/('objects'if folder=='NHN_objects'else'sources')/p.name;q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q)
   files.append(dict(source=str(p),path=str(q),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
# Only own rebuildable scratch is removed. Assigned cache and all shared inputs remain.
removed=[]
for n in ['NHN_target','NHN_native','NHN_tmp']:
 p=b/n
 if p.exists():
  assert not p.is_symlink();shutil.rmtree(p);removed.append(str(p))
print(json.dumps(dict(status='PASS',workspace_retained=str(b),export=str(cache),files=files,export_bytes=sum(x['bytes']for x in files),removed_own_scratch=removed,seed_retained='/home/dombarker/project-offloads/codex-cx-slice-d-field3-cache-20261104/NHN_seed_20261106',inherited_path='NHN_L011.json env.LEAN_PATH; prepend export/objects for reuse')))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
(E/'NHN_EXPORT.json').write_text(r.stdout);print('Export bytes',json.loads(r.stdout)['export_bytes'])
