"""Create only NEM scratch and copy accepted objects; no infrastructure changes."""
from pathlib import Path
import subprocess,json,hashlib,time,base64
E=Path(__file__).resolve().parent;P=E.parent/'slice-s-compose4-20261101'
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-slice-s-compose5-20261029'
pins=json.loads((P/'NEL_RUST_SOURCE_PINS.json').read_text())
files={n:base64.b64encode(subprocess.check_output(['git','show',pins['revision']+':'+n])).decode() for n in pins['files']}
code='''from pathlib import Path
import json,shutil,hashlib,base64
root=Path('/home/dombarker/project-offloads');b=root/'codex-cx-slice-s-compose5-20261029';b.mkdir(exist_ok=True)
old=root/'codex-cx-slice-s-compose4-20261029';out=[]
p=old/'S2W_run_host.py';q=b/p.name
if not q.exists():shutil.copy2(p,q)
assert p.read_bytes()==q.read_bytes()
out.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
cache=root/'codex-cx-slice-s-compose5-cache-20261029';cache.mkdir(exist_ok=True)
seeds=['codex-cx-slice-s-compose4-cache-20261029/NEL_final_objects_20261102','codex-cx-slice-s-compose3-cache-20261029/NEJ_final_objects_20261101','codex-cx-slice-s-compose4-cache-20261029','codex-cx-slice-s-compose3-cache-20261029','codex-cx-leaf-cache-20261027','codex-cx-cpilot-cache-20261028','codex-cx-front2-cache-20261028','codex-cx-front4-cache-20261028','codex-cx-slice-s-compose2-cache-20261029','codex-cx-slice-s-compose-cache-20261029']
for seed in seeds:
 r=root/seed
 if not r.exists():continue
 for p in r.rglob('*'):
  if not p.is_file() or p.suffix not in ['.lean','.olean','.ilean']:continue
  q=cache/p.relative_to(r)
  if q.exists():continue
  q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  assert hashlib.sha256(p.read_bytes()).digest()==hashlib.sha256(q.read_bytes()).digest()
  out.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
files=json.loads(INPUT_FILES)
s=b/'NEM_src';s.mkdir(exist_ok=True)
for n,v in files.items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True)
 v=base64.b64decode(v)
 if p.exists():assert p.read_bytes()==v
 else:p.write_bytes(v)
print(json.dumps(dict(imports=out,frozen_files=len(files))))
'''.replace('INPUT_FILES',repr(json.dumps(files)))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input=code,text=True,capture_output=True)
(E/'NEM_BOOTSTRAP.log').write_text(r.stderr)
assert r.returncode==0,r.stderr
(E/'NEM_HOST_PINS.json').write_text(r.stdout)
# Reuse predecessor gates, with OWN path/prefix and exact job attempt limits.
for name in ['run.py','kani_run.py','kani_gate.py','prepare_window.py']:
 t=(P/('NEL_'+name)).read_text().replace('NEL_','NEM_').replace('codex-cx-slice-s-compose4-20261029','codex-cx-slice-s-compose5-20261029').replace('codex-cx-slice-s-compose4-cache-20261029','codex-cx-slice-s-compose5-cache-20261029')
 if name=='run.py':
  t=t.replace('<=120','<=80').replace('<120','<80').replace("b.parent/'codex-cx-slice-s-compose5-cache-20261029/NEM_final_objects_20261102',",'').replace(':/home/dombarker/project-offloads/codex-cx-slice-s-compose5-cache-20261029/NEM_final_objects_20261102','')
 if name=='kani_run.py':t=t.replace('<60','<110').replace('<=60','<=110')
 (E/('NEM_'+name)).write_text(t)
for name in ['contract_controls.patch','RUST_SOURCE_PINS.json']:(E/('NEM_'+name)).write_bytes((P/('NEL_'+name)).read_bytes())
(E/'NEM_IMPORT_PROVENANCE.json').write_text(json.dumps(dict(predecessor='evidence/slice-s-compose4-20261101',unchanged_modules='NEL, NEJ, NEE, NED copied in host cache; no reproof',runners='predecessor own runners; prefix/path and budget only',actual_branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip(),requested_branch='codex/cx-slice-s-compose5-20261029',frozen_revision=pins['revision']),indent=1)+'\n')
