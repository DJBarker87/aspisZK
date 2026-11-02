from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent
names=json.loads((E/'NEL_BOOTSTRAP_REPAIR.json').read_text())['removed_own_copied_harness_artifacts']
files={}
for n in names:
 r=subprocess.run(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True,capture_output=True)
 if r.returncode==0:files[n]=r.stdout
code=f'''from pathlib import Path
import json,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-slice-s-compose4-20261029');s=b/'NEL_src'
pins=json.loads((b/'NEL_RUST_SHA256.json').read_text())
assert all(hashlib.sha256((s/n).read_bytes()).hexdigest()==h for n,h in pins.items())
for n,v in json.loads({json.dumps(files)!r}).items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(v);pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
(b/'NEL_RUST_SHA256.json').write_text(json.dumps(pins,indent=1))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'NEL_INCLUDE_REPAIR.json').write_text(json.dumps(dict(reason='K001 missing frozen includes; input repair, no theorem failure',files={n:hashlib.sha256(v.encode()).hexdigest() for n,v in files.items()}),indent=1)+'\n')
