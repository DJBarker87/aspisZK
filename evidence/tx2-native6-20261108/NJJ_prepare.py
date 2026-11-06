from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-tx2-native6-20261108'
# Read-only capture; admission for staging was obtained before scratch mutation.
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=f'''from pathlib import Path
import json
b=Path({B!r});print(json.dumps(dict(pins=json.loads((b/'NJJ_SOURCE_PINS.json').read_text()),lib=(b/'NJJ_src/crates/aspis-r1-cost-probe/src/lib.rs').read_text())))
''',capture_output=True,text=True);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);lib=x['lib']+'\n#[cfg(kani)]\n#[path = "NJJ_lib.rs"]\nmod NJJ_lib;\n'
files={'crates/aspis-r1-cost-probe/src/lib.rs':lib,'crates/aspis-r1-cost-probe/src/NJJ_lib.rs':(E/'NJJ_lib.rs.txt').read_text()}
pins=x['pins'];pins.update({p:hashlib.sha256(t.encode()).hexdigest() for p,t in files.items()})
(E/'NJJ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n');(E/'NJJ_NATIVE_INPUTS.json').write_text(json.dumps(files,indent=2)+'\n')
(E/'NJJ_FROZEN_LIB.json').write_text(json.dumps(dict(path='crates/aspis-r1-cost-probe/src/lib.rs',sha256=hashlib.sha256(x['lib'].encode()).hexdigest(),append_only_cfg_kani=True),indent=2)+'\n')
