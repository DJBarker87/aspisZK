#!/usr/bin/env python3
"""Upload only lane-owned cfg(kani) overlays to the existing scratch tree."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-slice-q-compose-20261029'
files=json.loads((E/'NEB_ADDITIVE_FILES.json').read_text())
code=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});s=b/'NEB_src';files=json.loads({json.dumps(files)!r})
for n,v in files.items():
 p=s/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(v)
pins=json.loads((b/'NEB_SOURCE_PINS.json').read_text())
for n in files:pins[n]=hashlib.sha256((s/n).read_bytes()).hexdigest()
(b/'NEB_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\\n')
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stdout+r.stderr
print('additive overlay uploaded; no prover launched')
