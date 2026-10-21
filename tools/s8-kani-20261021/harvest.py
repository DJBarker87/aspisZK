#!/usr/bin/env python3
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s8-kani-20261021'
H='dombarker@100.108.41.90';D='/home/dombarker/project-offloads/codex-cx-s8-kani-20261021'
subprocess.run(['rsync','-a',H+':'+D+'/receipts/',str(E/'receipts')+'/'],check=True)
subprocess.run(['rsync','-a','--include=reservation-*.json','--exclude=*',H+':'+D+'/',str(E)+'/'],check=True)
for phase in ['extraction','extraction-concrete','extraction-leaves','extraction-complete']:
 out=E/phase;out.mkdir(exist_ok=True)
 # Do not adopt template axioms or binary LLBC. Pin all artifacts and keep emitted definitions.
 script='''from pathlib import Path
import hashlib,json
p=Path(%r);print(json.dumps({str(x.relative_to(p)):{'sha256':hashlib.sha256(x.read_bytes()).hexdigest(),'size_bytes':x.stat().st_size} for x in p.rglob('*') if x.is_file()},indent=2))'''%(D+'/'+phase)
 pins=subprocess.check_output(['ssh',H,'python3 - <<\'PYREMOTE\'\n'+script+'\nPYREMOTE'],text=True)
 (out/'artifact-pins.json').write_text(pins+'\n')
 subprocess.run(['rsync','-a','--exclude=*.llbc','--exclude=*Template*',H+':'+D+'/'+phase+'/',str(out)+'/'],check=True)
print('Harvested source/resource receipts and generated definitions; no binary or template axioms')
