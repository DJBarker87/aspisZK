#!/usr/bin/env python3
import json,subprocess,hashlib
from pathlib import Path
E=Path(__file__).resolve().parent.parent
R='/home/dombarker/project-offloads/codex-cx-prover-commit13-20261021'
host='dombarker@100.108.41.90'
subprocess.run(['scp','-r',host+':'+R+'/receipts',str(E)],check=True)
subprocess.run(['scp',host+':'+R+'/*-inputs.json',str(E)],check=True)
code='''import json,hashlib
from pathlib import Path
s=Path(%r)/'src'
files=[p for p in s.rglob('*') if p.is_file() and (p.suffix=='.rs' or p.name in ['Cargo.toml','Cargo.lock'])]
print(json.dumps({str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},indent=2))
'''%R
(E/'final-source-inputs.json').write_text(subprocess.check_output(['ssh',host,'python3 -'],input=code,text=True))
code='''import json
from pathlib import Path
s=Path(%r)/'kani-contract-target'
rows=[]
for p in s.rglob('*.kani-metadata.json'):
 x=json.loads(p.read_text())
 for h in x.get('proof_harnesses',[]):
  if any(t in h.get('pretty_name','') for t in ['safety13','scalar13','seeds13','query13','outer13']):rows.append(dict(metadata=str(p),harness=h))
print(json.dumps(rows,indent=2))
'''%R
(E/'scalar-harness-metadata.json').write_text(subprocess.check_output(['ssh',host,'python3 -'],input=code,text=True))
