#!/usr/bin/env python3
"""Collect compact host receipts; no binaries, keys, or compiled Lean objects."""
import subprocess,json,hashlib
from pathlib import Path
E=Path(__file__).resolve().parent.parent
H='dombarker@100.108.41.90';R='/home/dombarker/project-offloads/codex-cx-prover-commit7-20261021'
names=json.loads(subprocess.check_output(['ssh',H,'python3 -c '+"'import json; from pathlib import Path; print(json.dumps([p.name for p in Path(\""+R+'/receipts'+"\").iterdir()]))'"],text=True))
for name in names:
 (E/'receipts'/name).mkdir(parents=True,exist_ok=True)
 subprocess.run(['scp',H+':'+R+'/receipts/'+name+'/*',str(E/'receipts'/name)],check=True,stdout=subprocess.DEVNULL)
subprocess.run(['scp',H+':'+R+'/*-inputs.json',str(E)],check=True,stdout=subprocess.DEVNULL)
for name in ['caller-llbc-v3.json','frozen-elf-final-check.json']:
 subprocess.run(['scp',H+':'+R+'/'+name,str(E)],check=True,stdout=subprocess.DEVNULL)
for name in ['default','devnet','pool']:
 subprocess.run(['scp',H+':'+R+'/sbf-'+name+'-reservation.json',str(E)],check=True,stdout=subprocess.DEVNULL)
rows=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 d=json.loads(p.read_text());rows.append(dict(target=p.parent.name,**d))
(E/'receipt-index.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(dict(receipts=len(rows))))
