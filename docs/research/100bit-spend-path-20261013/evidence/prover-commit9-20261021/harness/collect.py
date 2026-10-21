#!/usr/bin/env python3
"""Collect only textual evidence; executable artifacts remain on the host."""
import subprocess,json,hashlib
from pathlib import Path
H='/home/dombarker/project-offloads/codex-cx-prover-commit9-20261021'
E=Path(__file__).resolve().parent.parent
code='''import json
from pathlib import Path
H=Path(%r)
paths=list(H.glob('*-inputs.json'))+list(H.glob('*-llbc-*.json'))+list((H/'receipts').rglob('*'))
print(json.dumps({str(p.relative_to(H)):p.read_text() for p in paths if p.is_file()}))
'''%H
items=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True))
for name,body in items.items():
 p=E/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(body)
rows=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 r=json.loads(p.read_text());name=p.parent.name
 if (E/(name+'-inputs.json')).exists():r['inputs']=json.loads((E/(name+'-inputs.json')).read_text())
 r['receipt']=str(p.relative_to(E));r['name']=name
 rows.append(r)
(E/'receipt-index.json').write_text(json.dumps(rows,indent=2)+'\n')
