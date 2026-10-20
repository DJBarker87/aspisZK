#!/usr/bin/env python3
from pathlib import Path
import subprocess,json,hashlib
ROOT=Path(__file__).resolve().parents[2]
E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/r4-transport2-20261021'
H='dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-cx-r4-transport2-20261021/'
subprocess.run(['rsync','-a',H+'receipts/',str(E/'host-receipts')+'/'],check=True)
subprocess.run(['rsync','-a','--include=*-inputs.json','--include=*-reservation.json','--exclude=*',H,str(E/'host-inputs')+'/'],check=True)
rows=[]
for p in sorted((E/'host-receipts').glob('*/receipt.json')):
 rec=json.loads(p.read_text());rec['attempt']=p.parent.name
 inp=E/'host-inputs'/(p.parent.name+'-inputs.json')
 rec['inputs']=json.loads(inp.read_text()) if inp.exists() else None
 rows.append(rec)
(E/'host-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
