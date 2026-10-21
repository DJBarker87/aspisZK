#!/usr/bin/env python3
"""Keep hashes and sizes of proof inputs on host, never commit binaries."""
from pathlib import Path
import hashlib,json,re
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit15-20261021')
rows=[]
for p in (H/'kani-contract-target').rglob('*material1514candidate_step.out'):
 rows.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
assert len(rows)==1,rows
(H/'kani-artifacts.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Hashed',len(rows),'host proof inputs; no binary copied')
