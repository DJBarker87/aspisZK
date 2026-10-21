#!/usr/bin/env python3
"""Keep hashes and sizes of proof inputs on host, never commit binaries."""
from pathlib import Path
import hashlib,json,re
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit14-20261021')
rows=[]
for name in ['kani-contract-target','kani-lane1-target','kani-lane2-target']:
 for p in (H/name).rglob('*material146word_*.out'):
  match=re.search(r'material146word_(\d+)\.out$',p.name)
  if match:
   rows.append(dict(word=int(match[1]),path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
(H/'kani-artifacts.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Hashed',len(rows),'host proof inputs; no binary copied')
