"""Read-only hash verification of all retained native compiler input snapshots."""
from pathlib import Path
import json,hashlib
B=Path('/home/dombarker/project-offloads/codex-cx-leaf-p6-3-20261027');errors=[];count=0
for p in sorted(B.glob('LPc_K*/receipt.json')):
 r=json.loads(p.read_text())
 for f,h in r['source_hashes'].items():
  q=p.parent/'sources'/f;count+=1
  if hashlib.sha256(q.read_bytes()).hexdigest()!=h:errors.append(r['attempt']+' '+f)
print(json.dumps({'runs':20,'source_inputs_checked':count,'errors':errors,'scope':'exact per-run native input snapshots; no prover invocation'},indent=2))
