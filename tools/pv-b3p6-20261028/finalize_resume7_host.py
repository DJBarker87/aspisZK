"""Finalize accounting and retain pinned private cache for unfinished V244."""
from pathlib import Path
import json,hashlib
from run import H
p=H/'TALLY-resume7.json';t=json.loads(p.read_text())
assert t['lean_attempts']==100 and len(t['used_ids'])==100
for a in [61597,61598,61599]:
 r=json.loads((H/f'lean-{a}/receipt/receipt.json').read_text());assert r['exit_status']==0
assert len(list(H.glob('llvm227-resume7-*/receipt/receipt.json')))==3
t.update(native_scopes=3,kani_runs=0,kani=0,budget_exhausted=True,next_unused_id=None,ordinary_range_exhausted=True)
p.write_text(json.dumps(t,indent=2)+'\n')
rows=[]
for p in sorted((H/'lean-objects').rglob('*')):
 if p.is_file():rows.append(dict(path=str(p.relative_to(H)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
O=H/'archive-resume7';O.mkdir(exist_ok=True)
(O/'private-object-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
(O/'cache-retention.json').write_text(json.dumps(dict(status='retained pinned private workspace for unfinished V244',directory=str(H),objects=len(rows),bytes=sum(r['bytes']for r in rows),reason='AGENTS resource rule6: reuse pinned workspace/cache between focused dependent targets. This budget round ended; V244 remains unfinished. No shared objects changed and no compiled objects committed.',wallet_keys_created_or_deleted=False),indent=2)+'\n')
print(json.dumps(dict(attempts=100,audits='all passed',private_objects=len(rows))))
