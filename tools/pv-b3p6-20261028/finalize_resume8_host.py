"""Finalize accounting; verify dependent hashes and retain the unfinished V244 cache."""
from pathlib import Path
import json,hashlib
from run import H
p=H/'TALLY-resume8.json';t=json.loads(p.read_text());assert t['lean_attempts']==100
assert sorted(t['used_ids'])==list(range(62300,62400))
assert t['audit_ids_used']==[62397,62398,62399]
for a in t['audit_ids_used']:assert json.loads((H/f'lean-{a}/receipt/receipt.json').read_text())['exit_status']==0
t.update(native_scopes=0,kani_runs=0,budget_exhausted=True,next_unused_id=None,ordinary_range_exhausted=True)
p.write_text(json.dumps(t,indent=2)+'\n')
latest={r['module']:r for r in t['receipts']if r['exit']==0};bad=[];checks=0
for module,row in latest.items():
 r=json.loads(Path(row['receipt']).read_text())
 for name,dep in r['dependency_objects'].items():
  q=Path(dep['path']);actual=hashlib.sha256(q.read_bytes()).hexdigest()if q.exists()else None;checks+=1
  if actual!=dep['sha256']:bad.append(dict(module=module,dependency=name,expected=dep['sha256'],actual=actual,path=str(q)))
 src=H/'lean'/(module.replace('.','/')+'.lean')
 assert hashlib.sha256(src.read_bytes()).hexdigest()==r['source_sha256'],module
O=H/'archive-resume8';O.mkdir(exist_ok=True)
(O/'final-dependency-check.json').write_text(json.dumps(dict(checked=checks,accepted_modules=len(latest),mismatches=bad),indent=2)+'\n');assert not bad,bad
rows=[]
for q in sorted((H/'lean-objects').rglob('*')):
 if q.is_file():rows.append(dict(path=str(q.relative_to(H)),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
(O/'private-object-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
(O/'cache-retention.json').write_text(json.dumps(dict(status='retained pinned private workspace for unfinished V244',directory=str(H),objects=len(rows),bytes=sum(r['bytes']for r in rows),reason='AGENTS resource rule6; incomplete exhaustive source binding, D188 matrix and std/slice obligations. Reuse pinned cache next round; no shared sources/objects changed.',wallet_keys_created_or_deleted=False),indent=2)+'\n')
print(json.dumps(dict(attempts=100,audits='all pass',private_objects=len(rows),dependency_checks=checks,mismatches=bad)))
