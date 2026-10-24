"""Summarize retained receipts, keeping all commands/hashes and failed attempts."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parent;R=D.parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/factory-iteration'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[];maximum=0
for O in sorted((E/'packet').iterdir()):
 r=json.loads((O/'receipt.json').read_text())
 row={k:r[k] for k in ['target','command','source_revision','source_sha256','dependency_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}
 row.update(id=O.name,receipt=str((O/'receipt.json').relative_to(E)),receipt_sha256=sha(O/'receipt.json'),preflight_sha256=sha(O/'preflight.json'),resources=json.loads((O/'resources.json').read_text()),resources_sha256=sha(O/'resources.json'))
 for phase in ['before','barrier']:
  p=O/f'admission-{phase}.json';a=json.loads(p.read_text());assert a['allowed'] and a['projected_reserved_bytes']<55*2**30
  row[f'admission_{phase}_sha256']=sha(p);maximum=max(maximum,a['projected_reserved_bytes'])
 out=(O/'stdout.log').read_text();m=re.search(r'\*\* \d+ of \d+ failed[^\n]*',out)
 if m:row['verification_result']=m[0]
 if r['exit_status']==124:
  row['peak_rss_limitation']='GNU time undercounts killed grandchildren. Exact aggregate process-tree RSS peak unavailable. resources gives sampled aggregate RSS and exact cgroup memory peak, neither is exact process-tree RSS.'
 rows.append(row)
ledger=dict(schema='ProverRwFactoryIteration-ledger-v1',parent_ledger_sha256=sha(E.parent/'factory-cleanup/ledger.json'),backend_used=15,backend_ceiling=16,backend_remaining=1,extraction_used=49,extraction_ceiling=52,extraction_remaining=3,lean_used=236,lean_ceiling=260,lean_remaining=24,kani_used=57,kani_ceiling=60,kani_remaining=3,kani_this_step=3,kani_step_ceiling=4,kani_step_remaining=1,optimized_rust_test_check_commands=0,optimized_rust_test_check_ceiling=2,charon_release_commands=0,maximum_projected_reservation_bytes=maximum,rows=rows,print_axioms='N/A for every new result: no Lean theorem/emission/compile or axioms change',claim='056 candidate cut only.055 and057 actual factory invariant attempts are not accepted proofs. Actual cut/caller semantic association, finite16 composition and real Drop event producer remain OPEN.',targets='Both deployed targets not yet established; unmerged/unadopted.')
(E/'ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
print(json.dumps(dict(rows=len(rows),maximum_projected_reservation_gib=maximum/2**30)))
