"""Read-only validation of continuation receipts; no compiler invocation."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];D=R/'evidence/pv-l2-sim-20261026'
allrs=[json.loads(p.read_text()) for p in sorted(D.glob('J*/receipt.json'))]
rs=[r for r in allrs if 21900<=r['attempt']<=21999]
assert [r['attempt'] for r in rs]==list(range(21900,22000))
manifest=json.loads((D/'FINAL-AUDIT-MANIFEST.json').read_text())
out=(D/'J21999/out.log').read_text()
ax=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))",out,re.S)
audit={n:a for n,a,_ in ax}
assert set(manifest['theorems'])<=set(audit)
assert len(manifest['theorems'])==121
assert all(set(a.split(', '))<={'propext','Classical.choice','Quot.sound',''} for a in audit.values())
for p in (R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_L2_*.lean'):
 assert not re.search(r'\b(sorry|axiom|native_decide|maxRecDepth|maxHeartbeats)\b',p.read_text()),p
 assert any(r['exit']==0 and r['target']=='R1Z/'+p.stem and r['source_sha256']==hashlib.sha256(p.read_bytes()).hexdigest() for r in allrs),p
zs=[json.loads(p.read_text()) for p in sorted(D.glob('z*/receipt.json'))]
assert len(zs)==20
for z in zs:
 assert hashlib.sha256((R/z['source_snapshot']).read_bytes()).hexdigest()==z['source_sha256'],z['attempt']
summary={'lean_attempts':len(rs),'lean_successes':sum(r['exit']==0 for r in rs),'kani_runs':len(zs),'kani_successes':sum(z['result']=='passed' for z in zs),'audited_modules':len(manifest['modules']),'audited_distinct_theorems':len(manifest['theorems']),'axioms':sorted({s for a in audit.values() for s in a.split(', ') if s}),'all_final_module_hashes_compiled':True,'final_receipt':'J21999/receipt.json','all_swaps_zero':all(r['swaps']==0 for r in rs+zs)}
(D/'SUMMARY-CONTINUATION.json').write_text(json.dumps(summary,indent=2)+'\n')
lines=['# Continuation receipts','','100 fresh Lean attempts and 20 fresh Kani runs. Source revisions describe the committed baseline; submitted source hashes identify proof edits. Direct dependency hashes were collected after runs, not a frozen transitive replay. Not all failed source versions are retained.','','| Attempt | Target | Exit | Wall | Peak RSS KiB | Swap | Receipt |','|---|---|---|---|---|---|---|']
for r in rs:
 i=r['attempt'];lines.append(f"| J{i} | {r['target']} | {r['exit']} | {r['wall']} | {r['peak_rss_kib']} | {r['swaps']} | [receipt](J{i}/receipt.json) |")
lines+=['','| Kani | Harness | Result | Exit | Wall | RSS KiB | Receipt |','|---|---|---|---|---|---|---|']
for r in zs:
 i=r['attempt'];lines.append(f"| {i} | {r['target']} | {r['result']} | {r['exit']} | {r['wall']} | {r['peak_rss_kib']} | [receipt]({i}/receipt.json) |")
(D/'INDEX-CONTINUATION.md').write_text('\n'.join(lines)+'\n')
lines=['# Continuation axioms audit','','J21999 compiled the final seed-prefix bridge and printed the following 121 distinct theorem results across 59 modules. Only standard axioms occur. The transport print is repeated in raw output. Cached focused dependency closure, not a frozen release replay. See [receipt](J21999/receipt.json) and [manifest](FINAL-AUDIT-MANIFEST.json).','','| Declaration | Axioms |','|---|---|']
lines += [f'| `{n}` | `{audit[n] or "[]"}` |' for n in manifest['theorems']]
(D/'AXIOMS-CONTINUATION.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(summary,indent=2))
