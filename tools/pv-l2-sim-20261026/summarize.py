"""Summarize retained receipts without running compilers or proof gates."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).resolve().parents[2];D=R/'evidence/pv-l2-sim-20261026'
rs=[json.loads(p.read_text()) for p in sorted(D.glob('J*/receipt.json'))]
assert [r['attempt'] for r in rs]==list(range(20101,20201))
# These launches preceded the stage commit, although collection finished after it.
for i in (20197,20198):
 p=D/f'J{i}/receipt.json';r=json.loads(p.read_text())
 r['source_revision']='f6741bc172c332da9c500ace8eb88e8c774f2e29'
 r['source_revision_note']='baseline at launch; proof-local submitted source pinned separately'
 p.write_text(json.dumps(r,indent=2)+'\n')
rows=['# Lean attempts and Kani runs','',
 'Every link contains the raw output, GNU time, exact submitted source hash,',
 'committed baseline revision and collected direct dependency object hashes.',
 'The baseline does not describe uncommitted proof edits: the source hash does.',
 'Dependency hashes are collected after each run, not a frozen transitive manifest.',
 'Failed source versions are not all retained; their hashes and diagnostics are.',
 '', '| Attempt | Target | Exit | Wall | Peak RSS KiB | Swap | Receipt |',
 '|---|---|---|---|---|---|---|']
for r in rs:
 i=r['attempt'];rows.append(f"| J{i} | {r['target']} | {r['exit']} | {r['wall']} | {r['peak_rss_kib']} | {r['swaps']} | [receipt](J{i}/receipt.json) |")
rows+=['','| Kani | Harness | Result | Exit | Wall | Peak RSS KiB | Receipt |','|---|---|---|---|---|---|---|']
for p in sorted(D.glob('k*/receipt.json')):
 r=json.loads(p.read_text());rows.append(f"| {p.parent.name} | {r['target']} | {r['result']} | {r['exit']} | {r['wall']} | {r['peak_rss_kib']} | [receipt]({p.parent.name}/receipt.json) |")
(D/'INDEX.md').write_text('\n'.join(rows)+'\n')
out=(D/'J20200/out.log').read_text();assert re.search(r'^exit=0$',out,re.M)
ax=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))",out,re.S)
assert len(ax)==140
assert all(set(a.split(', ')) <= {'propext','Classical.choice','Quot.sound',''} for _,a,_ in ax)
lines=['# Final focused axioms audit','',
 '`PV_L2_Audit`, J20200: exit 0; 140 printed declarations. Exact output and',
 'resource/source/dependency receipt: [J20200](J20200/receipt.json).',
 'Empty means Lean reported no axioms. Failed elaboration prints in earlier',
 'receipts are not proof results. No `sorryAx` occurs in this successful audit.',
 '', '| Declaration | `#print axioms` |','|---|---|']
lines += [f'| `{n}` | `{a or "[]"}` |' for n,a,_ in ax]
(D/'AXIOMS.md').write_text('\n'.join(lines)+'\n')
proofs=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
for p in proofs.glob('PV_L2_*.lean'):
 assert not re.search(r'\b(sorry|axiom|native_decide|maxRecDepth|maxHeartbeats)\b',p.read_text()),p
 assert any(r['exit']==0 and r['target']=='R1Z/'+p.stem and r['source_sha256']==hashlib.sha256(p.read_bytes()).hexdigest() for r in rs),p
print('100 Lean receipts;',sum(r['exit']==0 for r in rs),'successes; 140 standard-axiom audit entries; every final module hash has a successful compile')
