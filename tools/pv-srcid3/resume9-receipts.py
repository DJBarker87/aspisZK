#!/usr/bin/env python3
import pathlib,json
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
a=[json.loads(x) for x in (e/'resume9-attempts.jsonl').read_text().splitlines()] if (e/'resume9-attempts.jsonl').exists() else []
refusals=[]
for p in sorted(e.glob('reservation-42*.json')):
 r=json.loads(p.read_text())
 if r.get('allowed') is False:refusals.append(dict(attempt=int(p.stem.split('-')[-1]),utc=r.get('utc'),reason=r.get('reason','aggregate MemoryMax reservation'),charged=False))
(e/'resume9-refusals.json').write_text(json.dumps(refusals,indent=2)+'\n')
lines=['# Allocation 9 receipts','','Lean -M7000, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; one scope at a time. Each exact source snapshot, input/object hash, raw output, full printed axioms and timing is retained beside resume9-attempts.jsonl. No axiom report from a rejected attempt is accepted.','','| ID | Exact target | Exit | Validation | Wall | Peak RSS KiB | Swap | Source revision | Axiom reports |','| --- | --- | --- | --- | --- | --- | --- | --- | --- |']
for r in a:lines.append(f"| {r['attempt']} | {r['module']} | {r['exit']} | {'standard' if r['accepted'] else 'REJECTED'} | {r['wall']} | {r['peak_rss_kib']} | {r['swaps']} | {r['source_revision'][:10]} | {len(r['axioms'])}/{r['expected_axiom_reports']} |")
lines+=['',f'Charged Lean attempts: {len(a)}/100. Reservation refusals: {len(refusals)}, uncharged. Next unused ID: '+(e/'resume9-next-id.txt').read_text().strip()+'.','', '## Source discipline','', 'Only new allocation-9 PV_Src sources were installed; rejected drafts were corrected within those new modules. Existing published source modules and Stream A sources/objects were untouched. Their accepted source identity is resolved under h′. Accepted own object copies are rebuildable caches; no binary is committed. Source revision links distinguish exact snapshots from recorded worktree HEAD.']
lines+=['','## Kani runs','','0/0. Lean only under ruling (k); earlier arithmetic timeouts remain historical evidence, with no retry scheduled.']
(e/'RESUME9-RECEIPTS.md').write_text('\n'.join(lines)+'\n')
print('charged',len(a),'accepted',sum(r['accepted'] for r in a),'refusals',len(refusals))
