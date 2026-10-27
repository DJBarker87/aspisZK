#!/usr/bin/env python3
import pathlib,json
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
a=[json.loads(x) for x in (e/'resume7-attempts.jsonl').read_text().splitlines()] if (e/'resume7-attempts.jsonl').exists() else []
refusals=[]
for p in sorted(e.glob('reservation-40*.json')):
 r=json.loads(p.read_text())
 if r.get('allowed') is False:refusals.append(dict(attempt=int(p.stem.split('-')[-1]),utc=r.get('utc'),reason=r.get('reason','aggregate MemoryMax reservation'),charged=False))
(e/'resume7-refusals.json').write_text(json.dumps(refusals,indent=2)+'\n')
lines=['# Allocation 7 receipts','','Lean -M7000, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; one scope at a time. Each exact source snapshot, input/object hash, raw output, full printed axioms and timing is retained beside resume7-attempts.jsonl. No axiom report from a rejected attempt is accepted.','','| ID | Exact target | Exit | Validation | Wall | Peak RSS KiB | Swap | Source revision | Axiom reports |','| --- | --- | --- | --- | --- | --- | --- | --- | --- |']
for r in a:lines.append(f"| {r['attempt']} | {r['module']} | {r['exit']} | {'standard' if r['accepted'] else 'REJECTED'} | {r['wall']} | {r['peak_rss_kib']} | {r['swaps']} | {r['source_revision'][:10]} | {len(r['axioms'])}/{r['expected_axiom_reports']} |")
lines+=['',f'Charged Lean attempts: {len(a)}/100. Reservation refusals: {len(refusals)}, uncharged. Next unused ID: '+(e/'resume7-next-id.txt').read_text().strip()+'.','', '## Shared replacements','', 'Each overwritten shared source/object has its preimage under the assigned host job snapshots/resume7-ID. Accepted own object copies are rebuildable caches; no binary is committed. All changed dependent outputs, or exact pending exception reasons, are recorded in the gate JSON.']
lines+=['','## Kani runs','','Optimized compilation then named CBMC step; 6G/8G/swap0/Tasks64, one scope at a time. Kani has no #print axioms (N/A); exact input hashes and metadata retained.','','| Target | Exit | Wall seconds | Peak RSS KiB | Cgroup peak bytes | Swap | Revision |','| --- | --- | --- | --- | --- | --- | --- | --- |']
for name in ['srcid7-rootprefix11-try1','srcid7-rootinternal-try0']:
 r=json.loads((e/name/'receipt.json').read_text())
 lines.append(f"| {r['target']} | {r['exit_status']} | {r['wall_seconds']:.6f} | {r['peak_rss_kib']} | {r['cgroup_memory_peak_bytes']} | {r['swaps']} | {r['source_revision']} |")
lines+=['','Prefix timeout GNUtime RSS is a wrapper proxy, not aggregate solver RSS; use its cgroup peak. No equality is inferred from timeout. Internal comparison passed 514 checks. Both harness metadata records show no stubs. See resume7-kani-source-audit.json (193/193 source inputs per run match its commit) and resume7-kani-metadata.json.']
(e/'RESUME7-RECEIPTS.md').write_text('\n'.join(lines)+'\n')
print('charged',len(a),'accepted',sum(r['accepted'] for r in a),'refusals',len(refusals))
