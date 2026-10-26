#!/usr/bin/env python3
"""Render the recorded receipts; this does not launch or replay a proof."""
import json,pathlib,re,subprocess
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
a=[json.loads(s) for s in (e/'attempts.jsonl').read_text().splitlines()]
k=[json.loads(s) for s in (e/'kani-invocations.jsonl').read_text().splitlines()]
lines=['# Recorded receipts','','Exact source hashes, dependency objects and complete #print axioms are in attempts.jsonl.','This table is a rendering of existing evidence, not a final kernel replay.','','## Lean','','| ID | Target | Exit | Wall | Peak RSS KiB | Swap | Revision | Axioms |','| --- | --- | --- | --- | --- | --- | --- | --- |']
for r in a:
 ax='standard only' if r['axioms'] and all('sorryAx' not in x for x in r['axioms']) and r['exit']==0 else ('FAILED — not accepted' if r['exit'] else 'see log')
 lines.append(f"| {r['attempt']} | {r['module']} | {r['exit']} | {r['wall']} | {r['peak_rss_kib']} | {r['swaps']} | {r['source_revision'][:10]} | {ax} |")
lines+=['','## Kani','','All commands optimized via explicit MIR/Rust flags, 6G/8G/swap0/tasks64; exact commands and source hashes in each receipt.','#print axioms: N/A for Rust/Kani. Cgroup peak is aggregate; timed-out parent `/usr/bin/time` RSS may omit killed descendants.','','| # | Target | Exit | Wall sec | RSS KiB | Aggregate peak bytes | Swap | Revision | Checks failed/total |','| --- | --- | --- | --- | --- | --- | --- | --- | --- |']
results=[]
for run in k:
 p=e/run['name']/'receipt.json'
 if not p.exists():continue
 r=json.loads(p.read_text());so=(p.parent/'stdout.log').read_text();m=re.search(r'\*\* (\d+) of (\d+) failed',so)
 checks=f'{m[1]}/{m[2]}' if m else 'no verification result'
 lines.append(f"| {run['number']} | {run.get('harness',run['name']) if isinstance(run.get('harness'),str) else run.get('harness',{}).get('pretty_name',run['name'])} | {r['exit_status']} | {r['wall_seconds']:.3f} | {r['peak_rss_kib']} | {r['cgroup_memory_peak_bytes']} | {r['swaps']} | {r['source_revision'][:10]} | {checks} |")
 results.append(dict(number=run['number'],name=run['name'],exit=r['exit_status'],wall_seconds=r['wall_seconds'],checks=checks))
(e/'RECEIPTS.md').write_text('\n'.join(lines)+'\n')
refusals=[]
for p in e.glob('reservation-*.json'):
 r=json.loads(p.read_text())
 if not r.get('allowed',True):refusals.append(p.name)
previous=json.loads((e/'BUDGET.json').read_text())
resume=previous.get('resume')
limit=130 if resume else 100
budget=dict(new_lean=len(a),predecessor_lean=4,total_lean=len(a)+4,authorized_lean_total=limit,remaining_lean=limit-4-len(a),new_kani=len(k),authorized_new_kani=20 if resume else 12,completed_kani=len(results),results=results,zero_charge_resource_refusals=refusals,other_zero_charge_preflights=[25401])
if resume:
 resume.update(charged_lean=len(a)-89,charged_kani=len(k)-12)
 budget['resume']=resume
(e/'BUDGET.json').write_text(json.dumps(budget,indent=2)+'\n')
print(json.dumps({key:value for key,value in budget.items() if key not in ['results','zero_charge_resource_refusals']}))
