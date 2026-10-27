#!/usr/bin/env python3
"""Summarize retained receipts without launching builds."""
import hashlib,json,pathlib,subprocess
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-runjoin8-20261026'
rows=sorted((json.loads(p.read_text()) for p in e.glob('receipt-*.json')),key=lambda r:r['attempt'])
lines=['attempt\ttarget\texit\twall_seconds\tpeak_rss_bytes\tswaps\tsource_revision\tsource_sha256\taxioms\taccepted']
for r in rows:lines.append('\t'.join(str(r.get(k,'')) if k!='axioms' else json.dumps(r.get(k)) for k in ['attempt','target','exit','wall_seconds','peak_rss_bytes','swaps','source_revision','source_sha256','axioms','accepted']))
(e/'receipt-index.tsv').write_text('\n'.join(lines)+'\n')
kani=[]
for p in sorted(e.glob('pv8-runjoin-kani-*/receipt.json')):
 r=json.loads(p.read_text());out=(p.parent/'out.log').read_text();kani.append(dict(number=r['number'],harness=r['harness'],exit=r['exit'],successful='VERIFICATION:- SUCCESSFUL' in out,wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_bytes'],cgroup_peak_bytes=r['cgroup_peak_bytes'],swaps=r['swaps'],revision=r['source_revision']))
counts=dict(lean_attempts=sum(r.get('exit') is not None for r in rows),accepted=sum(r['accepted'] for r in rows),failed=sum(not r['accepted'] for r in rows),refusals=len(list(e.glob('refusal-*.json'))),kani_runs=len(kani),kani_passes=sum(r['successful'] for r in kani),kani_timeouts=sum(r['exit']==124 for r in kani))
x=dict(budget=dict(lean=100,kani=8),counts=counts,kani=kani)
(e/'BUDGET.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(counts))
