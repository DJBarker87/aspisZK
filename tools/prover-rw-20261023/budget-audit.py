#!/usr/bin/env python3
"""Count actual task Kani invocations, including failed launches and drafts."""
from pathlib import Path
from collections import Counter
import hashlib,json
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/continuation'
rows=[]
for p in sorted((E/'receipts/candidate').glob('*/receipt.json')):
 r=json.loads(p.read_text())
 if 'kani' not in r['target']:continue
 name=p.parent.name;code=r['exit_status']
 kind='pass' if code==0 else 'timeout' if code==124 else 'cli_rejection' if code==2 else 'rejected_contract' if name=='field-codec-kani-arbitrary_field_decoders' else 'compile_failure'
 rows.append(dict(attempt=name,kind=kind,exit_status=code,receipt=str(p.relative_to(R)),receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],cgroup_memory_peak_bytes=r.get('cgroup_memory_peak_bytes'),swaps=r['swaps']))
counts=dict(Counter(x['kind'] for x in rows));result=dict(kani_invocations_used=len(rows),kani_limit=60,kani_remaining=60-len(rows),outcomes=counts,lean_compiles_used=0,lean_limit=100,lean_status='No assigned env J range; no new theorem has been compiled',invocations=rows)
assert len(rows)<=60
(E/'budget-audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='invocations'}))
