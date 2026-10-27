#!/usr/bin/env python3
import json,pathlib
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-runjoin13-20261027'
rows=sorted([json.loads(p.read_text()) for p in e.glob('receipt-[0-9]*.json')],key=lambda r:r['attempt'])
used=sorted(int(p.stem.split('-')[1]) for p in e.glob('used-*.json'))
charged=sum(r.get('exit') is not None for r in rows)
k=e/'kani-invocations.jsonl';kani=len(k.read_text().splitlines()) if k.exists() else 0
x=dict(lean_charged=charged,lean_accepted=sum(r['accepted'] for r in rows),lean_rejected=sum(r.get('exit') is not None and not r['accepted'] for r in rows),refusals=len(list(e.glob('refusal-*.json'))),used_ids=used,next_id=max(used)+1 if used else 50600,lean_remaining=100-charged,kani_charged=kani,kani_remaining=2-kani,audit_reserved=3)
(e/'tally.json').write_text(json.dumps(x,indent=2)+'\n')
keys=['attempt','target','exit','wall_seconds','peak_rss_bytes','swaps','source_revision','source_sha256','axioms','accepted']
(e/'receipt-index.tsv').write_text('\t'.join(keys)+'\n'+'\n'.join('\t'.join(json.dumps(r.get(k)) if k=='axioms' else str(r.get(k,'')) for k in keys) for r in rows)+'\n')
print(json.dumps({k:v for k,v in x.items() if k!='used_ids'}))
