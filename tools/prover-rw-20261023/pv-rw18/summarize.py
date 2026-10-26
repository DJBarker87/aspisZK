"""Summarize immutable proof receipts. Does not launch or retry any job."""
from pathlib import Path
import json,re
r=Path(__file__).resolve().parents[3];e=r/'evidence/pv-rw18-20261026'
lean=[json.loads(p.read_text()) for p in sorted((e/'local').glob('*-receipt.json'))]
native=[json.loads(p.read_text()) for p in sorted(e.glob('pv-rw18-*/receipt.json'))]
kani=[x for x in native if 'kani' in x['target']]
for x in kani:
 out=(e/x['attempt']/'stdout.log').read_text()
 x['verification_success']=x['exit_status']==0 and '1 successfully verified harnesses, 0 failures, 1 total' in out
x=dict(lean_charged=len(lean),lean_pass=sum(v['exit_status']==0 for v in lean),lean_budget=100,kani_charged=len(kani),kani_pass=sum(v['verification_success'] for v in kani),kani_budget=20,
 lean=[{k:v[k] for k in ['attempt','module','source_revision','source_sha256','exit_status','wall_seconds','peak_rss_bytes','swaps','print_axioms']} for v in lean],
 native=[{k:v.get(k) for k in ['attempt','target','source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms','verification_success']} for v in native])
assert x['lean_charged']<=100 and x['kani_charged']<=20
(e/'summary.json').write_text(json.dumps(x,indent=2)+'\n')
print({k:v for k,v in x.items() if k not in ['lean','native']})
