"""Refresh compact, exact resume metrics without claiming source closure."""
from pathlib import Path
import json
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027'
t=json.loads((out/'TALLY.json').read_text()); rows=[]
for a in t['lean_charged']:
 r=json.loads((out/f'{a}.json').read_text());rows.append({k:r.get(k) for k in ['attempt','module','exit','wall','peak_rss_kib','swap','source_revision','source_sha256','axioms','target']})
native=[]
for n in t['kani_charged']:
 r=json.loads((out/n/'collected-receipt.json').read_text());native.append(dict(name=n,**{k:r.get(k) for k in ['harness','exit','wall','peak_rss_kib','swap','source_revision','print_axioms','target']}))
(out/'RESUME8-RECEIPTS.json').write_text(json.dumps(dict(tally=t,lean=rows,kani=native),indent=2)+'\n')
print('Lean',len(rows),'Kani',len(native),'next',t['next_id'])
