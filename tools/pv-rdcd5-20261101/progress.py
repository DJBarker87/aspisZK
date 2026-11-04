"""Aggregate actual run receipts without turning drafts into proof credit."""
from pathlib import Path
import json,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd5-20261101'
receipts=[]
for p in sorted(E.glob('*/receipt.json')):
 j=json.load(open(p));j['receipt_path']=str(p.relative_to(E));receipts.append(j)
lean=[x for x in receipts if x['expected_phase']=='Lean'];native=[x for x in receipts if x['expected_phase']!='Lean']
assert len(lean)<=100 and len(native)<=30
ids=[x['attempt'] for x in lean];assert len(ids)==len(set(ids)) and all(78200<=i<=78299 for i in ids)
counts=dict(lean=len(lean),lean_pass=sum(x['exit']==0 for x in lean),lean_fail=sum(x['exit']!=0 for x in lean),native=len(native),kani=0)
(E/'RUNS.json').write_text(json.dumps(dict(counts=counts,receipts=receipts),indent=2)+'\n')
s=json.load(open(E/'SESSION.json'));s.update(lean_attempts_used=len(lean),native_scopes_used=len(native),kani_runs_used=0,ids_consumed=ids,scopes_launched=len(receipts));(E/'SESSION.json').write_text(json.dumps(s,indent=2)+'\n')
passed={x['module']:x for x in lean if x['exit']==0}
drafts=[]
for p in sorted((R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RDCD5_*.lean')):
 m='R1Z/'+p.stem;h=hashlib.sha256(p.read_bytes()).hexdigest();x=passed.get(m)
 drafts.append(dict(module=m.replace('/','.'),path=str(p.relative_to(R)),sha256=h,status='COMPILED; row/source association checked separately' if x and x['source_sha256']==h else 'UNCOMPILED DRAFT; no theorem or row credit'))
(E/'UNCOMPILED-DRAFTS.json').write_text(json.dumps(drafts,indent=2)+'\n')
print(json.dumps(counts))
