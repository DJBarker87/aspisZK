"""Record actual receipts separately from refusals and uncompiled drafts."""
from pathlib import Path
import json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029'
receipts=[]
for p in sorted(E.glob('*/receipt.json')):
 j=json.load(open(p));j['receipt_path']=str(p.relative_to(E));receipts.append(j)
lean=[x for x in receipts if x['expected_phase']=='Lean'];native=[x for x in receipts if x['expected_phase']!='Lean']
assert len(lean)<=100 and len(native)<=40
actual_ids=[x['attempt'] for x in lean];assert len(set(actual_ids))==len(actual_ids)
assert all(66300<=n<=66399 for n in actual_ids)
(E/'RUNS.json').write_text(json.dumps(dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),counts=dict(lean_actual=len(lean),lean_pass=sum(x['exit']==0 for x in lean),lean_fail=sum(x['exit']!=0 for x in lean),native_actual=len(native),native_pass=sum(x['exit']==0 for x in native),native_fail=sum(x['exit']!=0 for x in native),kani=0),receipts=receipts),indent=2)+'\n')
association=json.load(open(E/'v201-proof-association.json'))
rows=[]
for n in [201,220,237,236,233,197]:
 current=E/f'rows/V{n}.json'
 old=json.load(open(current if current.exists() else R/f'evidence/pv-rdcd3-20261028/rows/V{n}.json'))
 old.update(status=old['status'] if current.exists() else 'SUSPENDED',rdcd4_status='IN PROGRESS' if n==201 else 'NOT YET STARTED: V201-first order retained',endpoint_premises_removed=[],endpoint_premises_added=[],endpoint_premises_changed=[])
 if n==201 and old['status']!='RESTORED':old.update(reason='The new complete source-value/Result theorem passes, but the constructor/generated helper closure and final source/object coherence remain pending.',kernel_theorem='R1Z.PV_RDCD4_V201.source_reference',remaining_modules=association['pending_new_modules'],b3p6_1_reclassifications=0)
 rows.append(old)
(E/'STATUS.json').write_text(json.dumps(dict(phase='progress snapshot, not a final disposition',rows=rows),indent=2)+'\n')
print(json.dumps(json.load(open(E/'RUNS.json'))['counts']))
