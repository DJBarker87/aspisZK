from pathlib import Path
import json,hashlib
from collections import Counter
E=Path(__file__).resolve().parent;R=E.parents[1]
p=R/'evidence/recount7-20261026/Rc7_premises.json';ledger=json.loads(p.read_text())
removed={f'F3Y_G_L{n}' for n in [133,134,135,136,137,138,147]}
rows=ledger['rows'];after=[]
for row in rows:
 r=dict(row)
 if r['id'] in removed:
  r.update(status='removed',evidence='FIp_Top.deployed; FIp_Aligned.values derives FIn_Derived on the SAME shape/source-read/saved64 witness; FIp_Canonical/FIp_Join/FIp_Bound/FIp_Cost consume it.',blocker='Discharged globally; native-local row retained separately.')
 after.append(r)
def counts(rs):
 return {scope:dict(Counter(r['classification'] for r in rs if r['scope']==scope)) for scope in ['actual antecedent','deployment only','deployment alias']}
result=dict(before='AspisR1.Rc7_Top.deployed',after='AspisR1.FIp_Top.deployed',method=ledger['method'],ledger_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),before_counts=counts(rows),after_counts=counts([r for r in after if r['status']!='removed']),removed=sorted(removed),added=[],delta=dict(T=0,P=-7,G=0,C=0),distinct_quarter_delta=dict(T=0,P=-6,G=0,C=0),native_local='All native-local L133–L147 rows retained, with native/global witness domains counted separately.',quantifiers='Specialise operational carrier F and dictionary; same source/model/native events and conclusions. Remaining global Pair/matching/semantic owner is guarded by Shape derived in FIp_RunFinish on the SAME native witness. No caller-provided shape, replacement endpoint, or canonicality law is added.',rows=after)
(E/'FIp_recount.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['before_counts','after_counts','removed','delta','distinct_quarter_delta']},indent=2))
