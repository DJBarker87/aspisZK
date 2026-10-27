from pathlib import Path
from collections import Counter
import hashlib,json
P=Path(__file__).resolve().parent;R=P.parents[1]
source=R/'evidence/finish-install5-20261026/FIr_recount.json'
old=json.loads(source.read_text());rows=old['rows']
def counts(rs):
 return {scope:dict(Counter(r['classification'] for r in rs if r['scope']==scope and r['status']!='removed')) for scope in ['actual antecedent','deployment only','deployment alias']}
c=counts(rows)
assert c==old['after_counts']
combined=dict(Counter(c['actual antecedent'])+Counter(c['deployment only']))
x=dict(before='AspisR1.FIr_Top.deployed',after='AspisR1.FIr_Top.deployed',method=old['method'],ledger_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),before_counts=c,after_counts=c,combined_excluding_alias=combined,removed=[],added=[],delta=dict(T=0,P=0,G=0,C=0),distinct_quarter_delta=dict(T=0,P=0,G=0,C=0),quantifiers='Identical inherited deployed statement. No new deployed theorem, premise removal, carrier, game, failure event, metric, constant or trust-item change. Native-local L144/L145 remain separately counted.',rows=rows)
(P/'FJe_recount.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({k:x[k] for k in ['before_counts','after_counts','combined_excluding_alias','delta']},indent=2))

actualSource=R/'evidence/recount10-20261026/Rc10_premises.json'
actual=json.loads(actualSource.read_text())
actualRows=actual['rows']
actualCounts=counts(actualRows)
for scope in ['actual antecedent','deployment only','deployment alias']:
 assert all(actualCounts[scope].get(k,0)==v for k,v in actual['raw_counts'][scope]['classes'].items())
y=dict(before=actual['actual_theorem'],after=actual['actual_theorem'],method=actual['method'],ledger_sha256=hashlib.sha256(actualSource.read_bytes()).hexdigest(),before_counts=actual['counts'],after_counts=actual['counts'],removed=[],added=[],delta=dict(T=0,P=0,G=0,C=0),rows=actualRows,quantifiers='Unchanged Rc10 deployed statement; FIr is a separate finish-row branch, not composed into Rc10 by FJe. No credit transferred between ledgers.')
(P/'FJe_Rc10-recount.json').write_text(json.dumps(y,indent=2)+'\n')
