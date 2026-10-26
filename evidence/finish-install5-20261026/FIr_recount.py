from pathlib import Path
from collections import Counter
import hashlib,json
P=Path(__file__).resolve().parent;R=P.parents[1]
source=R/'evidence/finish-install4-20261026/FIq_recount.json'
old=json.loads(source.read_text());rows=old['rows']
def counts(rs):
 return {scope:dict(Counter(r['classification'] for r in rs if r['scope']==scope and r['status']!='removed')) for scope in ['actual antecedent','deployment only','deployment alias']}
before=counts(rows)
removed=['F3Y_G_L144','F3Y_G_L145']
for row in rows:
 if row['id'] in removed:
  assert row['status']=='retained'
  row.update(status='removed',evidence='FIr_PhysicalInitial.on_run, FIr_PhysicalChain.on_run, FIr_GlobalOwners.complete, FIr_GlobalOwners2.complete, FIr_Top.deployed',blocker='',disposition='Initial/chain equation derived from the SAME accepted prepare call, source prefix, returned alpha and literal view; no replacement premise.')
x=dict(before='AspisR1.FIq_Top.deployed',after='AspisR1.FIr_Top.deployed',method=old['method'],ledger_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),before_counts=before,after_counts=counts(rows),removed=removed,added=[],delta=dict(T=0,P=-2,G=0,C=0),distinct_quarter_delta=dict(T=0,P=-2,G=0,C=0),quantifiers='Same installation, complete conclusion, game, failure events, metric, constants and trust items. The source-global initial and chain equations are removed. Native-local L144/L145 remain separately counted; no alias discount.',rows=rows)
(P/'FIr_recount.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({k:x[k] for k in ['before_counts','after_counts','removed','delta']},indent=2))
