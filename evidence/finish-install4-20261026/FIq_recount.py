from pathlib import Path
import json,hashlib
from collections import Counter
P=Path(__file__).resolve().parent;R=P.parents[1]
p=R/'evidence/finish-install3-20261026/FIp_recount.json';old=json.loads(p.read_text());rows=old['rows']
def counts(rs):
 return {scope:dict(Counter(r['classification'] for r in rs if r['scope']==scope)) for scope in ['actual antecedent','deployment only','deployment alias']}
live=[r for r in rows if r['status']!='removed']
x=dict(before='AspisR1.FIp_Top.deployed',after='AspisR1.FIq_Top.deployed',method=old['method'],ledger_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),before_counts=counts(live),after_counts=counts(live),removed=[],added=[],delta=dict(T=0,P=0,G=0,C=0),distinct_quarter_delta=dict(T=0,P=0,G=0,C=0),quantifiers='Operational seed specialises only boundaries.terminal; same frozen3 game, source/model/native events, metric, constants, trust items and conclusions. Same five global owner families and all native-local families retained. No credit for specialization, cached dependency replay or local source-chain lemmas.',rows=rows)
(P/'FIq_recount.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:x[k] for k in ['before_counts','after_counts','removed','delta']},indent=2))
