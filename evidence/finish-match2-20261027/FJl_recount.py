from pathlib import Path
from collections import Counter
import json,hashlib
P=Path(__file__).resolve().parent;R=P.parents[1]
src=R/'evidence/recount11-20261027/Rc11_premises.json'
x=json.loads(src.read_text());rows=[r for r in x['rows'] if r['status']!='removed']
counts={scope:dict(Counter(r['classification'] for r in rows if r['scope']==scope)) for scope in ['actual antecedent','deployment only','deployment alias']}
for scope,c in counts.items():
 for k,v in x['after'][scope]['classes'].items():assert c.get(k,0)==v
out=dict(before='AspisR1.ARX_Root.deployed',after='AspisR1.ARX_Root.deployed',new_deployed_theorem=None,method=x['method'],ledger_source=str(src.relative_to(R)),ledger_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),before_counts=counts,after_counts=counts,combined_excluding_alias=dict(Counter(counts['actual antecedent'])+Counter(counts['deployment only'])),removed=[],added=[],delta=dict(T=0,P=0,G=0,C=0),rows=rows,qualification='Owner adopted ARX_Root on 2026-10-27. This job does not credit the earlier ARX/Rc10 delta or transfer FIr global L144/L145 removals to ARX. Both L143 scopes remain retained. Model, game, carriers, failure event, metric, constants, trust and top kernel are unchanged.')
(P/'FJl_recount.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['before_counts','after_counts','combined_excluding_alias','delta']},indent=2))
