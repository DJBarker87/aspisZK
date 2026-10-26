"""Proposed G reclassification only; no theorem edit or premise-removal credit."""
from pathlib import Path
import json,hashlib,collections,copy
E=Path(__file__).resolve().parent;R=E.parents[1]
G={'L083','L084'}|{f'Rc5_G{i:03d}' for i in range(1,12)}
result={}
for label,rel in [('FGl','evidence/finish-global-20261026/FGl_premises.json'),('Rc6','evidence/recount6-20261026/Rc6_premises.json')]:
 p=R/rel;old=json.loads(p.read_text());rows=copy.deepcopy(old['rows'])
 assert G <= {r['id'] for r in rows}
 for r in rows:
  if r['id'] in G:
   assert r['classification']=='P'
   r['classification']='G';r['reclassification_citation']='SECURITY-CONTRACT-20261021.md, Owner-approved amendment 2026-10-26 §2(a–d); C3-BIN 2026-10-23 18:05 success conditioning'
 def counts(rs):return dict(collections.Counter(r['classification'] for r in rs))
 result[label]=dict(actual_theorem=old['actual_theorem'],baseline_path=rel,baseline_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),before_counts=old['counts'],after_counts={
  'actual':counts([r for r in rows if r['scope']=='actual antecedent']),
  'deduplicated_actual_plus_deployment':counts([r for r in rows if r['scope']!='deployment alias'])},
  reclassified=sorted(G),mathematical_premises_removed=0,trust_items_changed=0,rows=rows)
assert result['FGl']['after_counts']['actual']==dict(T=83,P=28,G=13)
assert result['Rc6']['after_counts']['actual']==dict(T=83,P=19,G=13)
assert result['FGl']['after_counts']['deduplicated_actual_plus_deployment']==dict(T=89,P=36,G=13)
assert result['Rc6']['after_counts']['deduplicated_actual_plus_deployment']==dict(T=89,P=27,G=13)
(E/'TAu_recount.json').write_text(json.dumps(result,indent=2)+'\n')
print('FGl 83T/41P -> 83T/28P/13G; Rc6 83T/32P -> 83T/19P/13G; premises removed 0')
