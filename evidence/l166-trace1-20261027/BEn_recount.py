from pathlib import Path
from collections import Counter
import json,copy,hashlib
P=Path(__file__).resolve().parent; R=P.parents[1]
j=json.loads((R/'evidence/recount12-20261027/Rc12_LEDGER_DELTA.json').read_text())
before=copy.deepcopy(j['roots']['ARX_Root']['rows']);after=copy.deepcopy(before)
row=next(r for r in after if r['id']=='L166')
row.update(status='closed in extracted-trace interpretation',scope='discharged deployment row',evidence='BEn_LocalAssociation.observation; BEn_ReachedLaws.cuts; BEn_AdmittedCuts.selected; BEn_OriginalAssociation.selected; BEn_Top.deployed',blocker='No L166-local blocker under adopted D188 trace fidelity. Separate D188-P2, P7 and joint fixture rows retained.')
def count(rows):
 return dict(Counter(r['classification'] for r in rows if r['scope'] in ['actual antecedent','deployment only']))
def actual(rows):return dict(Counter(r['classification'] for r in rows if r['scope']=='actual antecedent'))
b=count(before);a=count(after)
assert b=={'T':89,'P':28,'G':13}
assert a=={'T':89,'P':27,'G':13}
assert actual(before)==actual(after)=={'T':83,'P':11,'G':13}
assert not any(r['id'] in ['L159','L181','L185'] for r in before)
statement=(P/'BEn_BEFORE_statement.lean.txt').read_bytes()
assert statement==(P/'BEn_AFTER_statement.lean.txt').read_bytes()
out=dict(method=j['method'],base='Rc12 ARX atomic ledger; inherited added D188-P2 deployment rows retained',before=dict(actual=actual(before),deployment_inclusive=b),after=dict(actual=actual(after),deployment_inclusive=a),delta=dict(T=0,P=-1,G=0,C=0),removed=['L166'],added=[],reclassified=[],actual_binders_removed=0,statement_sha256=hashlib.sha256(statement).hexdigest(),limits='Removal applies only to the specifically associated extracted batch under the adopted trace trust. No source-to-ELF, D188-P2 transport or joint non-vacuity closure.',rows_before=before,rows_after=after)
(P/'BEn_RECOUNT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if not k.startswith('rows')}))
