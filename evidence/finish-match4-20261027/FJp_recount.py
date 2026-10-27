from pathlib import Path
from collections import Counter
import hashlib,json,copy
E=Path(__file__).resolve().parent;R=E.parents[1]
src=R/'evidence/recount12-20261027/Rc12_LEDGER_DELTA.json'
x=json.loads(src.read_text());root=x['roots']['ARX_Root'];rows=copy.deepcopy(root['rows'])
removed=['L143','F3Y_G_L143']
assert json.loads((E/'FJp_087/receipt.json').read_text())['exit_status']==0
for r in rows:
 if r['id'] in removed:
  assert r['scope']=='actual antecedent' and r['classification']=='P'
  r['blocker_before']=r.get('blocker');r['blocker']='Discharged in FJp_Top.deployed for the installed dictionary; separate release/provenance obligations remain.'
  r['status']='removed';r['FJp_evidence']='FJp_Top.deployed, passing087; exact source/kernel statement comparison and closure audit'
  r['FJp_blocker']='None for this row in the installed dictionary; other release/runtime/provenance obligations are retained separately.'
def count(rows):
 out={}
 for scope in ['actual antecedent','deployment only','deployment alias']:
  c=Counter(r['classification'] for r in rows if r['scope']==scope)
  out[scope]={k:c[k] for k in 'TPGC'}
 out['deployment-inclusive non-alias']={k:out['actual antecedent'][k]+out['deployment only'][k] for k in 'TPGC'}
 return out
before=count(root['rows']);after=count([r for r in rows if r['id'] not in removed])
assert before['actual antecedent']==dict(T=83,P=11,G=13,C=0)
assert after['actual antecedent']==dict(T=83,P=9,G=13,C=0)
assert before['deployment-inclusive non-alias']==dict(T=89,P=28,G=13,C=0)
assert after['deployment-inclusive non-alias']==dict(T=89,P=26,G=13,C=0)
assert len([r for r in rows if r['id'] in removed])==2
out=dict(before='AspisR1.ARX_Root.deployed',after='AspisR1.FJp_Top.deployed',method=x['method'],ledger_source=str(src.relative_to(R)),ledger_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),before_counts=before,after_counts=after,removed=removed,added=[],delta=dict(T=0,P=-2,G=0,C=0),rows=rows,qualification='Owner/user adopts ARX; Rc12 adoption prose is older. Preserve the expanded deployment tasks. No FIr, earlier ARX, L166/D188 ruling or parallel-worker credit. This branch is not pushed or merged; the replacement root is delivered for lead integration. Joint premise inhabitation and deployed100-bit release remain unestablished.')
(E/'FJp_recount.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['before_counts','after_counts','removed','added','delta']},indent=2))
