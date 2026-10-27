from pathlib import Path
from collections import Counter
import hashlib,json,copy
E=Path(__file__).resolve().parent;R=E.parents[1]
p=R/'evidence/finish-match4-20261027/FJp_recount.json'
x=json.loads(p.read_text());rows=copy.deepcopy(x['rows'])
removed=['L144','L145','F3Y_G_L144','F3Y_G_L145']
assert json.loads((E/'FJu_010/receipt.json').read_text())['exit_status']==0
before=[r for r in rows if r['status']!='removed']
for r in rows:
 if r['id'] in removed:
  assert r['scope']=='actual antecedent' and r['classification']=='P' and r['status']!='removed'
  r['blocker_before']=r.get('blocker');r['status']='removed'
  r['blocker']='None for this first/chain row in the installed dictionary. Release association and other rows remain separate.'
  r['FJu_evidence']='FJu_Top.deployed010; KernelComparison011; same-run derivation006; global transport002'
def count(rs):
 out={}
 for scope in ['actual antecedent','deployment only','deployment alias']:
  c=Counter(r['classification'] for r in rs if r['scope']==scope)
  out[scope]={k:c[k] for k in 'TPGC'}
 out['deployment-inclusive non-alias']={k:out['actual antecedent'][k]+out['deployment only'][k] for k in 'TPGC'}
 return out
bc=count(before);ac=count([r for r in rows if r['status']!='removed'])
assert bc==x['after_counts']
assert bc['actual antecedent']==dict(T=83,P=9,G=13,C=0)
assert ac['actual antecedent']==dict(T=83,P=5,G=13,C=0)
assert bc['deployment-inclusive non-alias']==dict(T=89,P=26,G=13,C=0)
assert ac['deployment-inclusive non-alias']==dict(T=89,P=22,G=13,C=0)
assert len([r for r in rows if r['id'] in removed])==4
out=dict(before='AspisR1.FJp_Top.deployed',after='AspisR1.FJu_Top.deployed',method=x['method'],ledger_source=str(p.relative_to(R)),ledger_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),before_counts=bc,after_counts=ac,removed=removed,added=[],delta=dict(T=0,P=-4,G=0,C=0),rows=rows,qualification='Exact inherited expanded deployment ledger method:89T/26P/13G before, versus89T/25P/13G in the prose ledger. This preserves all17 deployment-only P rows mechanically; no unrelated row or parallel-worker credit. Actual antecedent9P->5P agrees independently. No joint root-premise inhabitant or deployed100-bit release claim.')
(E/'FJu_recount.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['before_counts','after_counts','removed','added','delta']},indent=2))
