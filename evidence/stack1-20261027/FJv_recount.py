from pathlib import Path
from collections import Counter
import hashlib,json,copy
E=Path(__file__).resolve().parent;R=E.parents[1]
p=R/'evidence/finish-chain1-20261027/FJu_recount.json'
x=json.loads(p.read_text());rows=copy.deepcopy(x['rows'])
for module in ['FJv_Top.lean','FJv_Deployed.lean']:
 assert any(module in (r:=json.loads(f.read_text()))['sources'] and r['exit_status']==0 for f in E.glob('FJv_*/receipt.json')), 'No passing top receipt: '+module
def count(rs):
 out={}
 for scope in ['actual antecedent','deployment only','deployment alias']:
  c=Counter(r['classification'] for r in rs if r['scope']==scope)
  out[scope]={k:c[k] for k in 'TPGC'}
 out['deployment-inclusive non-alias']={k:out['actual antecedent'][k]+out['deployment only'][k] for k in 'TPGC'}
 return out
def active():return [r for r in rows if r['status']!='removed']
before=count(active());assert before==x['after_counts']
steps=[]
for top,removed,expected,evidence in [
 ('AspisR1.FJv_Top.deployed',['L142','F3Y_G_L142'],3,'FJv_GlobalOwners.complete; FJv_ActualLiteral.strengthen; FJv_Top.deployed'),
 ('AspisR1.FJv_Deployed.deployed',['L146','F3Y_G_L146'],1,'FJv_GlobalTerminal.owners; FJv_DLiteral.from_cut; FJv_Deployed.deployed')]:
 b=count(active())
 for rid in removed:
  hits=[r for r in rows if r['id']==rid];assert len(hits)==1
  r=hits[0];assert r['status']!='removed' and r['scope']=='actual antecedent' and r['classification']=='P'
  r['blocker_before']=r.get('blocker');r.update(status='removed',blocker='None for this family in the checked composition; deployment/artifact association remains separate.',FJv_evidence=evidence)
 a=count(active());assert a['actual antecedent']==dict(T=83,P=expected,G=13,C=0)
 steps.append(dict(top=top,before_counts=b,after_counts=a,removed=removed,added=[],reclassified=[],delta=dict(T=0,P=-2,G=0,C=0),rows=copy.deepcopy(rows)))
assert [r['id'] for r in active() if r['scope']=='actual antecedent' and r['classification']=='P']==['L154']
out=dict(method=x['method'],source=str(p.relative_to(R)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),steps=steps,qualification='Configuration substitution earns no premise-removal credit. Inherited deployment-only rows and aliases are preserved mechanically; the inherited prose inclusive count differs by one P from its JSON. No unconditional joint deployed fixture or full release claim.')
(E/'FJv_recount.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([{k:s[k] for k in ['top','before_counts','after_counts','removed','delta']} for s in steps],indent=2))
