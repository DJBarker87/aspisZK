"""Add explicit forest roots omitted by map-shaped historical manifest parsing."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NGZ_AUDIT_ROOTS.json').read_text());added=[]
for a in ['NGK','NGC','NGN','NGO','NGV','NGM','NGT','NGU','NGH','NGD','NFW','NGP','NGR','NGS']:
 d=next(E.parent.glob('*/'+a+'_HANDOFF.md')).parent;p=d/(a+'_AUDIT_ROOTS.json');m=json.loads(p.read_text());rs=list(m)if isinstance(m,dict)and not any(k in m for k in ['roots','groups','modules'])else []
 for p in d.glob(a+'_*IMPORT.lean'):rs+=re.findall(r'^#print axioms ([\w.]+)',p.read_text(),re.M)
 for n in rs:
  if n not in x['roots']:x['roots'].append(n);added.append(n)
# Earlier disjoint batches keep exact selected names; only not-yet-run last batch expands.
assert not (E/'NGZ_L031/receipt.json').exists()
x['groups'][-1]+=added;x['completion']=dict(added=added,reason='Include NGC map-shaped manifest keys and every explicit selected-forest import axiom root; no filtering or omission')
(E/'NGZ_AUDIT_ROOTS.json').write_text(json.dumps(x,indent=1));print(len(x['roots']),len(added))
