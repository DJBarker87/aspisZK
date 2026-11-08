from pathlib import Path
import json
E=Path(__file__).resolve().parent;rs=[];roots=[]
for p in sorted(E.glob('NNL_L*/receipt.json')):
 x=json.loads(p.read_text());rs.append(x)
for p in(E/'NNL_audit').glob('batch*/proof*.json'):
 x=json.loads(p.read_text());roots+=x['results']
print(json.dumps(dict(completed_scopes=len(rs),raw_roots=len(roots),required_roots=len(json.loads((E/'NNL_AUDIT_ROOTS.json').read_text())['roots']),nonstandard_raw=[r for r in roots if not set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}],last_target=rs[-1]['module']if rs else None)))
