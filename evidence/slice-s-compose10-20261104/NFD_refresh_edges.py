"""Reporting only: derive edge status from the already checked rows."""
from pathlib import Path
import json
E=Path(__file__).resolve().parent;R=E.parent.parent
spec=json.loads((R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json').read_text())['slices']['S']
rows=json.loads((E/'NFD_CHECKED_ROWS.json').read_text());previous={x['edge']:x for x in json.loads((E/'NFD_EDGES.json').read_text())}
out=[]
for edge in spec['internal_edges']:
 f,g=edge.split(' -> ');obs=[o for r in rows if r['function']==f for o in r['caller_domain_obligations'] if o.get('callee')==g]
 old=previous.get(edge,{});closed=bool(obs) and all(o['status']=='CLOSED' for o in obs)
 out.append(dict(edge=edge,status='CLOSED' if closed else 'OPEN',certificates=list(dict.fromkeys(o['discharged_by'] for o in obs if o.get('discharged_by'))),required_named_hypotheses=list(dict.fromkeys(h for o in obs for h in o['required_named_hypotheses'])),obstacle=None if closed else old.get('obstacle','Exact native call-domain/physical certificate remains missing.')))
assert len(out)==len(spec['internal_edges'])==129
(E/'NFD_EDGES.json').write_text(json.dumps(out,indent=1)+'\n')
print(dict(closed_edges=sum(x['status']=='CLOSED' for x in out)))
