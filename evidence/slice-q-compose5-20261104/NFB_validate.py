"""Additive NEW validator. Existing validators are imported unchanged."""
from pathlib import Path
import sys,json,hashlib,copy
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;O=E.parent/'slice-q-compose4-20261104'
sys.path.insert(0,str(O))
import NEW_validate as prior
from NFB_certificates import expected,ROOT
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def validate(edges=None,certificates=None,replay=True):
 old=prior.validate(replay=replay)
 assert old==obj(O/'NEW_LEDGER_DELTA.json'),'inherited result drift'
 rows,replacements=expected(prior.net.neo.baseline())
 certificates=obj(E/'NFB_CERTIFICATES.json') if certificates is None else certificates
 assert certificates==rows,'unregistered/incomplete root certificate'
 old_edges=obj(O/'NEW_EDGES.json');new_edges=copy.deepcopy(old_edges)
 newly=0
 for i,e in enumerate(new_edges['edges']):
  if e['edge'] not in replacements:continue
  newly+=e['status']!='CLOSED'
  new_edges['edges'][i]=replacements[e['edge']]
 edges=obj(E/'NFB_EDGES.json') if edges is None else edges
 assert edges==new_edges,'unregistered edge change or hidden prune'
 roots=dict(old['roots']);roots[ROOT]='CLOSED'
 return dict(schema='NFB-additive-NEW-v1',baseline_validator_sha256=sha(O/'NEW_validate.py'),
  newly_closed=sorted(r['row'] for r in rows),new_count=len(rows),total_closed=old['total_closed']+len(rows),
  q_occurrences_closed=old['q_occurrences_closed']+len(rows),q_functions_closed=old['q_functions_closed']+1,
  edge_closed=old['edge_closed']+newly,edge_total=old['edge_total'],roots=roots,
  trust=old['trust'],security_target_established=False,
  baseline_NEV_qualification='Inherited NEW accumulation rows retained exactly; NFA stronger audit admission is still withheld, no waiver or new NEV credit')
if __name__=='__main__':
 d=validate(replay='--no-replay' not in sys.argv)
 if '--write' in sys.argv:(E/'NFB_LEDGER_DELTA.json').write_text(json.dumps(d,indent=1)+'\n')
 else:assert d==obj(E/'NFB_LEDGER_DELTA.json'),'ledger drift'
 print(json.dumps(d))
