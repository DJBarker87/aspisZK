"""Add checks to NET, never weaken or edit its inherited validator."""
from pathlib import Path
import sys,json,hashlib,copy
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;O=E.parent/'slice-q-compose3-20261102'
sys.path.insert(0,str(O))
import NET_validate as net
require=net.require
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def validate(edges=None,certificates=None,replay=True):
 prior=net.validate(replay=replay)
 require(prior==obj(O/'NET_LEDGER_DELTA.json'),'NET inherited ledger drift')
 intake=obj(E/'NEW_INTAKE.json')
 for name,h in intake['pins'].items():require(sha(E.parent.parent/name)==h,'intake pin drift: '+name)
 edges=obj(E/'NEW_EDGES.json') if edges is None else edges
 certificates=obj(E/'NEW_CERTIFICATES.json') if certificates is None else certificates
 import NEW_inverse_certificates as inverse
 expected_rows,new_edges=inverse.expected(net.neo.baseline())
 import NEW_peer_certificates as peer
 peer_rows,peer_edges=peer.expected(net.neo.baseline(),obj(O/'NET_EDGES.json'))
 expected_rows+=peer_rows;new_edges.update(peer_edges)
 require(certificates==expected_rows,'incomplete or unreviewed NEW certificate')
 expected_edges=obj(O/'NET_EDGES.json')
 for i,e in enumerate(expected_edges['edges']):
  if e['edge'] in new_edges:expected_edges['edges'][i]=new_edges[e['edge']]
 require(edges==expected_edges,'unregistered NEW edge change')
 return dict(schema='NEW-additive-NET-v1',baseline_revision='0e20f7ad5c',baseline_validator_sha256=sha(O/'NET_validate.py'),newly_closed=sorted(c['row'] for c in expected_rows),new_count=len(expected_rows),total_closed=prior['total_closed']+len(expected_rows),q_occurrences_closed=prior['q_occurrences_closed']+len(expected_rows),q_functions_closed=prior['q_functions_closed']+2,edge_closed=prior['edge_closed']+len(new_edges),edge_total=prior['edge_total'],roots=prior['roots'],trust=prior['trust'],security_target_established=False)
if __name__=='__main__':
 d=validate()
 if '--write' in sys.argv:(E/'NEW_LEDGER_DELTA.json').write_text(json.dumps(d,indent=1)+'\n')
 else:require(d==obj(E/'NEW_LEDGER_DELTA.json'),'NEW delta drift')
 print(json.dumps(d))
