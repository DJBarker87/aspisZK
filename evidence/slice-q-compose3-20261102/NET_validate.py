"""Additive validator; NEO's validator executes unchanged on inherited evidence.

A new recipe must discharge every inner hypothesis. Source-only/native-log
work is deliberately excluded from composed status until all parts exist.
"""
from pathlib import Path
import sys,json,hashlib,copy
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent;O=E.parent/'slice-q-compose2-20261102'
sys.path.insert(0,str(O))
import NEO_validate as neo
require=neo.require
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def continuation(edges,certificates):
 old=obj(O/'NEO_EDGES.json')
 require(set(edges)==set(old),'added or removed edge collection fields')
 require(len(edges['edges'])==257,'changed edge inventory')
 prior={e['edge']:e for e in old['edges']};seen=set()
 import NET_window_certificates as windows
 expected_rows,new_edges=windows.expected(neo.baseline())
 import NET_wide_certificates as wide
 wide_rows,wide_edges=wide.expected(neo.baseline())
 expected_rows+=wide_rows;new_edges.update(wide_edges)
 import NET_prefix_certificates as prefix
 prefix_rows,prefix_edges=prefix.expected(neo.baseline())
 expected_rows+=prefix_rows;new_edges.update(prefix_edges)
 import NET_peer_certificates as peer
 peer_rows,peer_recipes,peer_edges=peer.expected(neo.baseline())
 new_edges.update(peer_edges)
 require(certificates==expected_rows,'new parser recipe differs from complete checked evidence')
 for edge in edges['edges']:
  name=edge['edge'];require(name in prior and name not in seen,'invented or duplicate edge')
  seen.add(name)
  expected=copy.deepcopy(prior[name])
  if name in peer_edges:expected=peer_edges[name]
  elif name in new_edges:expected.update(new_edges[name])
  require(edge==expected,'unregistered edge mutation or premature promotion: '+name)
 for k,v in old.items():
  if k!='edges':require(edges[k]==v,'changed inherited row certificate collection: '+k)
 return dict(schema='NET-additive-NEO-v1',baseline_revision='62ab0a9cc5',baseline_edges_sha256=sha(O/'NEO_EDGES.json'),newly_closed=sorted([c['row'] for c in expected_rows]+[r['row'] for r in peer_rows]),new_count=14,total_closed=144,q_occurrences_closed=122,q_functions_closed=61,edge_closed=164,edge_total=257,roots=dict(neo.obj(O/'NEO_LEDGER_DELTA.json')['roots']),trust='P6/D188 option A semantic transport retained; reclassification, never removal',security_target_established=False)

def validate(edges=None,certificates=None,replay=True):
 receipt=obj(O/'NEO_FINAL_REVIEW.json')
 require(receipt['exit_status']==0 and receipt['validator_sha256']==sha(O/'NEO_validate.py'),'NEO baseline validator pin')
 require(receipt['tests_sha256']==sha(O/'NEO_tests.py'),'NEO baseline tests pin')
 if replay:
  delta=neo.compose(neo.baseline(),neo.obj(O/'NEO_PEER_POSITIVE.json'),neo.obj(O/'NEO_EDGES.json'))
  require(delta==neo.obj(O/'NEO_LEDGER_DELTA.json'),'NEO inherited replay mismatch')
 return continuation(obj(E/'NET_EDGES.json') if edges is None else edges,obj(E/'NET_CERTIFICATES.json') if certificates is None else certificates)

if __name__=='__main__':
 d=validate()
 if '--write' in sys.argv:(E/'NET_LEDGER_DELTA.json').write_text(json.dumps(d,indent=1)+'\n')
 else:require(d==obj(E/'NET_LEDGER_DELTA.json'),'NET delta drift')
 print(json.dumps(d))
