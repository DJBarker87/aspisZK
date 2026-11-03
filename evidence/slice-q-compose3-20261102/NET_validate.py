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
 require(certificates==[], 'No new composed recipe is admitted before its complete native/model/domain/Result/frame validation is implemented')
 for edge in edges['edges']:
  name=edge['edge'];require(name in prior and name not in seen,'invented or duplicate edge')
  seen.add(name)
  require(edge==prior[name],'unregistered edge mutation or premature promotion: '+name)
 for k,v in old.items():
  if k!='edges':require(edges[k]==v,'changed inherited row certificate collection: '+k)
 return dict(schema='NET-additive-NEO-v1',baseline_revision='62ab0a9cc5',baseline_edges_sha256=sha(O/'NEO_EDGES.json'),newly_closed=[],new_count=0,total_closed=130,q_occurrences_closed=108,q_functions_closed=54,edge_closed=124,edge_total=257,roots=dict(neo.obj(O/'NEO_LEDGER_DELTA.json')['roots']),trust='P6/D188 option A semantic transport retained; reclassification, never removal',security_target_established=False)

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
