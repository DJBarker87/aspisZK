#!/usr/bin/env python3
"""Negative mutation tests; synthetic certificates never earn ledger credit."""
from pathlib import Path
import copy,json,sys
sys.dont_write_bytecode=True
import NEB_validate as v
E=Path(__file__).resolve().parent
base=v.obj(v.N/'NDT_LEDGER.json');edges=v.obj(E/'NEB_EDGES.json');results=[]
def test(name,fn):
 fn();results.append(dict(test=name,result='PASS'))
def reject(fn):
 try:fn()
 except (AssertionError,ValueError,KeyError,OSError):return
 raise AssertionError('mutation admitted')
def open_with(cert):
 mutated=copy.deepcopy(edges);edge=next(e for e in mutated['edges'] if e['model_domain_theorems']);edge['certificate']=cert
 _,delta=v.extend(base,mutated)
 assert delta['closed_count']==0 and delta['edge_closed']==0
 assert all(x==['OPEN'] for x in delta['roots'].values())
test('unmodified original NDT invariants',lambda:v.ndt.validate_invariants(base))
test('missing certificate keeps every composed row OPEN',lambda:open_with(None))
edge=next(e for e in edges['edges'] if e['model_domain_theorems'])
wrong=dict(edge=edge['edge']+' wrong',status='CLOSED')
test('wrong certificate edge keeps every composed row OPEN',lambda:open_with(wrong))
wrong=dict(edge=edge['edge'],status='CLOSED',frozen_revision='0'*40)
test('wrong frozen revision keeps every composed row OPEN',lambda:open_with(wrong))
wrong=dict(edge=edge['edge'],status='CLOSED',frozen_revision=base['frozen_revision'],source_body_sha256='0'*64)
test('wrong body hash keeps every composed row OPEN',lambda:open_with(wrong))
wrong=dict(edge=edge['edge'],status='CLOSED',frozen_revision=base['frozen_revision'],source_body_sha256=edge['source_body_sha256'],kind='DIRECT_CALL',selected_callee_claims=[])
test('wrong callee PacketDomain selection keeps row OPEN',lambda:open_with(wrong))
model_only=dict(edge=edge['edge'],status='CLOSED',frozen_revision=base['frozen_revision'],source_body_sha256=edge['source_body_sha256'],kind='DIRECT_CALL',selected_callee_claims=sorted(set(c for r in base['rows'] if r['function']==edge['callee'] for c in r['selected_claims'])),inner_hypotheses_discharged=sorted(set(h['name'] for r in base['rows'] if r['function']==edge['callee'] for h in r['named_hypotheses'])),parts={'packet_domain':{'theorems':edge['model_domain_theorems']}})
test('model-only theorem cannot supply native/state/effect association',lambda:open_with(model_only))
missing=copy.deepcopy(edges);missing['edges'].pop()
test('missing slice edge is rejected',lambda:reject(lambda:v.extend(base,missing)))
dup=copy.deepcopy(edges);dup['edges'].append(dup['edges'][0])
test('duplicate slice edge is rejected',lambda:reject(lambda:v.extend(base,dup)))
changed=copy.deepcopy(base);changed['rows'][0]['composed_status']='CLOSED'
test('forged baseline CLOSED status is rejected by unchanged NDT invariants',lambda:reject(lambda:v.extend(changed,edges)))
_,delta=v.extend(base,edges)
test('validation never mutates authoritative baseline',lambda:(_ for _ in ()).throw(AssertionError()) if base!=v.obj(v.N/'NDT_LEDGER.json') else None)
print(json.dumps(dict(results=results,tests=len(results),composed_closed=delta['closed_count'],synthetic_evidence_credit=0),indent=1))
