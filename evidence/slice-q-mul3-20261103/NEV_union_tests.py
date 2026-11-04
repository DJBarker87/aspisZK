"""Mutation controls for exact new certificates and immutable inherited rows."""
from NEV_union import *
base=json.loads(lzma.decompress((E/'NEV_NET_BASELINE.json.xz').read_bytes()))
import NEV_materialize_net as material
be=obj(material.C/'NET_EDGES.json');out=obj(E/'NEV_DERIVED_LEDGER.json');edges=obj(E/'NEV_EDGES.json');cs=obj(E/'NEV_UNION_CERTIFICATES.json')
assert validate(out,edges,cs['edges'],cs['rows'],base,be)
checks=[]
def reject(name,change):
 o,e,c,r=map(copy.deepcopy,[out,edges,cs['edges'],cs['rows']]);change(o,e,c,r)
 try:validate(o,e,c,r,base,be)
 except (AssertionError,ValueError,KeyError):checks.append(name);return
 raise AssertionError('accepted mutation '+name)
key=next(k for k,c in cs['edges'].items() if c['kind']=='DIRECT_CALL')
def cert(e):return next(x['certificate'] for x in e['edges'] if x['edge']==key)
reject('missing native association',lambda o,e,c,r:cert(e)['parts'].pop('native_callsite_association'))
reject('residual inner hypothesis',lambda o,e,c,r:cert(e).update(residual_hypotheses=['callee_result']))
reject('wrong callee selection',lambda o,e,c,r:cert(e).update(selected_callee_claims=[]))
reject('missing canonical carrier',lambda o,e,c,r:cert(e)['parts'].pop('canonical_carrier'))
reject('missing SAME argument result',lambda o,e,c,r:cert(e)['parts'].pop('same_inputs_result'))
reject('inherited row changed',lambda o,e,c,r:o['rows'][next(i for i,x in enumerate(o['rows']) if x['composed_status']=='CLOSED' and x['row'] not in NEW|{'TX1:182','TX2:108'})].update(selected_claims=[]))
reject('native receiver pair dropped',lambda o,e,c,r:r['TX1:182']['native_pairs'].pop())
reject('copy controls dropped',lambda o,e,c,r:r['TX1:182'].update(copy_controls=[]))
reject('canonical weights omitted',lambda o,e,c,r:r['TX1:182'].update(domain=r['TX1:182']['domain'].replace('input immutable weight vector and ','input ')))
reject('external trait assumed',lambda o,e,c,r:r['TX1:182'].update(external_obligations={}))
reject('root hidden hypothesis',lambda o,e,c,r:r['TX1:182'].update(remaining_inner_hypotheses=['successful_child']))
reject('missing slice edge',lambda o,e,c,r:e['edges'].pop())
(E/'NEV_UNION_TESTS.json').write_text(json.dumps(dict(passed=len(checks),controls=checks),indent=2)+'\n')
print(len(checks),'mutation controls passed')
