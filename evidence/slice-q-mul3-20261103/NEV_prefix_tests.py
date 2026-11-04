"""Mutations must reject or demonstrably demote; no exception-only oracle."""
from pathlib import Path
import copy,json
import NEV_composition as m
E=Path(__file__).resolve().parent
c,p,prepare,validate=m.context();base=m.obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');edges=prepare(base)
results=[]
def rejected(name,fn):
 try:fn()
 except (AssertionError,ValueError,KeyError):results.append(dict(test=name,status='PASS',outcome='rejected'))
 else:raise AssertionError('accepted mutation: '+name)
def change_edges(mut):
 d=copy.deepcopy(edges);mut(d);return validate(base,d)
def root(d):return next(v for v in d['row_certificates'] if v['row']=='TX1:185')
def actual(d):return next(v for v in d['edges'] if v['caller']==m.PREFIX and v['callee']==m.MUL)
x=m.obj(E/'NEV_PREFIX_CAMPAIGN.json')
y=copy.deepcopy(x);y['accepted']=[r for r in y['accepted'] if r['hi']!=110]
rejected('missing capacity110 cannot stand in for complete caller family',lambda:m.gate.audit(y))
y=copy.deepcopy(x);z=next(r for r in y['accepted'] if r['stride']==5);z['stride']=1
rejected('unproved capacities cannot be filled by interval metadata',lambda:m.gate.audit(y))
y=copy.deepcopy(x);z=y['accepted'][0];z['positive'],z['negative']=z['negative'],z['positive']
rejected('negative receipt cannot be used as positive native evidence',lambda:m.gate.audit(y))
rejected('wrong prefix source body',lambda:change_edges(lambda d:root(d).update(frozen_body_sha256='0'*64)))
rejected('missing full Result/source theorem',lambda:change_edges(lambda d:root(d)['lean_evidence'][0].update(theorems=['NEV_PrefixCalls.member'])))
rejected('wrong std occurrence line',lambda:change_edges(lambda d:next(iter(root(d)['external_obligations'].values())).update(line=999)))
rejected('direct M31 call cannot be pruned',lambda:change_edges(lambda d:actual(d).update(selected_target=False)))
rejected('prefix edge cannot select an unrelated callee packet',lambda:change_edges(lambda d:actual(d)['certificate'].update(selected_callee_claims=[])))
rejected('std class cannot admit outside-slice accumulation constructor',lambda:c.neb._NEV_check_prefix_external(dict(function='crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node'),{}, {},{}))
missing=copy.deepcopy(edges);actual(missing).update(certificate=None,status='OPEN')
out,delta=validate(base,missing)
assert not {'TX1:185','TX2:111'}&set(delta['composed_rows_closed']),'uncertified actual child bypassed'
assert set(m.obj(E/'NEV_NEI_REPLAY_DELTA.json')['composed_rows_closed'])<=set(delta['composed_rows_closed']),'independent inherited closures lost'
results.append(dict(test='missing actual M31 edge demotes prefix only',status='PASS',outcome='both prefix rows OPEN; all66 independent inherited rows CLOSED'))
out,delta=validate(base,edges)
assert {'TX1:185','TX2:111'}<=set(delta['composed_rows_closed']) and len(delta['composed_rows_closed'])==68 and delta['edge_closed']==117
results.append(dict(test='complete positive packet closes both prefix occurrences',status='PASS',outcome='68 component rows,117 edges'))
(E/'NEV_PREFIX_TESTS.json').write_text(json.dumps(dict(passed=len(results),tests=results),indent=2)+'\n')
print(json.dumps(dict(passed=len(results))))
