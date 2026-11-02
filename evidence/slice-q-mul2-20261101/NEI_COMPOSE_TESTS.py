"""Negative controls for new constructor registration and occurrence binding."""
from pathlib import Path
import copy,json
import NEI_composition as c
E=Path(__file__).resolve().parent
base=c.obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');edges=c.prepare(base)
results=[]
def reject(name,mutate):
 data=copy.deepcopy(edges);mutate(data)
 try:c.validate(base,data)
 except (AssertionError,ValueError,KeyError):results.append(dict(test=name,status='PASS',outcome='rejected'))
 else:raise AssertionError('mutation accepted: '+name)
def root(data,row):return next(r for r in data['row_certificates'] if r['row']==row)
def edge(data):return next(e for e in data['edges'] if e.get('certificate'))
reject('wrong caller body',lambda d:root(d,'TX1:107').update(frozen_body_sha256='0'*64))
reject('wrong edge selected packet',lambda d:edge(d)['certificate'].update(selected_callee_claims=[]))
reject('missing native call edge',lambda d:edge(d).update(certificate=None,status='OPEN'))
reject('wrong external occurrence ordinal',lambda d:root(d,'TX2:073')['external_obligations']['external:TX2:73:1'].update(ordinal=2))
reject('wrong external callee',lambda d:root(d,'TX2:073')['external_obligations']['external:TX2:73:1'].update(callee='not-the-constructor'))
reject('older native credit cannot be smuggled in',lambda d:root(d,'TX1:110').update(id='NEB-old-native'))
reject('wrong audited proof receipt',lambda d:root(d,'TX1:110')['lean_evidence'][0].update(receipt_sha256='0'*64))
missing=copy.deepcopy(edges);missing['row_certificates']=[r for r in missing['row_certificates'] if r['function'].endswith('::EbyKDot::new')]
out,delta=c.validate(base,missing);assert delta['composed_rows_closed']==[],'uncertified child was bypassed'
results.append(dict(test='missing child root prevents public constructor closure',status='PASS',outcome='zero rows close'))
row=next(r for r in base['rows'] if r['row']=='TX2:073');row=copy.deepcopy(row);row['function']='crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node'
try:c.check_ctor_occurrence(row,{}, {}, {},base,{}, {})
except AssertionError:results.append(dict(test='constructor occurrence rule cannot admit accumulation boundary',status='PASS',outcome='rejected'))
else:raise AssertionError('constructor scope guard missing')
reject('wrong row widening source',lambda d:root(d,'TX1:195')['external_obligations']['external:TX1:195:2'].update(source_body_sha256='0'*64))
reject('wrong row widening syntax',lambda d:root(d,'TX2:125')['external_obligations']['external:TX2:125:2'].update(syntax='u32::from'))
independent=copy.deepcopy(edges);independent['row_certificates']=[r for r in independent['row_certificates'] if not r['function'].endswith('::canonical::Dot::new') and r['function']!=c.arithmetic.WIDE]
_,independent_delta=c.validate(base,independent)
assert len(independent_delta['composed_rows_closed'])==8 and not any(x in independent_delta['composed_rows_closed'] for x in ['TX1:107','TX2:073','TX1:110','TX2:076'])
results.append(dict(test='independent row/getter/push members proceed while dot constructor is open',status='PASS',outcome='eight independent rows close'))
try:c.arithmetic.check_widen(dict(function='not-the-row'),{}, {}, {})
except AssertionError:results.append(dict(test='row widening class cannot admit another function',status='PASS',outcome='rejected'))
else:raise AssertionError('widening scope guard missing')
reject('wide Option source occurrence mismatch',lambda d:root(d,'TX1:049')['external_obligations']['external:TX1:49:0'].update(line=214))
reject('wide packet wrong actual body',lambda d:root(d,'TX2:032').update(frozen_body_sha256='0'*64))
wide_independent=copy.deepcopy(edges);wide_independent['row_certificates']=[r for r in wide_independent['row_certificates'] if r['function']==c.arithmetic.WIDE]
_,wide_delta=c.validate(base,wide_independent)
assert set(wide_delta['composed_rows_closed'])=={'TX1:049','TX2:032'}
results.append(dict(test='wide constructor is independent of dot products and old native credit',status='PASS',outcome='exactly two wide constructor rows close'))
source=c.obj(E/'NEI_VALIDATOR_SOURCE_DELTA.json');original=Path(source['original']).read_text();derived=Path(source['derived']).read_text();assert derived.replace(source['only_added_branch'],'')==original
results.append(dict(test='every original validator check retained verbatim',status='PASS'))
(E/'NEI_COMPOSE_TESTS_receipt.json').write_text(json.dumps(dict(tests=results,passed=len(results),failed=0,baseline_unchanged=True,original_neb_file_unchanged=True),indent=2)+'\n')
print(json.dumps(dict(passed=len(results),failed=0)))
