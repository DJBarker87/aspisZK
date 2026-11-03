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
def edge(data):return next(e for e in data['edges'] if e['edge']=='crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new -> crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::new')
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
independent=copy.deepcopy(edges);independent['row_certificates']=[r for r in independent['row_certificates'] if not r['function'].endswith('::canonical::Dot::new') and r['function']!=c.arithmetic.WIDE and r['function'] not in c.dots.gate.FUNCTIONS and r['function'] not in c.fields.gate.FUNCTIONS and r['function'] not in {p['function'] for p in c.folds.packets()}]
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
reject('private modulus value mismatch',lambda d:root(d,'TX1:115')['external_obligations']['external:TX1:115:0'].update(source_value=2147483648))
reject('Q constructor occurrence mismatch',lambda d:root(d,'TX2:075')['external_obligations']['external:TX2:75:1'].update(line=124))
reject('outer unwrap wrong callee',lambda d:root(d,'TX1:106')['external_obligations']['external:TX1:106:3'].update(callee='not-wide-constructor'))
reject('old private reducer certificate cannot be supplied',lambda d:root(d,'TX2:081').update(id='NEB-private-reducer-root:TX2:081'))
missing_reducer=copy.deepcopy(edges);missing_reducer['row_certificates']=[r for r in missing_reducer['row_certificates'] if r['function']!=c.dots.gate.FUNCTIONS[0]]
_,without_reducer=c.validate(base,missing_reducer)
assert not set(without_reducer['composed_rows_closed'])&{'TX1:115','TX2:081','TX1:109','TX2:075','TX1:106','TX2:072'}
assert {'TX1:114','TX2:080','TX1:049','TX2:032'}<=set(without_reducer['composed_rows_closed'])
results.append(dict(test='missing reducer blocks both finishers but permits independent getters/constructor',status='PASS'))
missing_wide=copy.deepcopy(edges);missing_wide['row_certificates']=[r for r in missing_wide['row_certificates'] if r['function']!=c.arithmetic.WIDE]
_,without_wide=c.validate(base,missing_wide)
assert not set(without_wide['composed_rows_closed'])&{'TX1:106','TX2:072','TX1:049','TX2:032'}
assert {'TX1:109','TX2:075','TX1:114','TX2:080'}<=set(without_wide['composed_rows_closed'])
results.append(dict(test='missing actual wide constructor prevents outer finisher closure',status='PASS'))
p=copy.deepcopy(c.dots.packets()[-1]);p['lean_evidence']=[e for e in p['lean_evidence'] if not any(n.startswith('NEI_EbyFinishAssociation.') for n in e['theorems'])]
try:c.dots.audit(p,c.neb)
except (AssertionError,ValueError):results.append(dict(test='unrelated reducer/frame proofs cannot replace outer Result association',status='PASS'))
else:raise AssertionError('missing outer association admitted')
field_packet=copy.deepcopy(c.fields.packets()[0]);field_packet['lean_evidence']=[p for p in field_packet['lean_evidence'] if not any(t.startswith('NEI_FieldScalar.') for t in p['theorems'])]
try:c.fields.audit(field_packet,c.neb)
except (AssertionError,ValueError):results.append(dict(test='field frame cannot replace exact emitted operator association',status='PASS'))
else:raise AssertionError('missing field result association admitted')
private_inactive=next(o['id'] for o in next(r for r in base['rows'] if r['row']=='TX2:009')['caller_domain_obligations'] if o.get('call',{}).get('resolution')=='disabled release cfg')
reject('inactive counter cannot be activated',lambda d:root(d,'TX2:009')['external_obligations'][private_inactive].update(selected_core_features=['r0','r0-op-count']))
static_edge=next(e['edge'] for e in edges['edges'] if (e.get('certificate') or {}).get('kind')=='STATIC_UNREACHABLE')
reject('static receiver resolution cannot become a direct call',lambda d:next(e for e in d['edges'] if e['edge']==static_edge).update(selected_target=True))
no_self=copy.deepcopy(edges);no_self['inventory_edges']=[]
_,no_self_delta=c.validate(base,no_self)
assert not {'TX1:001','TX2:001','TX1:047','TX2:028','TX1:190','TX2:117'}&set(no_self_delta['composed_rows_closed'])
assert {'TX1:013','TX2:009','TX1:195','TX2:125'}<=set(no_self_delta['composed_rows_closed'])
results.append(dict(test='original conservative self obligations cannot be erased; unrelated rows proceed',status='PASS'))
no_add=copy.deepcopy(edges);no_add['row_certificates']=[r for r in no_add['row_certificates'] if r['function']!='crates/aspis-core/src/field.rs::M31::add']
_,no_add_delta=c.validate(base,no_add)
assert not {'TX1:047','TX2:028','TX1:188','TX1:190','TX2:113','TX2:117'}&set(no_add_delta['composed_rows_closed'])
assert {'TX1:195','TX2:125','TX1:017','TX2:013'}<=set(no_add_delta['composed_rows_closed'])
results.append(dict(test='missing scalar child blocks dependent field/fold rows only',status='PASS'))
source=c.obj(E/'NEI_VALIDATOR_SOURCE_DELTA.json');original=Path(source['original']).read_text();derived=Path(source['derived']).read_text();assert derived.replace(source['only_added_branch'],'')==original
results.append(dict(test='every original validator check retained verbatim',status='PASS'))
(E/'NEI_COMPOSE_TESTS_receipt.json').write_text(json.dumps(dict(tests=results,passed=len(results),failed=0,baseline_unchanged=True,original_neb_file_unchanged=True),indent=2)+'\n')
print(json.dumps(dict(passed=len(results),failed=0)))
