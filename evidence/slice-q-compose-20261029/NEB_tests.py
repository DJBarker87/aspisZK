#!/usr/bin/env python3
"""Mutate actual certificates; no fabricated proof, source or receipt writes."""
from pathlib import Path
import copy,json,sys
sys.dont_write_bytecode=True
import NEB_validate as v
E=Path(__file__).resolve().parent
base=v.obj(v.N/'NDT_LEDGER.json');edges=v.obj(E/'NEB_EDGES.json');results=[]
TARGET='crates/aspis-core/src/field.rs::M31::reduce_u64 -> crates/aspis-core/src/field.rs::reduce_u64'
WRAPPERS={'TX1:020','TX2:014'}
def test(name,fn):
 fn();results.append(dict(test=name,result='PASS'))
def reject(fn):
 try:fn()
 except (AssertionError,ValueError,KeyError,OSError):return
 raise AssertionError('mutation admitted')
def affected_open(change):
 mutated=copy.deepcopy(edges);edge=next(e for e in mutated['edges'] if e['edge']==TARGET);change(edge)
 out,delta=v.extend(base,mutated)
 assert all(r['composed_status']=='OPEN' for r in out['rows'] if r['row'] in WRAPPERS)
 assert not(WRAPPERS & set(delta['composed_rows_closed'])) and delta['edge_closed']==106
 assert all(x==['OPEN'] for x in delta['roots'].values())
test('unchanged original NDT invariants',lambda:v.ndt.validate_invariants(base))
out,delta=v.extend(base,edges)
assert delta['closed_count']==62 and delta['edge_closed']==107
results.append(dict(test='registered reducer and additive certificates close 60 occurrence rows bottom-up',result='PASS'))
test('missing certificate keeps both actual callers OPEN',lambda:affected_open(lambda e:e.update(certificate=None)))
test('wrong edge identity keeps actual callers OPEN',lambda:affected_open(lambda e:e['certificate'].update(edge=TARGET+' wrong')))
test('wrong frozen revision keeps actual callers OPEN',lambda:affected_open(lambda e:e['certificate'].update(frozen_revision='0'*40)))
test('wrong caller body keeps actual callers OPEN',lambda:affected_open(lambda e:e['certificate'].update(source_body_sha256='0'*64)))
test('wrong selected callee packet keeps actual callers OPEN',lambda:affected_open(lambda e:e['certificate'].update(selected_callee_claims=[])))
test('missing inner physical hypothesis discharge keeps callers OPEN',lambda:affected_open(lambda e:e['certificate']['inner_hypotheses_discharged'].pop()))
test('missing state/effect association keeps callers OPEN',lambda:affected_open(lambda e:e['certificate']['parts'].pop('state_ordered_effects')))
test('wrong but audited theorem in PacketDomain slot is rejected by the concrete recipe',lambda:affected_open(lambda e:e['certificate']['parts']['packet_domain'].update(theorems=['NEB_ReducerCall.reference'])))
test('forged Lean receipt hash keeps actual callers OPEN',lambda:affected_open(lambda e:e['certificate']['lean_evidence'][0].update(receipt_sha256='0'*64)))
test('retained inner hypothesis keeps actual callers OPEN',lambda:affected_open(lambda e:e['certificate'].update(residual_hypotheses=['callee law'])))
missing=copy.deepcopy(edges);missing['edges'].pop()
test('missing slice edge is rejected',lambda:reject(lambda:v.extend(base,missing)))
dup=copy.deepcopy(edges);dup['edges'].append(dup['edges'][0])
test('duplicate slice edge is rejected',lambda:reject(lambda:v.extend(base,dup)))
bad=copy.deepcopy(edges);bad['row_certificates'][0]['top_hypotheses'].append('unapproved assumption')
test('extra root assumption is rejected',lambda:reject(lambda:v.extend(base,bad)))
bad=copy.deepcopy(edges);bad['row_certificates'][0]['external_obligations']={}
test('missing constructor classification is rejected',lambda:reject(lambda:v.extend(base,bad)))
bad=copy.deepcopy(edges);bad['row_certificates']=[r for r in bad['row_certificates'] if r['row']!='TX1:045']
def missing_leaf():
 changed,delta=v.extend(base,bad)
 assert all(r['composed_status']=='OPEN' for r in changed['rows'] if r['row'] in WRAPPERS)
test('missing lower composed row blocks both caller rows',missing_leaf)
changed=copy.deepcopy(base);changed['rows'][0]['composed_status']='CLOSED'
test('forged baseline CLOSED status rejected by original NDT invariants',lambda:reject(lambda:v.extend(changed,edges)))
# New additive certificates add checks without weakening the reducer mutations.
CM_ADD='crates/aspis-core/src/field.rs::CM31::add'
CM_ROWS={r['row'] for r in base['rows'] if r['function']==CM_ADD}
def additive_open(change):
 m=copy.deepcopy(edges);change(m);o,_=v.extend(base,m)
 assert all(r['composed_status']=='OPEN' for r in o['rows'] if r['row'] in CM_ROWS)
test('missing actual CM31 to M31 call-domain certificate blocks both CM31 occurrences',lambda:additive_open(lambda m:next(e for e in m['edges'] if e['caller']==CM_ADD and e['selected_target']) .update(certificate=None)))
test('missing conservative alternative certificate blocks parent',lambda:additive_open(lambda m:next(e for e in m['edges'] if e['caller']==CM_ADD and not e['selected_target']) .update(certificate=None)))
test('missing original inventory self-target certificate blocks parent',lambda:additive_open(lambda m:next(e for e in m['inventory_edges'] if e['caller']==CM_ADD).update(certificate=None)))
test('omitted self-target is never pruned implicitly',lambda:additive_open(lambda m:m.update(inventory_edges=[e for e in m['inventory_edges'] if e['caller']!=CM_ADD])))
test('wrong but audited additive field-domain theorem blocks parent',lambda:additive_open(lambda m:next(e for e in m['edges'] if e['caller']==CM_ADD and e['selected_target'])['certificate']['parts']['packet_domain'].update(theorems=['NEB_AdditiveFrames.cm_add'])))
bad=copy.deepcopy(edges);r=next(r for r in bad['row_certificates'] if r['row']=='TX2:009');next(vv for vv in r['external_obligations'].values() if vv['kind']=='RELEASE_CFG_INACTIVE')['selected_core_features'].append('r0-r91-audit')
test('wrong inactive cfg feature projection rejects promotion',lambda:reject(lambda:v.extend(base,bad)))
bad=copy.deepcopy(edges);next(r for r in bad['row_certificates'] if r['function']==CM_ADD)['lean_evidence'].pop()
test('omitting full-record injectivity evidence rejects promotion',lambda:reject(lambda:v.extend(base,bad)))
bad=copy.deepcopy(edges);bad['inventory_edges'].append(copy.deepcopy(bad['inventory_edges'][0]))
test('duplicate extra original inventory edge rejects promotion',lambda:reject(lambda:v.extend(base,bad)))
bad=copy.deepcopy(edges);bad['inventory_edges'][0]['selected_target']=True
test('self-cycle cannot be relabelled as an active proved call',lambda:reject(lambda:v.extend(base,bad)))
CANON='crates/aspis-core/src/field/wide_exact.rs::canonical_qm31'
EMBED='crates/aspis-core/src/field/wide_exact.rs::WideExact::from_qm31'
EMBED_ROWS={r['row'] for r in base['rows'] if r['function']==EMBED}
def embedding_open(change):
 m=copy.deepcopy(edges);change(m);o,_=v.extend(base,m)
 assert all(r['composed_status']=='OPEN' for r in o['rows'] if r['row'] in EMBED_ROWS)
test('missing canonical-embedding edge keeps both callers OPEN',lambda:embedding_open(lambda m:next(e for e in m['edges'] if e['caller']==EMBED).update(certificate=None)))
test('missing inner canonical helper physical discharge keeps embedding OPEN',lambda:embedding_open(lambda m:next(e for e in m['edges'] if e['caller']==EMBED)['certificate']['inner_hypotheses_discharged'].pop()))
test('missing lower canonical occurrence blocks both embedding rows',lambda:embedding_open(lambda m:m.update(row_certificates=[r for r in m['row_certificates'] if r['row']!='TX1:060'])))
bad=copy.deepcopy(edges);r=next(r for r in bad['row_certificates'] if r['function']==CANON);r['external_obligations'].pop(next(k for k,c in r['external_obligations'].items() if c['kind']=='BUNDLED_PURE_REMAINDER_CLOSURE'))
test('omitted bundled closure occurrence rejects promotion',lambda:reject(lambda:v.extend(base,bad)))
bad=copy.deepcopy(edges);r=next(r for r in bad['row_certificates'] if r['function']==CANON);next(c for c in r['external_obligations'].values() if c['kind']=='BUNDLED_PURE_REMAINDER_CLOSURE')['line']+=1
test('wrong bundled closure occurrence line rejects promotion',lambda:reject(lambda:v.extend(base,bad)))
bad=copy.deepcopy(edges);r=next(r for r in bad['row_certificates'] if r['function'].endswith('::WideExact::to_limbs'));r['lean_evidence'][0]['theorems'].remove('NEB_RepresentationRefs.e_injective')
test('missing complete eight-field carrier injection rejects promotion',lambda:reject(lambda:v.extend(base,bad)))
MUL='crates/aspis-core/src/field.rs::M31::mul'
MUL_ROWS={r['row'] for r in base['rows'] if r['function']==MUL}
def mul_open(change):
 m=copy.deepcopy(edges);change(m);o,_=v.extend(base,m)
 assert all(r['composed_status']=='OPEN' for r in o['rows'] if r['row'] in MUL_ROWS)
test('missing actual product-to-reducer edge blocks raw multiplication',lambda:mul_open(lambda m:next(e for e in m['edges'] if e['caller']==MUL).update(certificate=None)))
test('wrong audited result theorem cannot replace exact native call association',lambda:mul_open(lambda m:next(e for e in m['edges'] if e['caller']==MUL)['certificate']['parts']['native_callsite_association'].update(theorems=['NEB_MulReducerCall.value'])))
bad=copy.deepcopy(edges);r=next(r for r in bad['row_certificates'] if any(c['kind']=='LOSSLESS_U32_TO_U64' for c in r['external_obligations'].values()));next(c for c in r['external_obligations'].values() if c['kind']=='LOSSLESS_U32_TO_U64')['line']+=1
test('wrong scalar conversion occurrence rejects promotion',lambda:reject(lambda:v.extend(base,bad)))
bad=copy.deepcopy(edges);r=next(r for r in bad['row_certificates'] if r['function']==MUL);r['lean_evidence'].pop()
test('omitted checked-versus-wrapping product witness rejects promotion',lambda:reject(lambda:v.extend(base,bad)))
TABLE='crates/aspis-r1-cost-probe/src/fast_domain.rs::table_value'
TABLE_ROWS={r['row'] for r in base['rows'] if r['function']==TABLE}
def table_open(change):
 m=copy.deepcopy(edges);change(m);o,_=v.extend(base,m)
 assert all(r['composed_status']=='OPEN' for r in o['rows'] if r['row'] in TABLE_ROWS)
test('missing constructor interpretation certificate blocks table values',lambda:table_open(lambda m:next(e for e in m['edges'] if e['caller']==TABLE).update(certificate=None)))
test('constructor context cannot retain inner interpretation as a hidden premise',lambda:table_open(lambda m:next(e for e in m['edges'] if e['caller']==TABLE)['certificate'].update(residual_hypotheses=['constructor interpretation'])))
def altered_scope():
 original=v.obj
 def override(path):
  d=original(path)
  if path==E/'NEB_SCOPE.json':d=copy.deepcopy(d);d['slice']['roots']=[]
  return d
 v.obj=override
 try:reject(lambda:v.extend(base,edges))
 finally:v.obj=original
test('root membership must match authoritative slice manifest',altered_scope)
POINT='crates/aspis-r1-cost-probe/src/fast_domain.rs::fibre_point'
POINT_ROWS={r['row'] for r in base['rows'] if r['function']==POINT}
def point_open(change):
 m=copy.deepcopy(edges);change(m);o,_=v.extend(base,m)
 assert all(r['composed_status']=='OPEN' for r in o['rows'] if r['row'] in POINT_ROWS)
test('missing actual native point product use certificate blocks closure',lambda:point_open(lambda m:next(e for e in m['edges'] if e['caller']==POINT and e['callee'].endswith('::CM31::mul')).update(certificate=None)))
test('missing conservative point product alternative certificate blocks closure',lambda:point_open(lambda m:next(e for e in m['edges'] if e['caller']==POINT and not e['selected_target']).update(certificate=None)))
bad=copy.deepcopy(edges);next(e for e in bad['edges'] if e['callee']==POINT)['required_named_hypotheses']=[]
test('new packet qualifiers cannot be omitted at a caller',lambda:reject(lambda:v.extend(base,bad)))
bad=copy.deepcopy(edges);next(e for e in bad['edges'] if e['caller']==POINT and not e['selected_target'])['selected_target']=True
test('wrong native point receiver resolution rejects promotion',lambda:reject(lambda:v.extend(base,bad)))
bad=copy.deepcopy(edges);r=next(r for r in bad['row_certificates'] if r['function']==POINT);r['lean_evidence']=[p for p in r['lean_evidence'] if not any(n=='NEB_GeometryFieldPorts.physical' for n in p['theorems'])]
test('missing actual R17 dictionary instance rejects promotion',lambda:reject(lambda:v.extend(base,bad)))
SQUARE='crates/aspis-core/src/field.rs::square_n'
def square_open(change):
 m=copy.deepcopy(edges);change(m);o,_=v.extend(base,m)
 assert all(r['composed_status']=='OPEN' for r in o['rows'] if r['function']==SQUARE)
test('missing raw square cell domain blocks loop closure',lambda:square_open(lambda m:next(e for e in m['edges'] if e['caller']==SQUARE and e['selected_target']).update(certificate=None)))
test('wrong square trace-frame role blocks loop closure',lambda:square_open(lambda m:next(e for e in m['edges'] if e['caller']==SQUARE and e['selected_target'])['certificate']['parts']['native_callsite_association'].update(theorems=['NEB_SquareComposition.cell'])))
test('omitted scalar-loop conservative alternative blocks loop closure',lambda:square_open(lambda m:next(e for e in m['edges'] if e['caller']==SQUARE and not e['selected_target']).update(certificate=None)))
assert base==v.obj(v.N/'NDT_LEDGER.json');results.append(dict(test='authoritative ledger unchanged',result='PASS'))
print(json.dumps(dict(results=results,tests=len(results),composed_closed=delta['closed_count'],slice_roots_closed=0,synthetic_evidence_credit=0),indent=1))
