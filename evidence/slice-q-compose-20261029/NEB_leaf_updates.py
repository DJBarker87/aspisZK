"""Additive, explicitly checked NEA point/line packet refresh over immutable NDT."""
from pathlib import Path
import copy,json,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();obj=lambda p:json.loads(p.read_text())
POINT='crates/aspis-r1-cost-probe/src/fast_domain.rs::fibre_point';LINE='crates/aspis-r1-cost-probe/src/fast_domain.rs::line_node'
PINS={'NEB_GeometryFieldPorts': 'dc372a2ff5db4733f40c095803a51c11f97a8768d8a5102d62fcab857ffe2c51', 'NEB_ActualGeometryPoint': 'e41c9d2fa9274f20aaf6846347f21f003b7b65cc116a14011c54ab77cedf62cc', 'NEB_GeometryDictionaryEq': 'bc976c4b7ee156c86c2893eea1839e7807b6b45ef8e226ee77177a8250b3f357', 'NEB_ActualGeometryLine': 'cd73f50387d4c74d6a09768fd214051c33c0c4db68f9111d4a6043be45734e1e'}
def proof(module,names):
 h=PINS[module];assert sha((E/(module+'.lean')).read_bytes())==h
 found=[]
 for p in E.glob('NEB_L*/receipt.json'):
  d=obj(p)
  if d.get('module')==module and d['exit_status']==0 and d['source_hashes'].get(module+'.lean')==h and all(any(a.startswith("'"+n+"' ") and 'sorryAx' not in a for a in d['print_axioms']) for n in names):found.append(p)
 assert found,(module,names)
 p=sorted(found)[-1];return dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p.read_bytes()),theorems=names)
def recipes():
 # Imported files and each native/extraction/source/graph/lock/control packet
 # were independently revalidated. Check their immutable content address here.
 review=obj(E/'NEB_POINT_REVIEW.json');assert review['revision']=='1e4272618020d800521764b136f052f59ddf8d99' and len(review['native'])==8
 imports=obj(E/'NEB_POINT_IMPORTS.json');assert imports['revision']==review['revision']
 for f in imports['files']:assert sha((R/f['path']).read_bytes())==f['sha256']
 for c in review['native']:assert sha((E/'NEB_IMPORTED_POINT'/c['attempt']/'receipt.json').read_bytes())==c['receipt_sha256']
 ps=[proof('NEB_GeometryFieldPorts',['NEB_GeometryFieldPorts.physical','NEB_GeometryFieldPorts.cm_eq','NEB_GeometryFieldPorts.add','NEB_GeometryFieldPorts.sub','NEB_GeometryFieldPorts.double']),proof('NEB_ActualGeometryPoint',['NEB_ActualGeometryPoint.calls','NEB_ActualGeometryPoint.frame']),proof('NEB_GeometryDictionaryEq',['NEB_GeometryDictionaryEq.point','NEB_GeometryDictionaryEq.line','NEB_GeometryDictionaryEq.point_success','NEB_GeometryDictionaryEq.line_success']),proof('NEB_ActualGeometryLine',['NEB_ActualGeometryLine.calls'])]
 packets=obj(E/'NEB_IMPORTED_POINT/NEA_CLOSED.json');result={}
 for fn,claim in [(POINT,'NEA::fibre_point'),(LINE,'NEA::line_node')]:
  p=next(p for p in packets if p['function']==fn);assert p['claim_id']==claim and p['status']=='CLOSED-CONDITIONAL'
  result[fn]=dict(claim=claim,source_packet_sha256=sha((E/'NEB_IMPORTED_POINT/NEA_CLOSED.json').read_bytes()),domain='u.val < 262144; no nonzero, successful-return, canonical input or output-equality hypothesis',native_control_pairs=['NEA_K017/NEA_K018','NEA_K012/NEA_K013'] if fn==POINT else ['NEA_K029/NEA_K030','NEA_K031/NEA_K032'],model_dictionary='ACTUAL R17CurrentCM31Semantics.operations, matched by checked equality to emitted FIo operations',lean_evidence=ps)
 return result
def apply(baseline):
 out=copy.deepcopy(baseline);updates=recipes();changed=[]
 for r in out['rows']:
  if r['function'] not in updates:continue
  u=updates[r['function']];assert r['bridge_status']=='OPEN' and not r['selected_claims'] and r['composed_status']=='OPEN' and r['frozen_body_verified']
  r.update(bridge_status='CLOSED-CONDITIONAL',selected_claims=[u['claim']],no_credit_reason=None)
  if u['claim'] not in r['claim_ids']:r['claim_ids'].append(u['claim'])
  r['named_hypotheses']=[dict(name=u['claim']+'.PacketDomain',statement=u['domain'],discharged_by=None),dict(name=u['claim']+'.PhysicalInterpretation',statement='Retain only root frozen-source/ABI/static-table/runtime/tool interpretation. Inner field-dictionary law is separately proved for actual R17 operations.',discharged_by=None)]
  r['feature_parity']=[dict(claim=u['claim'],status='explicit deployed-feature association revalidated from imported native packet')]
  r['reviewed_packet_updates'].append(dict(prefix='NEA via NEB',disposition='New local conditional leaf only; composed status still OPEN until all checked call-domain/root gates pass',evidence=['evidence/slice-q-compose-20261029/NEB_POINT_REVIEW.json','evidence/slice-q-compose-20261029/NEB_POINT_IMPORTS.json']))
  changed.append(dict(row=r['row'],function=r['function'],old_local='OPEN',new_local='CLOSED-CONDITIONAL',claim=u['claim']))
 # Keep every original call obligation. Refresh only the selected packet
 # identifiers/qualifications of these two updated callees; never clear status.
 for r in out['rows']:
  for o in r['caller_domain_obligations']:
   if o.get('callee') not in updates:continue
   u=updates[o['callee']];o['callee_claims']=[u['claim']];o['callee_local_status']='CLOSED-CONDITIONAL';o['required_named_hypotheses']=[u['claim']+'.PacketDomain',u['claim']+'.PhysicalInterpretation']
 assert len(changed)==4
 return out,changed

def resolutions(edge):
 if edge['caller'] not in [POINT,LINE]:return edge
 e=copy.deepcopy(edge)
 actual={POINT:{'crates/aspis-core/src/field.rs::CM31::mul','crates/aspis-core/src/r0/domain.rs::FibreIndex::get','crates/aspis-r1-cost-probe/src/fast_domain.rs::table_value'},LINE:{POINT,'crates/aspis-core/src/field.rs::M31::mul','crates/aspis-core/src/field.rs::M31::double','crates/aspis-core/src/field.rs::M31::sub'}}
 e['selected_target']=e['callee'] in actual[e['caller']]
 e['classification']='PURE_TYPED_CALL' if e['selected_target'] else 'CONSERVATIVE_ALTERNATIVE'
 e['static_resolution']='Frozen typed Point<M31>/CM31 operands PLUS actual native opaque-call logs; actual R17 full-Result call witness'
 return e
