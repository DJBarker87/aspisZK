from pathlib import Path
import json,hashlib
from NEB_leaf_updates import POINT,LINE,recipes,resolutions
E=Path(__file__).resolve().parent;R=E.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();obj=lambda p:json.loads(p.read_text())
def expected(base):
 packets=recipes();review=E/'NEB_IMPORTED_LEAF_ASSOCIATION.md';rev=dict(path=str(review.relative_to(R)),sha256=sha(review.read_bytes()),conclusion_hiding=False,statement_and_native_association_checked=True);native=E/'NEB_POINT_REVIEW.json';nr=dict(path=str(native.relative_to(R)),sha256=sha(native.read_bytes()));edges={};rows={}
 for fn in [POINT,LINE]:
  u=packets[fn];ps=u['lean_evidence'];names=[n for p in ps for n in p['theorems']];source=next(r for r in base['rows'] if r['function']==fn);assert source['selected_claims']==[u['claim']] and source['bridge_status']=='CLOSED-CONDITIONAL'
  domains=['NEB_ActualGeometryPoint.calls','NEB_GeometryFieldPorts.physical','NEB_GeometryFieldPorts.cm_eq'] if fn==POINT else ['NEB_ActualGeometryLine.calls','NEB_GeometryFieldPorts.add','NEB_GeometryFieldPorts.sub','NEB_GeometryFieldPorts.double']
  frame='NEB_ActualGeometryPoint.frame' if fn==POINT else 'NEB_ActualGeometryLine.calls'
  for edge in obj(E/'NEB_EDGES.json')['edges']:
   if edge['caller']!=fn:continue
   e=resolutions(edge);children=[r for r in base['rows'] if r['function']==e['callee']];inner=sorted(set(h['name'] for r in children for h in r['named_hypotheses']));claims=sorted(set(c for r in children for c in r['selected_claims']))
   edges[e['edge']]=dict(id='NEB-imported-leaf-edge:'+e['obligation_id'],edge=e['edge'],status='CLOSED',kind='DIRECT_CALL' if e['selected_target'] else 'STATIC_UNREACHABLE',frozen_revision=base['frozen_revision'],source_body_sha256=source['frozen_body_sha256'],selected_callee_claims=claims,inner_hypotheses_discharged=inner,hypothesis_discharge_theorems={n:domains+[frame] for n in inner},parts={part:dict(theorems=domains+[frame]) for part in ['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association']},lean_evidence=ps,theorems=names,residual_hypotheses=[],review=rev,native_review=nr,trust='NativeContractSemanticTransport: actual-cohort dictionary instance; reclassification, never removal')
  for r in base['rows']:
   if r['function']!=fn:continue
   assert not any('call' in o for o in r['caller_domain_obligations'])
   rows[r['row']]=dict(id='NEB-imported-leaf-root:'+r['row'],row=r['row'],function=fn,frozen_body_sha256=r['frozen_body_sha256'],selected_claims=r['selected_claims'],named_hypotheses_discharged=[h['name'] for h in r['named_hypotheses']],inventory_domains_discharged=[o['unit'] for o in r['inventory_domain_obligations']],parts=['result','state','ordered_effects','native_association'],lean_evidence=ps,remaining_inner_hypotheses=[],top_hypotheses=[fn+'.PacketDomain',fn+'.PhysicalInterpretation','NativeContractSemanticTransport'],review=rev,native_review=nr,external_obligations={})
 return edges,rows
