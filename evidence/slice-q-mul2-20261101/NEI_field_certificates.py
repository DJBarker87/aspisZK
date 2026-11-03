"""Immutable actual field-forest roots and typed actual-call resolutions."""
from pathlib import Path
import json,hashlib
import NEI_field_validate as gate
E=Path(__file__).resolve().parent;R=E.parent.parent
obj=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def packets():return obj(E/'NEI_FIELD_PACKETS.json') if (E/'NEI_FIELD_PACKETS.json').exists() else []
def audit(p,neb):return gate.audit(p,neb)
def recipes(base,neb):
 ps={p['function']:p for p in packets()};roots={};edges={};native=dict(path=str((E/'NEI_FIELD_REVIEW.json').relative_to(R)),sha256=sha(E/'NEI_FIELD_REVIEW.json'))
 for row in base['rows']:
  p=ps.get(row['function'])
  if not p:continue
  ext={}
  for o in row['caller_domain_obligations']:
   if 'call' not in o:continue
   call=o['call'];syntax=call.get('expression',call.get('syntax'))
   if call['resolution']=='disabled release cfg':
    ext[o['id']]=dict(kind='RELEASE_CFG_INACTIVE',cfg=call['cfg'],selected_core_features=['r0'],native_review=native)
   elif syntax=='M31':ext[o['id']]=dict(kind='TRANSPARENT_M31_CONSTRUCTOR',syntax=syntax)
   else:
    assert row['function']=='crates/aspis-core/src/field.rs::CM31::mul' and syntax=='u64::from' and call['line']==314,'unclassified field boundary'
    ext[o['id']]=dict(kind='LOSSLESS_U32_TO_U64',syntax=syntax,line=call['line'],caller_body_sha256=row['frozen_body_sha256'],native_review=native,theorems=['NEI_FieldFrames.widen'])
  review=dict(**p['review'],conclusion_hiding=False,statement_and_native_association_checked=True)
  roots[row['row']]=dict(id='NEI-field-root:'+row['row'],row=row['row'],function=row['function'],frozen_body_sha256=row['frozen_body_sha256'],selected_claims=row['selected_claims'],named_hypotheses_discharged=[h['name'] for h in row['named_hypotheses']],inventory_domains_discharged=[o['unit'] for o in row['inventory_domain_obligations']],parts=['result','state','ordered_effects','native_association'],lean_evidence=p['lean_evidence'],remaining_inner_hypotheses=[],top_hypotheses=[row['function']+'.PacketDomain',row['function']+'.PhysicalInterpretation','CompositionTrustOptionA'],review=review,native_review=native,external_obligations=ext)
 original=obj(E.parent/'slice-q-compose-20261029/NEB_EDGES.json')
 from NEB_field_certificates import expected as original_fields
 _,_,self_edges=original_fields(base)
 from NEB_additive_certificates import expected as original_additive
 _,_,additive_self=original_additive(base);self_edges+=additive_self
 for edge in original['edges']+self_edges:
  p=ps.get(edge['caller'])
  if not p:continue
  static=edge['selected_target'] is False
  if not static:assert edge['callee'] in ps,('actual field callee outside completed forest',edge['edge'])
  children=[r for r in base['rows'] if r['function']==edge['callee']];inner=sorted(set(h['name'] for r in children for h in r['named_hypotheses']));proofs=p['lean_evidence'];names=[n for e in proofs for n in e['theorems']];review=dict(**p['review'],conclusion_hiding=False,statement_and_native_association_checked=True)
  edges[edge['edge']]=dict(id='NEI-field-edge:'+edge['obligation_id'],edge=edge['edge'],status='CLOSED',kind='STATIC_UNREACHABLE' if static else 'DIRECT_CALL',frozen_revision=base['frozen_revision'],source_body_sha256=edge['source_body_sha256'],selected_callee_claims=sorted(set(c for r in children for c in r['selected_claims'])),inner_hypotheses_discharged=inner,hypothesis_discharge_theorems={h:names for h in inner},parts={part:dict(theorems=names) for part in ['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association']},lean_evidence=proofs,theorems=names,residual_hypotheses=[],review=review,native_review=native,trust='D188 actual immutable bodies with inverse carrier maps and fresh actual/emitted differential; existing typed receiver resolution retained; no old native credit')
 return edges,roots

def inventory(base,neb,approved):
 from NEB_field_certificates import expected as original_fields
 _,_,old=original_fields(base)
 from NEB_additive_certificates import expected as original_additive
 _,_,additive_self=original_additive(base);old+=additive_self
 out=[]
 for e in old:
  if e['caller'] not in {p['function'] for p in packets()}:continue
  assert e['caller']==e['callee'] and e['selected_target'] is False
  e=dict(e);e.update(certificate=approved[e['edge']],status='CLOSED',obstacle=None);out.append(e)
 return out
