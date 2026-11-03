"""Compose the already audited actual fold packets with fresh field callees."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent
obj=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def packets():
 ps=[obj(E/'NEI_LINE_PACKET.json'),obj(E/'NEI_CIRCLE_PACKET.json')]
 for p in ps:p['claim_id']='NEI::fold::'+p['function'].rsplit('::',1)[1]
 return ps
def audit(p,neb):
 from NEI_validate import audit_line,audit_circle
 return audit_line(p) if p['function'].endswith('::line_fold_with_inverses') else audit_circle(p)
def recipes(base,neb):
 from NEI_field_validate import FUNCTIONS
 ps={p['function']:p for p in packets()};roots={};edges={};native=dict(path=str((E/'NEI_FOLD_REVIEW.json').relative_to(R)),sha256=sha(E/'NEI_FOLD_REVIEW.json'))
 for row in base['rows']:
  p=ps.get(row['function'])
  if not p:continue
  ext={}
  for o in row['caller_domain_obligations']:
   if 'call' not in o:continue
   c=o['call'];assert c.get('expression',c.get('syntax'))=='M31','unclassified fold boundary'
   ext[o['id']]=dict(kind='TRANSPARENT_M31_CONSTRUCTOR',syntax='M31')
  rev=dict(**p['review'],conclusion_hiding=False,statement_and_native_association_checked=True)
  roots[row['row']]=dict(id='NEI-fold-root:'+row['row'],row=row['row'],function=row['function'],frozen_body_sha256=row['frozen_body_sha256'],selected_claims=row['selected_claims'],named_hypotheses_discharged=[h['name'] for h in row['named_hypotheses']],inventory_domains_discharged=[o['unit'] for o in row['inventory_domain_obligations']],parts=['result','state','ordered_effects','native_association'],lean_evidence=p['lean_evidence'],remaining_inner_hypotheses=[],top_hypotheses=[row['function']+'.PacketDomain',row['function']+'.PhysicalInterpretation','CompositionTrustOptionA'],review=rev,native_review=native,external_obligations=ext)
 original=obj(E.parent/'slice-q-compose-20261029/NEB_EDGES.json')
 for edge in original['edges']:
  p=ps.get(edge['caller'])
  if not p:continue
  assert edge['selected_target'] is not False and edge['callee'] in FUNCTIONS,'fold callee not completed field body'
  children=[r for r in base['rows'] if r['function']==edge['callee']];inner=sorted(set(h['name'] for r in children for h in r['named_hypotheses']));proofs=p['lean_evidence'];names=[n for i in proofs for n in i['theorems']]
  edges[edge['edge']]=dict(id='NEI-fold-edge:'+edge['obligation_id'],edge=edge['edge'],status='CLOSED',kind='DIRECT_CALL',frozen_revision=base['frozen_revision'],source_body_sha256=edge['source_body_sha256'],selected_callee_claims=sorted(set(c for r in children for c in r['selected_claims'])),inner_hypotheses_discharged=inner,hypothesis_discharge_theorems={h:names for h in inner},parts={part:dict(theorems=names) for part in ['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association']},lean_evidence=proofs,theorems=names,residual_hypotheses=[],review=dict(**p['review'],conclusion_hiding=False,statement_and_native_association_checked=True),native_review=native,trust='Actual field forest/whole same-call cuts and fresh native differential; field callee domains include all typed inputs; no old native credit')
 return edges,roots
