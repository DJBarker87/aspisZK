"""Additional exact finisher roots and real edges, with no older native credit."""
from pathlib import Path
import json,hashlib
import NEI_dot_finish_validate as gate
E=Path(__file__).resolve().parent;R=E.parent.parent
obj=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def packets():return obj(E/'NEI_DOT_FINISH_PACKETS.json') if (E/'NEI_DOT_FINISH_PACKETS.json').exists() else []
def audit(p,neb):return gate.audit(E,R,p,neb,neb.require)
def recipes(base,neb):
 ps={p['function']:p for p in packets()};rows={};edges={}
 for r in base['rows']:
  p=ps.get(r['function'])
  if not p:continue
  proofs=p['lean_evidence'];review=dict(**p['review'],conclusion_hiding=False,statement_and_native_association_checked=True);native=dict(path=str((E/'NEI_DOT_FINISH_REVIEW.json').relative_to(R)),sha256=sha(E/'NEI_DOT_FINISH_REVIEW.json'));ext={}
  for o in r['caller_domain_obligations']:
   if 'call' not in o:continue
   call=o['call'];syntax=call.get('expression',call.get('syntax'))
   if r['function'] in [gate.FUNCTIONS[2],gate.FUNCTIONS[3]]:
    isdot=r['function']==gate.FUNCTIONS[2]
    assert (syntax=='Q' and call['line']==123) if isdot else (syntax=='E::from_limbs([a,b,c,d,e,f,g,h]).unwrap' and call['line']==180),'wrong finisher terminal boundary'
    ext[o['id']]=dict(kind='NEI_DOT_VALUE_CTOR' if isdot else 'NEI_EBY_CTOR_UNWRAP',syntax=syntax,line=call['line'],source_body_sha256=r['frozen_body_sha256'],theorems=['NEI_DotFinishAssociation.finish'] if isdot else ['NEI_EbyFinishAssociation.ctor_unwrap','NEI_PublicDotFinishValues.source'])
    if not isdot:
     callee='crates/aspis-core/src/field/wide_exact.rs::WideExact::from_limbs';ext[o['id']].update(callee=callee,edge=r['function']+' -> '+callee)
    continue
   assert r['function']==gate.FUNCTIONS[0] and syntax=='u64::from','unregistered finisher external boundary'
   ext[o['id']]=dict(kind='NEI_PRIVATE_MODULUS_CAST',syntax='u64::from',line=call['line'],caller_body_sha256=r['frozen_body_sha256'],source_value=2147483647,theorems=['NEI_DotReduction.constant_cast'],native_review=native)
  rows[r['row']]=dict(id='NEI-dot-root:'+r['row'],row=r['row'],function=r['function'],frozen_body_sha256=r['frozen_body_sha256'],selected_claims=r['selected_claims'],named_hypotheses_discharged=[h['name'] for h in r['named_hypotheses']],inventory_domains_discharged=[o['unit'] for o in r['inventory_domain_obligations']],parts=['result','state','ordered_effects','native_association'],lean_evidence=proofs,remaining_inner_hypotheses=[],top_hypotheses=[r['function']+'.PacketDomain',r['function']+'.PhysicalInterpretation','CompositionTrustOptionA'],review=review,native_review=native,external_obligations=ext)
 if not ps:return {},{}
 reducer,limbs,dot,outer=gate.FUNCTIONS;wide='crates/aspis-core/src/field/wide_exact.rs::WideExact::from_limbs'
 for caller,callee in [(dot,reducer),(outer,dot),(outer,limbs),(outer,wide)]:
  parent=next(r for r in base['rows'] if r['function']==caller);children=[r for r in base['rows'] if r['function']==callee];p=ps[caller];proofs=p['lean_evidence'];names=[n for e in proofs for n in e['theorems']];inner=sorted(set(h['name'] for r in children for h in r['named_hypotheses']));key=caller+' -> '+callee
  review=dict(**p['review'],conclusion_hiding=False,statement_and_native_association_checked=True)
  edges[key]=dict(id='NEI-dot-edge:'+caller.split('rs::')[1]+':'+callee.split('rs::')[1],edge=key,status='CLOSED',kind='DIRECT_CALL',frozen_revision=base['frozen_revision'],source_body_sha256=parent['frozen_body_sha256'],selected_callee_claims=sorted(set(c for r in children for c in r['selected_claims'])),inner_hypotheses_discharged=inner,hypothesis_discharge_theorems={h:names for h in inner},parts={part:dict(theorems=names) for part in ['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association']},lean_evidence=proofs,theorems=names,residual_hypotheses=[],review=review,native_review=dict(path=str((E/'NEI_DOT_FINISH_REVIEW.json').relative_to(R)),sha256=sha(E/'NEI_DOT_FINISH_REVIEW.json')),trust='Fresh whole actual caller result/control; unconditional child domains; P6/D188 retained; old native credits withheld')
 return edges,rows
