"""Additional same-call row/getter/push certificates, never old native credit."""
from pathlib import Path
import json,hashlib,copy
import NEI_getter_validate,NEI_row_validate,NEI_push_validate,NEI_wide_ctor_validate
WIDE=NEI_wide_ctor_validate.FUNCTION
from NEI_validate import function
E=Path(__file__).resolve().parent;R=E.parent.parent
obj=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
V='crates/aspis-r1-cost-probe/src/verifier.rs::'
ROW=V+'update_residue_row';PUSH=V+'BatchedWeights::push';GETTERS=[V+'power_limb_at',V+'residue_limb_at']
def packets():
 ps=obj(E/'NEI_GETTER_PACKETS.json')
 for name in ['ROW','PUSH']:
  p=obj(E/('NEI_'+name+'_PACKET.json'));p['claim_id']='NEI::'+p['function'].split('::')[-1];ps.append(p)
 if (E/'NEI_WIDE_CTOR_PACKET.json').exists():ps.append(obj(E/'NEI_WIDE_CTOR_PACKET.json'))
 return ps

def audit(p,neb):
 if p['function']==WIDE:return NEI_wide_ctor_validate.audit(E,R,p,neb,neb.require)
 if p['route']=='D188_ACTUAL_GETTER_FRAME':return NEI_getter_validate.audit(E,R,p,neb,neb.require)
 if p['function']==ROW:return NEI_row_validate.audit(E,R,p,neb,neb.require,function)
 if p['function']==PUSH:return NEI_push_validate.audit(E,R,p,neb,neb.require,function)
 raise AssertionError('unregistered arithmetic packet')

def proof():
 r=E/'NEI_L069/receipt.json';return dict(receipt=str(r.relative_to(R)),receipt_sha256=sha(r),theorems=['NEI_RowEdges.'+n for n in ['residue','power','index_domain','widen']])

def recipes(base,neb):
 ps={p['function']:p for p in packets()};rows={};edges={}
 for r in base['rows']:
  if r['function'] not in ps:continue
  p=ps[r['function']];lean=p['lean_evidence']+([] if r['function']==WIDE else [proof()])
  review=dict(**p['review'],conclusion_hiding=False,statement_and_native_association_checked=True)
  external={}
  for o in r['caller_domain_obligations']:
   if 'call' not in o:continue
   syntax=o['call'].get('expression',o['call'].get('syntax'))
   if r['function']==WIDE:
    assert syntax in ['Some','M31'],'unregistered wide constructor operation'
    external[o['id']]=dict(kind='NEI_WIDE_OPTION_CONSTRUCTOR' if syntax=='Some' else 'TRANSPARENT_M31_CONSTRUCTOR',source_body_sha256=r['frozen_body_sha256'],syntax=syntax,line=o['call']['line'],theorems=['NEI_WideCtorAssociation.same_result'])
    continue
   assert r['function']==ROW and syntax=='u64::from' and o['call']['line']==240,'unregistered row external operation'
   external[o['id']]=dict(kind='NEI_ROW_U32_U64_WIDEN',source_body_sha256=r['frozen_body_sha256'],syntax='u64::from',line=240,theorems=['NEI_RowEdges.widen'])
  rows[r['row']]=dict(id='NEI-arithmetic-root:'+r['row'],row=r['row'],function=r['function'],frozen_body_sha256=r['frozen_body_sha256'],selected_claims=r['selected_claims'],named_hypotheses_discharged=[h['name'] for h in r['named_hypotheses']],inventory_domains_discharged=[o['unit'] for o in r['inventory_domain_obligations']],parts=['result','state','ordered_effects','native_association'],lean_evidence=lean,remaining_inner_hypotheses=[],top_hypotheses=[r['function']+'.PacketDomain',r['function']+'.PhysicalInterpretation','CompositionTrustOptionA'],review=review,native_review=dict(path=str((E/'NEI_ARITHMETIC_REVIEW.json').relative_to(R)),sha256=sha(E/'NEI_ARITHMETIC_REVIEW.json')),external_obligations=external)
 for caller,callee in [(ROW,g) for g in GETTERS]+[(PUSH,ROW)]:
  parent=next(r for r in base['rows'] if r['function']==caller);children=[r for r in base['rows'] if r['function']==callee]
  p=ps[caller];lean=p['lean_evidence']+[proof()];names=[n for item in lean for n in item['theorems']];inner=sorted(set(h['name'] for r in children for h in r['named_hypotheses']));edge=caller+' -> '+callee
  edges[edge]=dict(id='NEI-arithmetic-edge:'+caller.rsplit('::',1)[1]+':'+callee.rsplit('::',1)[1],edge=edge,status='CLOSED',kind='DIRECT_CALL',frozen_revision=base['frozen_revision'],source_body_sha256=parent['frozen_body_sha256'],selected_callee_claims=sorted(set(c for r in children for c in r['selected_claims'])),inner_hypotheses_discharged=inner,hypothesis_discharge_theorems={n:names for n in inner},parts={part:dict(theorems=names) for part in ['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association']},lean_evidence=lean,theorems=names,residual_hypotheses=[],review=dict(**p['review'],conclusion_hiding=False,statement_and_native_association_checked=True),native_review=dict(path=str((E/'NEI_ARITHMETIC_REVIEW.json').relative_to(R)),sha256=sha(E/'NEI_ARITHMETIC_REVIEW.json')),trust='P6/D188 retained; exact native/read/borrow contexts; no old native credit')
 return edges,rows

def check_widen(row,o,ext,rc):
 assert row['function']==ROW,'widen belongs to a different parent'
 assert o['call'].get('expression',o['call'].get('syntax'))=='u64::from' and o['call']['line']==240,'wrong native conversion occurrence'
 assert ext['syntax']=='u64::from' and ext['line']==240 and ext['source_body_sha256']==row['frozen_body_sha256'],'conversion source binding'
 assert ext['theorems']==['NEI_RowEdges.widen'] and any(ext['theorems'][0] in p['theorems'] for p in rc['lean_evidence']),'widen law unaudited'
 frozen=obj(E/'NEI_FROZEN.json')['crates/aspis-r1-cost-probe/src/verifier.rs'];assert frozen.splitlines()[239].count('u64::from')==2,'native source conversion changed'
