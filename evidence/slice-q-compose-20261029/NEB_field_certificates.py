"""Compose only explicitly adopted field packets plus fresh exact call witnesses."""
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();obj=lambda p:json.loads(p.read_text())
PINS={'NEB_MulReducerCall': '5dc0752caa64b51b0ec9872030e3e381805b13ea80dafe6e46bd9bc7c2a35386', 'NEB_CMCalls': 'a6b82ced2512c3c026bb800bcbd3788585aa034f0d21622ab0446801fe6b737c', 'NEB_QMCalls': 'd75da4354ed1478e0cb4cc090a05789fe8a64d7e146dad6e1aa4de140733e459', 'NEB_AdditiveCalls': '72302cda5b38b2879d070c12667df9f166124eaaba7891135b293d72d929df2b', 'NEB_ByRCalls': 'e221da3ae1a9b867257ed8a5e6764d51d951da8ad2820de5adf599c87f6553d9', 'NEB_WideCalls': 'cb0cf637d42f390b55fc02d4a38994e2d8fe724d0ace51db5ad7f99968bdbba0', 'NEB_FieldFrames': 'e7f43d24e3f53614250e00b5a06411da1565d2b1a4bc2bee48979905e3fb9472', 'NEB_NativeFieldScalars': '244ee72e968e65762f64cf0a43bc4ea26330f7fd2ba1360219c5aa1327d3363c', 'NEB_CMCarrier': 'fbc1855599d9eb378eedfb3751159414c55e750e11677eb5549e3107316e0e32'}
def proof(module,names):
 h=PINS[module];assert sha((E/(module+'.lean')).read_bytes())==h
 found=[]
 for p in E.glob('NEB_L*/receipt.json'):
  d=obj(p)
  if d.get('module')==module and d['exit_status']==0 and d['source_hashes'].get(module+'.lean')==h and all(any(a.startswith("'"+n+"' ") and 'sorryAx' not in a for a in d['print_axioms']) for n in names):found.append(p)
 assert found,(module,names)
 p=sorted(found)[-1];return dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p.read_bytes()),theorems=names)
def expected(base):
 subprocess.run(['python3',str(E/'NEB_field_transport_validate.py'),'--check'],check=True,stdout=subprocess.DEVNULL)
 field='crates/aspis-core/src/field.rs::';wide='crates/aspis-core/src/field/wide_exact.rs::'
 defs={field+'M31::mul':('NEB_MulReducerCall',['domain','input_value','callsite','value','state_effects'],'NEB_MulReducerCall','state_effects'),field+'CM31::mul':('NEB_CMCalls',['multiply'],'NEB_FieldFrames','cm_mul'),field+'CM31::mul_m31':('NEB_CMCalls',['scale'],'NEB_FieldFrames','cm_scale'),field+'QM31::mul':('NEB_QMCalls',['multiply'],'NEB_FieldFrames','qm_mul'),field+'QM31::mul_m31':('NEB_AdditiveCalls',['qm_scale'],'NEB_FieldFrames','qm_scale'),field+'mul_by_r':('NEB_ByRCalls',['source'],'NEB_FieldFrames','by_r'),wide+'mul_u':('NEB_ByRCalls',['mul_u'],'NEB_FieldFrames','mul_u'),wide+'WideExact::mul':('NEB_WideCalls',['multiply'],'NEB_FieldFrames','wide_mul'),wide+'WideExact::mul_m31':('NEB_WideCalls',['scale'],'NEB_FieldFrames','wide_scale'),wide+'WideExact::mul_qm31':('NEB_WideCalls',['mixed'],'NEB_FieldFrames','wide_mixed')}
 review=E/'NEB_FIELD_ASSOCIATION.md';rev=dict(path=str(review.relative_to(R)),sha256=sha(review.read_bytes()),conclusion_hiding=False,statement_and_native_association_checked=True);native=E/'NEB_FIELD_TRANSPORT_REVIEW.json';nr=dict(path=str(native.relative_to(R)),sha256=sha(native.read_bytes()));edges={};rows={};extras=[];current=obj(E/'NEB_EDGES.json')['edges']
 for fn,(callmod,callnames,framemod,frame) in defs.items():
  source=next(r for r in base['rows'] if r['function']==fn)
  assert source['bridge_status']=='CLOSED-CONDITIONAL' and source['selected_claims']
  full=framemod+'.'+frame;domains=[callmod+'.'+n for n in callnames]
  ps=[proof(callmod,domains)]
  if framemod!=callmod:ps.append(proof(framemod,[full]))
  if fn==field+'M31::mul':ps.append(proof('NEB_NativeFieldScalars',['NEB_NativeFieldScalars.m31_checked_product']))
  if fn==field+'CM31::mul':
   ps.extend([proof('NEB_NativeFieldScalars',['NEB_NativeFieldScalars.sum_checked','NEB_NativeFieldScalars.cross_checked']),proof('NEB_CMCarrier',['NEB_CMCarrier.lossless','NEB_CMCarrier.actual_casts'])])
  names=[n for p in ps for n in p['theorems']];selected=[e for e in current if e['caller']==fn]
  for o in source['caller_domain_obligations']:
   if o.get('callee')==fn:
    assert not any(e['obligation_id']==o['id'] for e in selected)
    e=dict(edge=fn+' -> '+fn,caller=fn,callee=fn,obligation_id=o['id'],status='OPEN',classification='CONSERVATIVE_ALTERNATIVE',source_body_sha256=source['frozen_body_sha256'],static_resolution='Fixed typed nonrecursive adopted emitted field body; original self-target retained',selected_target=False,model_domain_theorems=[],certificate=None,required_named_hypotheses=o['required_named_hypotheses'],callee_packet_domains=[],actual_inventory_calls=[],obstacle='Explicit conservative self-target certificate required')
    selected.append(e);extras.append(e)
  for e in selected:
   children=[r for r in base['rows'] if r['function']==e['callee']];claims=sorted(set(c for r in children for c in r['selected_claims']));inner=sorted(set(h['name'] for r in children for h in r['named_hypotheses']));kind='DIRECT_CALL' if e['selected_target'] else 'STATIC_UNREACHABLE'
   c=dict(id='NEB-adopted-field-edge:'+e['obligation_id'],edge=e['edge'],status='CLOSED',kind=kind,frozen_revision=base['frozen_revision'],source_body_sha256=source['frozen_body_sha256'],selected_callee_claims=claims,inner_hypotheses_discharged=inner,hypothesis_discharge_theorems={n:domains if n.endswith('PacketDomain') else domains+[full] for n in inner},parts=dict(packet_domain=dict(theorems=domains),canonical_carrier=dict(theorems=domains+[full]),same_inputs_result=dict(theorems=domains+[full]),state_ordered_effects=dict(theorems=[full]),physical_interpretation=dict(theorems=domains+[full]),native_callsite_association=dict(theorems=domains+[full])),lean_evidence=ps,theorems=names,residual_hypotheses=[],review=rev,native_review=nr,trust='NativeContractSemanticTransport: adopted translated field bridge; reclassification, never removal')
   edges[e['edge']]=c
   if e in extras:e.update(certificate=c,status='CLOSED',obstacle=None)
  for r in base['rows']:
   if r['function']!=fn:continue
   ext={}
   for o in r['caller_domain_obligations']:
    if 'call' not in o:continue
    call=o['call'];syntax=call.get('expression',call.get('syntax'))
    if call.get('resolution')=='disabled release cfg':ext[o['id']]=dict(kind='RELEASE_CFG_INACTIVE',syntax=syntax,cfg=call['cfg'],selected_core_features=['r0'],theorems=[full],native_review=nr)
    elif syntax=='M31':ext[o['id']]=dict(kind='TRANSPARENT_M31_CONSTRUCTOR',syntax=syntax,theorems=[full])
    else:
     assert fn==field+'CM31::mul' and syntax=='u64::from',call
     ext[o['id']]=dict(kind='LOSSLESS_U32_TO_U64',syntax=syntax,line=call['line'],caller_body_sha256=r['frozen_body_sha256'],theorems=['NEB_CMCarrier.lossless','NEB_CMCarrier.actual_casts','NEB_NativeFieldScalars.cross_checked'],native_review=nr)
   rows[r['row']]=dict(id='NEB-adopted-field-root:'+r['row'],row=r['row'],function=fn,frozen_body_sha256=r['frozen_body_sha256'],selected_claims=r['selected_claims'],named_hypotheses_discharged=[h['name'] for h in r['named_hypotheses']],inventory_domains_discharged=[o['unit'] for o in r['inventory_domain_obligations']],parts=['result','state','ordered_effects','native_association'],lean_evidence=ps,remaining_inner_hypotheses=[],top_hypotheses=[fn+'.PacketDomain',fn+'.PhysicalInterpretation','NativeContractSemanticTransport'],review=rev,native_review=nr,external_obligations=ext)
 return edges,rows,extras
