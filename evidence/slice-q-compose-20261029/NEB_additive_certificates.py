"""Content-addressed additive recipes; every slot has a reviewed theorem role."""
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();obj=lambda p:json.loads(p.read_text())
# Updated only after the corresponding scoped target passed and statement review.
SOURCES={'NEB_AdditiveFrames': '1c4acff00a3fa6f32a91c715c3674dafdd28a2e5ec11d6cf22b14ca56d4d42b1', 'NEB_AdditiveCalls': '72302cda5b38b2879d070c12667df9f166124eaaba7891135b293d72d929df2b', 'NEB_FieldDomains': 'b5b9bd475ba3fa4af2f266525e8035af55d725c66f2351fe2738504d68f76474', 'NEB_QMCalls': 'd75da4354ed1478e0cb4cc090a05789fe8a64d7e146dad6e1aa4de140733e459', 'NEB_WideSubCalls': '45520de6e38360537e79de00923c4aa26181f238dd278e0d8136475c7a2ccad6', 'NEB_WideSubRef': 'bf74375c4b7de9802ce5d3fb51ca91d4032026f48961fe6ec14061034162684a', 'NEB_ArrayRefs': '9a9cb1445ff664ca4122d4e52569be7f07ba6988f8f7dc91dd95ff801962e484', 'NEB_WordRefs': '162acce1ba3a9762bfde9b71c2eaea468717465935ccdc5d24339895341cc7b3'}
def evidence(module,names):
 p=E/(module.replace('.','/')+'.lean');expected=SOURCES[module];assert sha(p.read_bytes())==expected,'unreviewed additive source'
 found=[]
 for q in E.glob('NEB_L*/receipt.json'):
  d=obj(q)
  if d.get('module')==module and d['exit_status']==0 and d['source_hashes'].get(module.replace('.','/')+'.lean')==expected:
   if all(any(a.startswith("'"+n+"' ") and 'sorryAx' not in a for a in d['print_axioms']) for n in names):found.append(q)
 assert found,(module,names)
 q=sorted(found)[-1];return dict(receipt=str(q.relative_to(R)),receipt_sha256=sha(q.read_bytes()),theorems=names)
def expected(base):
 if not SOURCES:return {},{},[]
 subprocess.run(['python3',str(E/'NEB_additive_review.py'),'--check'],check=True,stdout=subprocess.DEVNULL)
 ex=obj(E/'NEB_ADDITIVE_EXTRACTION_PINS.json');assert ex['exit']==0 and ex['rust_reference_sha256']==sha((E/'NEB_additive_reference.rs').read_bytes())
 assert ex['charon_sha256']=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8' and ex['aeneas_sha256']=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
 for n in ['Types','Funs']:assert sha((E/'NEB_AdditiveRef'/(n+'.lean')).read_bytes())==ex['outputs']['NEB_additive_extracted/NEB_AdditiveRef/'+n+'.lean']
 field='crates/aspis-core/src/field.rs::';wide='crates/aspis-core/src/field/wide_exact.rs::'
 definitions={field+'M31::add':('m_add',None,[]),field+'M31::sub':('m_sub',None,[]),field+'M31::double':('m_double','NEB_AdditiveCalls',['base_double_arguments']),field+'CM31::add':('cm_add','NEB_FieldDomains',['cm_arguments','cm_add_calls']),field+'CM31::sub':('cm_sub','NEB_FieldDomains',['cm_arguments','cm_sub_calls']),field+'CM31::double':('cm_double','NEB_AdditiveCalls',['double_arguments']),field+'QM31::add':('qm_add','NEB_QMCalls',['add']),field+'QM31::sub':('qm_sub','NEB_QMCalls',['sub']),wide+'WideExact::add':('wide_add','NEB_AdditiveCalls',['wide_add']),wide+'WideExact::sub':('wide_sub','NEB_WideSubCalls',['source'])}
 review=E/'NEB_ADDITIVE_ASSOCIATION.md';rev=dict(path=str(review.relative_to(R)),sha256=sha(review.read_bytes()),conclusion_hiding=False,statement_and_native_association_checked=True);native=E/'NEB_ADDITIVE_REVIEW.json';nr=dict(path=str(native.relative_to(R)),sha256=sha(native.read_bytes()))
 edges={};rows={};extras=[];current=obj(E/'NEB_EDGES.json')['edges'];allrows=base['rows']
 for fn,(short,callmod,callnames) in definitions.items():
  frame='NEB_AdditiveFrames.'+short;proofs=[evidence('NEB_AdditiveFrames',[frame])]
  if callmod:proofs.append(evidence(callmod,[callmod+'.'+n for n in callnames]))
  if short=='wide_sub':proofs.append(evidence('NEB_WideSubRef',['NEB_WideSubRef.reference','NEB_WideSubRef.result']))
  elif short.startswith(('cm_','qm_','wide_')):proofs.append(evidence('NEB_ArrayRefs',['NEB_ArrayRefs.'+('cm_injective' if short.startswith('cm_') else 'qm_injective' if short.startswith('qm_') else 'wide_injective')]))
  else:proofs.append(evidence('NEB_WordRefs',['NEB_WordRefs.'+short[2:]]))
  allnames=[n for p in proofs for n in p['theorems']];source=next(r for r in allrows if r['function']==fn)
  selected_edges=[e for e in current if e['caller']==fn]
  # NDT retains conservative self-targets even though slices exclude self edges.
  for o in source['caller_domain_obligations']:
   if o.get('callee')==fn:
    assert not any(e['obligation_id']==o['id'] for e in selected_edges)
    e=dict(edge=fn+' -> '+fn,caller=fn,callee=fn,obligation_id=o['id'],status='OPEN',classification='CONSERVATIVE_ALTERNATIVE',source_body_sha256=source['frozen_body_sha256'],static_resolution='Frozen receiver field type and full actual parent contract; no recursive call',selected_target=False,model_domain_theorems=[],certificate=None,required_named_hypotheses=o['required_named_hypotheses'],callee_packet_domains=[],actual_inventory_calls=[],obstacle='Explicit conservative self-target certificate required')
    selected_edges.append(e);extras.append(e)
  for e in selected_edges:
   children=[r for r in allrows if r['function']==e['callee']];claims=sorted(set(c for r in children for c in r['selected_claims']));names=sorted(set(h['name'] for r in children for h in r['named_hypotheses']))
   active=e['selected_target'];kind='DIRECT_CALL' if active else 'STATIC_UNREACHABLE'
   def part(ns):return dict(theorems=ns)
   domains=[callmod+'.'+n for n in callnames] if callmod else [frame]
   c=dict(id='NEB-additive-edge:'+e['obligation_id'],edge=e['edge'],status='CLOSED',kind=kind,frozen_revision=base['frozen_revision'],source_body_sha256=source['frozen_body_sha256'],selected_callee_claims=claims,inner_hypotheses_discharged=names,hypothesis_discharge_theorems={n:domains if n.endswith('PacketDomain') else [frame] for n in names},parts=dict(packet_domain=part(domains),canonical_carrier=part(domains+[frame]),same_inputs_result=part(domains+[frame]),state_ordered_effects=part([frame]),physical_interpretation=part([frame]),native_callsite_association=part([frame])),lean_evidence=proofs,theorems=allnames,residual_hypotheses=[],review=rev,native_review=nr,trust='NativeContractSemanticTransport: reclassification, never removal')
   edges[e['edge']]=c
   if e in extras:e.update(certificate=c,status='CLOSED',obstacle=None)
  for r in allrows:
   if r['function']!=fn:continue
   ext={}
   for o in r['caller_domain_obligations']:
    if 'call' not in o:continue
    call=o['call'];syntax=call.get('expression',call.get('syntax'))
    if call.get('resolution')=='disabled release cfg':
     assert call['cfg'] and any(any('feature = \"'+f+'\"' in c for f in ['r0-op-count','r0-r91-audit','r0-e4-reference']) for c in call['cfg'])
     ext[o['id']]=dict(kind='RELEASE_CFG_INACTIVE',syntax=syntax,cfg=call['cfg'],selected_core_features=['r0'],theorems=[frame],native_review=nr)
    else:
     assert syntax=='M31'
     ext[o['id']]=dict(kind='TRANSPARENT_M31_CONSTRUCTOR',syntax=syntax,theorems=[frame])
   rows[r['row']]=dict(id='NEB-additive-root:'+r['row'],row=r['row'],function=fn,frozen_body_sha256=r['frozen_body_sha256'],selected_claims=r['selected_claims'],named_hypotheses_discharged=[h['name'] for h in r['named_hypotheses']],inventory_domains_discharged=[o['unit'] for o in r['inventory_domain_obligations']],parts=['result','state','ordered_effects','native_association'],lean_evidence=proofs,remaining_inner_hypotheses=[],top_hypotheses=[fn+'.PacketDomain',fn+'.PhysicalInterpretation','NativeContractSemanticTransport'],review=rev,native_review=nr,external_obligations=ext)
 return edges,rows,extras
