from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();obj=lambda p:json.loads(p.read_text())
PINS={'NEB_RepresentationRefs': '9b87768a1b0c4f4583ff31477dfe74a8348230ab358eb0b3f369d781acecbe13', 'NEB_WideRepresentation': 'a3acdb2abf3ea6450e404301053fedbecb3759214ae931a4587b357fff6ad893', 'NEB_EmbeddingDomain': '490a6f0a208e8337a35121ba8b72db755c82cee0fecdb258e664780b678f73f8'}
def proof(module,names):
 h=PINS[module];assert sha((E/(module+'.lean')).read_bytes())==h
 found=[]
 for p in E.glob('NEB_L*/receipt.json'):
  d=obj(p)
  if d.get('module')==module and d['exit_status']==0 and d['source_hashes'].get(module+'.lean')==h and all(any(a.startswith("'"+n+"' ") and 'sorryAx' not in a for a in d['print_axioms']) for n in names):found.append(p)
 assert found,(module,names)
 p=sorted(found)[-1];return dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p.read_bytes()),theorems=names)
def expected(base):
 subprocess.run(['python3',str(E/'NEB_additive_review.py'),'--check'],check=True,stdout=subprocess.DEVNULL)
 ex=obj(E/'NEB_REPRESENTATION_EXTRACTION_PINS.json');assert ex['exit']==0 and ex['rust_reference_sha256']==sha((E/'NEB_representation_reference.rs').read_bytes())
 assert ex['charon_sha256']=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8' and ex['aeneas_sha256']=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
 for n in ['Types','Funs']:assert sha((E/'NEB_RepresentationRef'/(n+'.lean')).read_bytes())==ex['outputs']['NEB_representation_extracted/NEB_RepresentationRef/'+n+'.lean']
 w='crates/aspis-core/src/field/wide_exact.rs::';spec={w+'canonical_qm31':('canonical_frame',['q_roundtrip','q_injective','canonical']),w+'WideExact::from_qm31':('embedding_frame',['embedding_roundtrip','embedding_injective','embedding']),w+'WideExact::to_limbs':('getter_frame',['e_roundtrip','e_injective','getter'])}
 review=E/'NEB_REPRESENTATION_ASSOCIATION.md';rev=dict(path=str(review.relative_to(R)),sha256=sha(review.read_bytes()),conclusion_hiding=False,statement_and_native_association_checked=True);native=E/'NEB_ADDITIVE_REVIEW.json';nr=dict(path=str(native.relative_to(R)),sha256=sha(native.read_bytes()));edges={};rows={}
 for fn,(frame,aux) in spec.items():
  full='NEB_RepresentationRefs.'+frame;ps=[proof('NEB_RepresentationRefs',[full]+['NEB_RepresentationRefs.'+n for n in aux]),proof('NEB_WideRepresentation',['NEB_WideRepresentation.word','NEB_WideRepresentation.canonical_calls'])]
  if frame=='embedding_frame':ps.append(proof('NEB_EmbeddingDomain',['NEB_EmbeddingDomain.canonical_output','NEB_EmbeddingDomain.canonical_edge']))
  names=[n for p in ps for n in p['theorems']];source=next(r for r in base['rows'] if r['function']==fn)
  if frame=='embedding_frame':
   edge=fn+' -> '+w+'canonical_qm31';children=[r for r in base['rows'] if r['function']==w+'canonical_qm31'];claims=sorted(set(c for r in children for c in r['selected_claims']));inner=sorted(set(h['name'] for r in children for h in r['named_hypotheses']));law='NEB_EmbeddingDomain.canonical_edge'
   edges[edge]=dict(id='NEB-embedding-canonical-edge',edge=edge,status='CLOSED',kind='DIRECT_CALL',frozen_revision=base['frozen_revision'],source_body_sha256=source['frozen_body_sha256'],selected_callee_claims=claims,inner_hypotheses_discharged=inner,hypothesis_discharge_theorems={n:[law] for n in inner},parts={p:dict(theorems=[law,full]) for p in ['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association']},lean_evidence=ps,theorems=names,residual_hypotheses=[],review=rev,native_review=nr,trust='NativeContractSemanticTransport: reclassification, never removal')
  for r in base['rows']:
   if r['function']!=fn:continue
   ext={}
   for o in r['caller_domain_obligations']:
    if 'call' not in o:continue
    call=o['call'];syntax=call.get('expression',call.get('syntax'))
    if syntax=='M31':ext[o['id']]=dict(kind='TRANSPARENT_M31_CONSTRUCTOR',syntax=syntax,theorems=[full])
    else:
     assert syntax=='reduce' and call['resolution'] in ['inline closure (body inventoried in parent)','local closure body bundled with caller']
     ext[o['id']]=dict(kind='BUNDLED_PURE_REMAINDER_CLOSURE',syntax=syntax,line=call['line'],caller_body_sha256=r['frozen_body_sha256'],theorems=['NEB_WideRepresentation.word','NEB_WideRepresentation.canonical_calls',full],native_review=nr)
   rows[r['row']]=dict(id='NEB-representation-root:'+r['row'],row=r['row'],function=fn,frozen_body_sha256=r['frozen_body_sha256'],selected_claims=r['selected_claims'],named_hypotheses_discharged=[h['name'] for h in r['named_hypotheses']],inventory_domains_discharged=[o['unit'] for o in r['inventory_domain_obligations']],parts=['result','state','ordered_effects','native_association'],lean_evidence=ps,remaining_inner_hypotheses=[],top_hypotheses=[fn+'.PacketDomain',fn+'.PhysicalInterpretation','NativeContractSemanticTransport'],review=rev,native_review=nr,external_obligations=ext)
 return edges,rows
