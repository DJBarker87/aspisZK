"""Five raw private-Q roots and their three real dependency edges."""
from NEO_native_review import *
import NEO_q_review
P='crates/aspis-r1-cost-probe/src/fast_pairing.rs::'
SPECS={P+'canonical::Q::limbs':('q_limbs','limbs','limbs_frame'),P+'canonical::Q::from_limbs':('q_from_limbs','from_limbs','constructor_frame'),P+'canonical::Q::from_wide':('q_from_wide','from_wide','wide_frame'),P+'limbs_of':('limbs_of','limbs_of','public_frame'),P+'checked_q':('checked_q','checked','checked_calls')}
def expected(base,check_receipt):
 review=NEO_q_review.review();assert review==obj(E/'NEO_Q_REVIEW.json');rows={};edges={}
 for row in base['rows']:
  if row['function'] not in SPECS:continue
  native,value,frame=SPECS[row['function']];nr=review[native];src=snapshot(nr['positive']);code=src['NEO_src/'+row['source_file']].encode()
  a,b=row['frozen_body_byte_range']
  frozen=subprocess.check_output(['git','show',base['frozen_revision']+':'+row['source_file']],cwd=R)
  injection=b'\n#[cfg(kani)]\nmod NEO_q { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/src/NEO_q.rs")); }'
  assert code.count(injection)==1 and code.replace(injection,b'')==frozen
  assert sha(frozen[a:b])==row['frozen_body_sha256']
  proofs=[]
  for attempt,names in [('NEO_L019',['NEO_QRepresentation.'+value]),('NEO_L020',['NEO_QComposition.'+frame])]:
   p=E/attempt/'receipt.json';item=dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p.read_bytes()),theorems=names)
   for n in names:
    rc=check_receipt(item,n)
    for f,h in rc['source_hashes'].items():assert sha((E/f).read_bytes())==h
   proofs.append(item)
  ext={};calls={}
  for o in row['caller_domain_obligations']:
   if 'callee' in o:
    allowed={P+'canonical::Q::from_wide':{'crates/aspis-core/src/field/wide_exact.rs::WideExact::to_limbs'},P+'checked_q':{P+'canonical::Q::from_limbs',P+'limbs_of'}}
    assert o['callee'] in allowed[row['function']]
    calls[o['id']]=dict(callee=o['callee'],domain='Every valid raw typed owned carrier, no canonicality/acceptance premise',same_input='Actual source input and intermediate getter words',parts=['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association'],theorems=[n for p in proofs for n in p['theorems']])
   else:
    syntax=o['call'].get('expression',o['call'].get('syntax'));assert syntax in ['Some','Self','Ok','Err'];ext[o['id']]=dict(kind='TRANSPARENT_CONSTRUCTOR',syntax=syntax,source_line=o['call']['line'])
  rows[row['row']]=dict(id='NEO-q-root:'+row['row'],row=row['row'],function=row['function'],claim_id='NEO::'+row['function'],frozen_body_sha256=row['frozen_body_sha256'],domain='Every raw typed input; complete Result including rejection',parts=['result','state','ordered_effects','native_association'],lean_evidence=proofs,native_pair=[nr['positive'],nr['negative']],active_support_receipts=[str((E/nr['positive']/'receipt.json').relative_to(R))],calls=calls,external_obligations=ext,remaining_inner_hypotheses=[],historical_credit_restored=[],top_hypotheses=['RootPacketDomain','RootPhysicalInterpretation','NativeContractSemanticTransport'],association_sha256=sha((E/'NEO_Q_ASSOCIATION.md').read_bytes()))
  for call in calls.values():
   edge=row['function']+' -> '+call['callee'];edges[edge]=dict(edge=edge,status='CLOSED',certificate=dict(id='NEO-q-edge:'+edge,caller=row['function'],**call,source_body_sha256=row['frozen_body_sha256'],native_pair=[nr['positive'],nr['negative']],lean_evidence=proofs),obstacle=None)
 assert len(rows)==10 and len(edges)==3
 return rows,edges
