from NEO_native_review import *
import NEO_tail_review
V='crates/aspis-r1-cost-probe/src/verifier.rs::'
C='crates/aspis-r1-cost-probe/src/candidate.rs::'
I='crates/aspis-core/src/r0/domain.rs::FibreIndex::new'
FUNCTIONS={I:('index','Every native usize; checked Ok exact input below262144 or precisely IndexOutOfRange'),C+'opening':('opening','Same immutable proof allocation of57607 arbitrary bytes and actual current query ordinal i<22')}
def expected(base,check_receipt):
 native=NEO_tail_review.audit();assert native==obj(E/'NEO_TAIL_REVIEW.json');rows={};edges={};proofs=[]
 for a,names in [('NEO_L052',['NEO_TailReference.checked','NEO_TailReference.opening']),('NEO_L059',['NEO_TailPackets.admitted','NEO_TailPackets.accepted','NEO_TailPackets.opening']),('NEO_L034',['NEO_GeometryGather.accepted'])]:
  p=E/a/'receipt.json';item=dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p.read_bytes()),theorems=names)
  for n in names:
   rc=check_receipt(item,n)
   for f,h in rc['source_hashes'].items():assert sha((E/f).read_bytes())==h
  proofs.append(item)
 for row in base['rows']:
  if row['function'] not in FUNCTIONS:continue
  method,domain=FUNCTIONS[row['function']];nr=native[method];src=snapshot(nr['positive']);a,b=row['frozen_body_byte_range']
  actual=src['NEO_src/'+row['source_file']].encode()[a:b]
  assert sha(actual)==row['frozen_body_sha256'] and not row['caller_domain_obligations']
  rows[row['row']]=dict(id='NEO-tail-root:'+row['row'],row=row['row'],function=row['function'],domain=domain,parts=['result','state','ordered_effects','native_association'],lean_evidence=proofs,native_pair=[nr['positive'],nr['negative']],active_support_receipts=[str((E/nr['positive']/'receipt.json').relative_to(R))],historical_support_restored=[],remaining_inner_hypotheses=[],top_hypotheses=['RootPacketDomain','RootPhysicalInterpretation','NativeContractSemanticTransport'],frozen_body_sha256=row['frozen_body_sha256'],association_sha256=sha((E/'NEO_TAIL_ASSOCIATION.md').read_bytes()))
 for caller,callee in [(V+'QueryGeometry::for_range',I),(C+'query_values',C+'opening')]:
  parent=next(r for r in base['rows'] if r['function']==caller)
  frozen=subprocess.check_output(['git','show',base['frozen_revision']+':'+parent['source_file']],cwd=R,text=True)
  a,b=parent['frozen_body_byte_range'];body=frozen.encode()[a:b].decode();assert sha(body.encode())==parent['frozen_body_sha256']
  if callee==I:
   for text in ['FibreIndex::new','for &query in &queries[start..end]','query as usize']:assert text in body
   domain=FUNCTIONS[I][1]
  else:
   for text in ['opening(proof, i)','p.queries[i]','let i = a.next;']:assert text in body
   domain=FUNCTIONS[C+'opening'][1]
  edge=caller+' -> '+callee
  edges[edge]=dict(edge=edge,status='CLOSED',obstacle=None,certificate=dict(id='NEO-tail-call:'+edge,caller=caller,callee=callee,source_body_sha256=parent['frozen_body_sha256'],domain=domain,native=native[FUNCTIONS[callee][0]],parts=['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association'],lean_evidence=proofs,residual_inner_hypotheses=[],association_sha256=sha((E/'NEO_TAIL_ASSOCIATION.md').read_bytes())))
 assert len(rows)==4 and len(edges)==2
 return rows,edges
