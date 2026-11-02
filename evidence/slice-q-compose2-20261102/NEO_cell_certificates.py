from NEO_native_review import *
import NEO_cell_review
V='crates/aspis-r1-cost-probe/src/verifier.rs::'
FUNCTIONS={V+'basis_at':('basis_cell','basis','Every raw [M31;256], index<256'),V+'accumulated_weight_at':('accumulated_cell','accumulated','Every raw QM31 slice of length<=64, index<len')}
def expected(base,check_receipt):
 native=NEO_cell_review.audit();assert native==obj(E/'NEO_CELL_REVIEW.json');rows={};edges={};proofs=[]
 for a,names in [('NEO_L038',['NEO_CellReference.slice','NEO_CellReference.array','NEO_CellReference.basis','NEO_CellReference.accumulated']),('NEO_L039',['NEO_CellCarrier.qm','NEO_CellCarrier.caller'])]:
  p=E/a/'receipt.json';item=dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p.read_bytes()),theorems=names)
  for n in names:
   rc=check_receipt(item,n)
   for f,h in rc['source_hashes'].items():assert sha((E/f).read_bytes())==h
  proofs.append(item)
 for row in base['rows']:
  if row['function'] not in FUNCTIONS:continue
  method,theorem,domain=FUNCTIONS[row['function']];nr=native[method];src=snapshot(nr['positive']);a,b=row['frozen_body_byte_range']
  assert sha(src['NEO_src/'+row['source_file']].encode()[a:b])==row['frozen_body_sha256'] and not row['caller_domain_obligations']
  rows[row['row']]=dict(id='NEO-cell-root:'+row['row'],row=row['row'],function=row['function'],domain=domain,parts=['result','state','ordered_effects','native_association'],lean_evidence=proofs,native_pair=[nr['positive'],nr['negative']],active_support_receipts=[str((E/nr['positive']/'receipt.json').relative_to(R))],historical_support_restored=[],remaining_inner_hypotheses=[],top_hypotheses=['RootPacketDomain','RootPhysicalInterpretation','NativeContractSemanticTransport'],frozen_body_sha256=row['frozen_body_sha256'],association_sha256=sha((E/'NEO_CELL_ASSOCIATION.md').read_bytes()))
 caller=V+'accumulate_batched_with_node';parent=next(r for r in base['rows'] if r['function']==caller)
 frozen=subprocess.check_output(['git','show',base['frozen_revision']+':'+parent['source_file']],cwd=R,text=True)
 start=frozen.index('fn accumulate_batched_with_node(');end=frozen.index('\npub fn polynomial(',start);body=frozen[start:end]
 for text in ['let width=a.weights.len();','let mut basis=[M31::ZERO;256];','for j in 0..width {','weights.push(j,a.power,basis_at(&basis,j));','accumulated_weight_at(&a.weights,j)','#[cfg(feature="prover")] {a.weights[j]=weights.value(j);}']:
  assert text in body
 for callee in FUNCTIONS:
  edge=caller+' -> '+callee
  edges[edge]=dict(edge=edge,status='CLOSED',obstacle=None,certificate=dict(id='NEO-cell-call:'+edge,caller=caller,callee=callee,source_body_sha256=parent['frozen_body_sha256'],domain='Same root a.weights allocation with length<=64 and current native j<a.weights.len(); local basis has exactly256 cells',native=native[FUNCTIONS[callee][0]],parts=['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association'],lean_evidence=proofs,residual_inner_hypotheses=[],association_sha256=sha((E/'NEO_CELL_ASSOCIATION.md').read_bytes())))
 assert len(rows)==4 and len(edges)==2
 return rows,edges
