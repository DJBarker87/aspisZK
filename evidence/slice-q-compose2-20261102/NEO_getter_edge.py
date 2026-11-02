"""Source-ordered query getter-copy edge on the constructor-established domain."""
from NEO_native_review import *
import NEO_getter_review
F='crates/aspis-r1-cost-probe/src/candidate.rs::query_values'
G='crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_query'
def expected(base,check_receipt):
 native=NEO_getter_review.audit('NEO_K043','NEO_K044',['NEO_K045','NEO_K046'])
 src=snapshot('NEO_K043');helper=src['NEO_src/crates/aspis-r1-cost-probe/src/verifier/NEO_geometry.rs']
 for statement in ['let actual=geometry.for_query(index);','let expected=NEO_getter_reference::selected(geometry.start,index,&geometry.inverses);','let copied=*actual;','let same=core::ptr::eq(actual,expected)&&copied[j].0==expected[j].0;','let j:usize=kani::any();kani::assume(j<5);']:
  assert helper.count(statement)==1,'missing/changed native copied-window assertion'
 frozen=subprocess.check_output(['git','show',base['frozen_revision']+':crates/aspis-r1-cost-probe/src/candidate.rs'],cwd=R,text=True)
 start=frozen.index('fn query_values(');end=frozen.index('\n\n\n#[inline(always)]',start);body=frozen[start:end]
 assert body.count('let i = a.next;')==1 and body.count('let inverse = *geometry.for_query(i);')==1
 prefix=body[:body.index('let inverse = *geometry.for_query(i);')]
 assert all(x not in prefix for x in ['a.next=','a.next =','&mut a','&mut geometry','geometry.start=','geometry.start ='])
 proofs=[]
 for a,names in [('NEO_L026',['NEO_GetterCaller.caller','NEO_GetterCaller.complete'])]:
  p=E/a/'receipt.json';item=dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p.read_bytes()),theorems=names)
  for n in names:
   r=check_receipt(item,n)
   for f,h in r['source_hashes'].items():assert sha((E/f).read_bytes())==h
  proofs.append(item)
 r=next(r for r in base['rows'] if r['function']==F)
 edge=F+' -> '+G
 return {edge:dict(edge=edge,status='CLOSED',obstacle=None,certificate=dict(id='NEO-getter-copied-call:'+edge,caller=F,callee=G,frozen_body_sha256=r['frozen_body_sha256'],domain='Root geometry constructor lengths are finish-start; start<=a.next<finish<=22. These are caller input invariants, not callee-success or output-equality assumptions.',native=native,source_query_body_sha256=sha(body.encode()),same_input='Same geometry and i=a.next; no prior write to either; original dereference/copy at the reached call',lean_evidence=proofs,parts=['packet_domain','canonical_carrier','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association'],residual_inner_hypotheses=[],root_domain_retained=True))}
