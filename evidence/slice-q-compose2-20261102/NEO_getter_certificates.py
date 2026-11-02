"""Exact full borrowed-return getter roots, not a borrowed contract stub."""
from NEO_native_review import *
import NEO_getter_review
F='crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_query'
def expected(base,check_receipt):
 review=NEO_getter_review.audit('NEO_K039','NEO_K040',['NEO_K041','NEO_K042']);assert review==obj(E/'NEO_GETTER_REVIEW.json')
 proofs=[]
 for a,names in [('NEO_L021',['NEO_GeometryGetter.selected']),('NEO_L025',['NEO_GetterReference.same']),('NEO_L026',['NEO_GetterCaller.caller','NEO_GetterCaller.complete'])]:
  p=E/a/'receipt.json';item=dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p.read_bytes()),theorems=names)
  for n in names:
   rc=check_receipt(item,n)
   for f,h in rc['source_hashes'].items():assert sha((E/f).read_bytes())==h
  proofs.append(item)
 rows={};src=snapshot('NEO_K039')
 for r in base['rows']:
  if r['function']!=F:continue
  assert r['caller_domain_obligations']==[]
  a,b=r['frozen_body_byte_range'];assert sha(src['NEO_src/'+r['source_file']].encode()[a:b])==r['frozen_body_sha256']
  rows[r['row']]=dict(id='NEO-getter-root:'+r['row'],row=r['row'],function=F,domain=review['domain'],parts=['result','state','ordered_effects','native_association'],lean_evidence=proofs,native_pair=['NEO_K039','NEO_K040'],active_support_receipts=[str((E/'NEO_K039/receipt.json').relative_to(R))],historical_support_restored=[],remaining_inner_hypotheses=[],top_hypotheses=['RootPacketDomain','RootPhysicalInterpretation','NativeContractSemanticTransport'],frozen_body_sha256=r['frozen_body_sha256'],association_sha256=sha((E/'NEO_GETTER_ASSOCIATION.md').read_bytes()))
 assert len(rows)==2
 return rows
