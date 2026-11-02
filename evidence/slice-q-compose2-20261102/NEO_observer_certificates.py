"""Adopted release-only mark subtree, never Option<fn> native credit."""
from NEO_native_review import *
P=E.parent/'slice-q-fnptr-20261029'
F='crates/aspis-r1-cost-probe/src/verifier.rs::mark'
C='crates/aspis-r1-cost-probe/src/candidate.rs::query_values'
def expected(base,check_receipt):
 import sys
 sys.path.insert(0,str(P));import NEF_OBSERVER_CERTIFICATE as c
 src,nodes=c.inputs();checked=c.validate(src,nodes);review=obj(E/'NEO_OBSERVER_REVIEW.json')
 assert review['certificate']==checked and review['adoption']=='C3-BIN 2026-11-02 ruling z(1)'
 assert not review['historical_native_credit_restored'] and not review['native_pointer_property']
 for f,h in review['scripts'].items():assert sha((P/f).read_bytes())==h
 for f,text in src.items():assert sha(text.encode())==review['source_hashes'][f]
 controls=obj(E/'NEO_OBSERVER_TESTS.json');assert controls['positive'] and len(controls['mutation_tests'])==17 and all(x['rejected'] for x in controls['mutation_tests'])
 rc=E/'NEO_L001/receipt.json';names=['NEO_ObserverPort.mark','NEO_ObserverPort.continuation','NEO_ObserverPort.frame']
 proof=dict(receipt=str(rc.relative_to(R)),receipt_sha256=sha(rc.read_bytes()),theorems=names)
 for n in names:
  receipt=check_receipt(proof,n)
  for f,h in receipt['source_hashes'].items():assert sha((E/f).read_bytes())==h
 rows={}
 for row in base['rows']:
  if row['function']!=F:continue
  a,b=row['frozen_body_byte_range'];assert sha(src[row['source_file']].encode()[a:b])==row['frozen_body_sha256']
  ext={}
  for o in row['caller_domain_obligations']:
   assert 'call' in o and o['call'].get('expression',o['call'].get('syntax'))=='f'
   ext[o['id']]=dict(kind='UNREACHED_NONE_BRANCH',same_cfg='deployed program without cu-profiling; candidate forwarding graph exact',observer='None',writes=[],events=[],calls=[],panic=False,diverges=False)
  rows[row['row']]=dict(id='NEO-observer-root:'+row['row'],row=row['row'],function=F,domain='Deployed cfg-constant None; every Phase after its original argument evaluation',parts=['result','state','ordered_effects','native_association'],lean_evidence=[proof],external_obligations=ext,active_support_receipts=[],historical_support_restored=[],source_body_sha256=row['frozen_body_sha256'],trust='Adopted z(1) P6/D188 no-effect oracle; reclassification, never removal',review_sha256=sha((E/'NEO_OBSERVER_REVIEW.json').read_bytes()))
 flow=next(x for x in checked['edges'] if x['path']=='crates/aspis-r1-cost-probe/src/candidate.rs' and x['caller']=='query_values' and x['callee']=='mark')
 assert flow==dict(path='crates/aspis-r1-cost-probe/src/candidate.rs',caller='query_values',callee='mark',argument=0,arity=2)
 edge=C+' -> '+F
 return rows,{edge:dict(edge=edge,status='CLOSED',obstacle=None,certificate=dict(id='NEO-observer-call:'+edge,caller=C,callee=F,domain='Exact deployed forwarded None established by adopted complete constructor/forwarding certificate',phase='Phase::Query(i), evaluated before the no-effect call',parts=['packet_domain','same_inputs_result','state_ordered_effects','physical_interpretation','native_callsite_association'],lean_evidence=[proof],flow=flow,native_credit_restored=[],review_sha256=sha((E/'NEO_OBSERVER_REVIEW.json').read_bytes())))}
