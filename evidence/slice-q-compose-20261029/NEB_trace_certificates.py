"""Exact deployed trace no-op recipe, retaining every disabled cfg occurrence."""
from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();obj=lambda p:json.loads(p.read_text())
PIN='decb42273a028bb941471b2c75a4e43e0b395d688e9fe5398bf6c3d8076d8ee0'
def expected(base):
 subprocess.run(['python3',str(E/'NEB_trace_review.py'),'--check'],check=True,stdout=subprocess.DEVNULL)
 assert sha((E/'NEB_TraceFrame.lean').read_bytes())==PIN
 p=E/'NEB_L075/receipt.json';d=obj(p);assert d['exit_status']==0 and d['source_hashes']=={'NEB_TraceFrame.lean':PIN} and d['print_axioms']==["'NEB_TraceFrame.result' does not depend on any axioms"]
 names=['NEB_TraceFrame.result'];ps=[dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p.read_bytes()),theorems=names)]
 fn='crates/aspis-r1-cost-probe/src/trace.rs::value';review=E/'NEB_TRACE_ASSOCIATION.md';rev=dict(path=str(review.relative_to(R)),sha256=sha(review.read_bytes()),conclusion_hiding=False,statement_and_native_association_checked=True);native=E/'NEB_TRACE_REVIEW.json';nr=dict(path=str(native.relative_to(R)),sha256=sha(native.read_bytes()));rows={};features=obj(native)['selected_library_features']
 for r in base['rows']:
  if r['function']!=fn:continue
  assert not any('callee' in o for o in r['caller_domain_obligations'])
  ext={}
  for o in r['caller_domain_obligations']:
   call=o['call'];assert call['resolution']=='disabled release cfg' and call['cfg']==['#[cfg(feature="prover")]']
   ext[o['id']]=dict(kind='RELEASE_PROVER_INACTIVE',syntax=call['syntax'],line=call['line'],cfg=call['cfg'],caller_body_sha256=r['frozen_body_sha256'],selected_library_features=features,theorems=names,native_review=nr)
  rows[r['row']]=dict(id='NEB-trace-root:'+r['row'],row=r['row'],function=fn,frozen_body_sha256=r['frozen_body_sha256'],selected_claims=r['selected_claims'],named_hypotheses_discharged=[h['name'] for h in r['named_hypotheses']],inventory_domains_discharged=[o['unit'] for o in r['inventory_domain_obligations']],parts=['result','state','ordered_effects','native_association'],lean_evidence=ps,remaining_inner_hypotheses=[],top_hypotheses=[fn+'.PacketDomain',fn+'.PhysicalInterpretation','NativeContractSemanticTransport'],review=rev,native_review=nr,external_obligations=ext)
 return {},rows
