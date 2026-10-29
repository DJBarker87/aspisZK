"""Exact scalar private-reducer recipe; no dot/carrier promotion."""
from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();obj=lambda p:json.loads(p.read_text())
PIN='728e76b4d9b537b661981f0a1dfbd80f448eee9e2b7e33166fa9e6c0f9e013e2'
def expected(base):
 subprocess.run(['python3',str(E/'NEB_private_reduce_review.py'),'--check'],check=True,stdout=subprocess.DEVNULL)
 assert sha((E/'NEB_PrivateReducer.lean').read_bytes())==PIN
 candidates=[]
 for p in E.glob('NEB_L*/receipt.json'):
  d=obj(p)
  if d.get('module')=='NEB_PrivateReducer' and d['exit_status']==0 and d['source_hashes'].get('NEB_PrivateReducer.lean')==PIN:candidates.append(p)
 assert candidates
 p=sorted(candidates)[-1];d=obj(p);names=['NEB_PrivateReducer.'+n for n in ['reference','frame','constant_cast']]
 assert all(any(a.startswith("'"+n+"' ") and 'sorryAx' not in a for a in d['print_axioms']) for n in names)
 ps=[dict(receipt=str(p.relative_to(R)),receipt_sha256=sha(p.read_bytes()),theorems=names)]
 fn='crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::reduce';review=E/'NEB_PRIVATE_REDUCER_ASSOCIATION.md';rev=dict(path=str(review.relative_to(R)),sha256=sha(review.read_bytes()),conclusion_hiding=False,statement_and_native_association_checked=True);native=E/'NEB_PRIVATE_REDUCE_REVIEW.json';nr=dict(path=str(native.relative_to(R)),sha256=sha(native.read_bytes()));rows={}
 for r in base['rows']:
  if r['function']!=fn:continue
  assert not any('callee' in o for o in r['caller_domain_obligations'])
  ext={}
  for o in r['caller_domain_obligations']:
   call=o['call'];assert call.get('expression',call.get('syntax'))=='u64::from'
   ext[o['id']]=dict(kind='LOSSLESS_PRIVATE_MODULUS_CAST',syntax='u64::from',line=call['line'],caller_body_sha256=r['frozen_body_sha256'],source_value=2147483647,theorems=['NEB_PrivateReducer.constant_cast','NEB_PrivateReducer.frame'],native_review=nr)
  assert sorted(c['line'] for c in ext.values())==[11,12,13,13]
  rows[r['row']]=dict(id='NEB-private-reducer-root:'+r['row'],row=r['row'],function=fn,frozen_body_sha256=r['frozen_body_sha256'],selected_claims=r['selected_claims'],named_hypotheses_discharged=[h['name'] for h in r['named_hypotheses']],inventory_domains_discharged=[o['unit'] for o in r['inventory_domain_obligations']],parts=['result','state','ordered_effects','native_association'],lean_evidence=ps,remaining_inner_hypotheses=[],top_hypotheses=[fn+'.PacketDomain',fn+'.PhysicalInterpretation','NativeContractSemanticTransport'],review=rev,native_review=nr,external_obligations=ext)
 return {},rows
