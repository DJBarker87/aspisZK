"""Capture checked sibling ledger states without altering inherited checks.

The NEO/NET replay checks run unchanged. A read-only Python return profiler
captures NEO's already checked local `out`; NET's four exact validated parser
recipes are then applied by the same additive row rules, with new checks.
"""
from pathlib import Path
import json,hashlib,lzma,sys,copy
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
C=E/'.NEV_net_capsule/evidence/slice-q-compose3-20261102'
sys.path.insert(0,str(C));import NET_validate as net
neo=net.neo
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def run():
 captured=[]
 def profile(frame,event,arg):
  if event=='return' and frame.f_code is neo.compose.__code__:captured.append(frame.f_locals['out'])
 sys.setprofile(profile)
 try:delta=neo.compose(neo.baseline(),neo.obj(neo.E/'NEO_PEER_POSITIVE.json'),neo.obj(neo.E/'NEO_EDGES.json'))
 finally:sys.setprofile(None)
 assert delta==neo.obj(neo.E/'NEO_LEDGER_DELTA.json') and len(captured)==1
 out=copy.deepcopy(captured[0]);index={r['row']:r for r in out['rows']}
 certificates=obj(C/'NET_CERTIFICATES.json');edges=obj(C/'NET_EDGES.json')
 checked=net.validate(edges,certificates,replay=False)
 assert checked==obj(C/'NET_LEDGER_DELTA.json')
 for certificate in sorted(certificates,key=lambda c:"QM31::from_le_bytes" in c["function"]):
  row=index[certificate['row']];assert row['composed_status']=='OPEN'
  assert row['function']==certificate['function'] and row['frozen_body_sha256']==certificate['frozen_body_sha256']
  before=copy.deepcopy(row);identity=certificate['id'];claim='NET::'+certificate['function']
  row.update(NEV_NET_before=before,NET_certificate=certificate,bridge_status='CLOSED-CONDITIONAL',composed_status='CLOSED',selected_claims=[claim],claim_ids=before['claim_ids']+[claim],open_transitive_dependencies=[],active_support_receipts=certificate['native_pair']+[certificate['frame_control']],k3_status='UNAFFECTED',NEN_rejections=[])
  row['named_hypotheses']=[dict(name=claim+'.'+kind,statement=certificate['domain'],discharged_by=identity) for kind in ['PacketDomain','PhysicalInterpretation']]
  for obligation in row['inventory_domain_obligations']:obligation.update(status='CLOSED',discharged_by=identity)
  for obligation in row['caller_domain_obligations']:
   if 'callee' in obligation:
    assert obligation['callee']==certificate['callee']
    assert all(r['composed_status']=='CLOSED' for r in out['rows'] if r['function']==certificate['callee'])
    assert row['function']+' -> '+certificate['callee'] in {e['edge'] for e in edges['edges'] if e['status']=='CLOSED'}
   else:assert obligation['id'] in certificate['external_obligations']
   obligation.update(status='CLOSED',discharged_by=identity+':'+obligation['id'])
 assert sum(r['composed_status']=='CLOSED' for r in out['rows'])==134
 payload=json.dumps(out,separators=(',',':')).encode();raw=lzma.compress(payload,preset=6)
 (E/'NEV_NET_BASELINE.json.xz').write_bytes(raw)
 (E/'NEV_NET_BASELINE.json.sha256').write_text(hashlib.sha256(payload).hexdigest()+'\n')
 (E/'NEV_NET_BASELINE_REVIEW.json').write_text(json.dumps(dict(status='CHECKED_ADDITIVE_NET_BASELINE',neo_validator_sha256=sha(neo.E/'NEO_validate.py'),net_validator_sha256=sha(C/'NET_validate.py'),neo_checks_unchanged=True,net_checks_unchanged=True,capture='Read-only Python return profiler; no inherited code or condition changed',rows_closed=134,source_revision=obj(E/'NEV_NET_PROVENANCE.json')['revision'],compressed_sha256=hashlib.sha256(raw).hexdigest()),indent=2)+'\n')
 own=obj(E/'NEV_DERIVED_LEDGER.json');a={r['row']:r for r in out['rows'] if r['composed_status']=='CLOSED'};b={r['row']:r for r in own['rows'] if r['composed_status']=='CLOSED'}
 print('NEV-only',[(k,b[k]['function']) for k in sorted(b.keys()-a.keys())])
 print('NET-only',len(a.keys()-b.keys()))
 return out
if __name__=='__main__':run()
