"""Adopted scalar private reducer packet; independent of dot/copy state."""
from pathlib import Path
import json,subprocess,hashlib,sys
E=Path(__file__).resolve().parent;R=E.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();obj=lambda p:json.loads(p.read_text());read=lambda p:subprocess.check_output(['git','show','HEAD:'+p],cwd=R)
B=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');assert sha((E.parent/'native-ledger3-20261029/NDT_LEDGER.json').read_bytes())==obj(E/'NEB_SCOPE.json')['ledger_sha256'];fn='crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::reduce';rows=[r for r in B['rows'] if r['function']==fn];assert len(rows)==2
for r in rows:
 assert r['bridge_status']=='CLOSED-CONDITIONAL' and r['frozen_body_verified'] and not r['no_credit_reason'] and all(p['status']=='SAME BODIES' for p in r['feature_parity'])
 raw=subprocess.check_output(['git','show',B['frozen_revision']+':'+r['source_file']],cwd=R);a,b=r['frozen_body_byte_range'];body=raw[a:b];assert sha(body)==r['frozen_body_sha256'] and sha(raw)==r['source_file_sha256']
 assert body.count(b'u64::from(P)')==4 and b'x=(x & u64::from(P))+(x>>31u32);' in body
 assert not any(s in body for s in [b'clone',b'copy_',b'Option<fn',b'Vec',b'alloc',b'unsafe',b'[' , b'::mul'])
 for p,h in r['receipt_sha256'].items():assert sha(read(p))==h
packet='evidence/native-tx2h-20261028/';d=json.loads(read(packet+'NBQ_K001/receipt.json'));g=json.loads(read(packet+'NBQ_K001-graph-check.json'));patch=read(packet+'NBQ_K001-harness.patch').decode();log=read(packet+'NBQ_K001/stdout.log').decode()
assert d['exit_status']==0 and d['swaps']=='0' and d['env']['CARGO_NET_OFFLINE']=='true' and d['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
assert g['graph_matches_frozen'] and g['resolved_packages']==441 and not g['edge_errors'] and not g['new_package_tuples']
lock=sha(subprocess.check_output(['git','show',B['frozen_revision']+':Cargo.lock'],cwd=R));assert g['lock_sha256']==d['source_hashes']['NBQ_src/Cargo.lock']==lock
assert 'fast_pairing::canonical::NBQ_private::reduce_all' in d['command']
assert 'fn reduce_all()' in patch and 'let x:u64=kani::any();' in patch and 'reduce(x)' in patch and 'assert!(u64::from(r)==x%u64::from(P));' in patch
assert 'VERIFICATION:- SUCCESSFUL' in log
out=dict(schema='NEB-private-scalar-adopted-review-v1',function=fn,frozen_body_sha256=rows[0]['frozen_body_sha256'],authoritative_ledger_sha256=obj(E/'NEB_SCOPE.json')['ledger_sha256'],native_receipt_sha256=sha(read(packet+'NBQ_K001/receipt.json')),native_patch_sha256=sha(patch.encode()),new_native_attempts=0,domain='Every U64; independent of private Q, slice width, count or dot history',native_method='Inherited authoritative plain scalar assertion, not proof_for_contract/stub_verified; exact natural mod P; no reached aggregate copy or fn-pointer',copy_dependency=False,field_multiplication_in_kani=False,trust='Previously adopted native helper packet and SAME BODIES feature association; option-A semantic transport is RECLASSIFICATION, never removal',exclusions='All historical failed support receipts excluded. Other NBQ private-Q/dot carrier copy claims are not promoted. No new or retrospective native gate claimed.')
p=E/'NEB_PRIVATE_REDUCE_REVIEW.json'
if '--check' in sys.argv:assert obj(p)==out
else:p.write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps(dict(adopted_scalar_occurrences=len(rows),new_native_attempts=0)))
