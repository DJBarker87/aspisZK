"""Revalidate the authoritative adopted square-loop packet; no new Kani credit."""
from pathlib import Path
import json,subprocess,hashlib,sys,re
E=Path(__file__).resolve().parent;R=E.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();obj=lambda p:json.loads(p.read_text());read=lambda p:subprocess.check_output(['git','show','HEAD:'+p],cwd=R)
B=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');assert sha((E.parent/'native-ledger3-20261029/NDT_LEDGER.json').read_bytes())==obj(E/'NEB_SCOPE.json')['ledger_sha256'];fn='crates/aspis-core/src/field.rs::square_n';rows=[r for r in B['rows'] if r['function']==fn];assert len(rows)==2
for r in rows:
 assert r['bridge_status']=='CLOSED-CONDITIONAL' and r['frozen_body_verified'] and not r['no_credit_reason']
 assert all(p['status']=='SAME BODIES' for p in r['feature_parity'])
 raw=subprocess.check_output(['git','show',B['frozen_revision']+':'+r['source_file']],cwd=R);a,b=r['frozen_body_byte_range'];body=raw[a:b];assert sha(body)==r['frozen_body_sha256'] and sha(raw)==r['source_file_sha256']
 assert b'fn square_n(mut value: M31, count: usize) -> M31 ' in raw[max(0,a-70):a]
 assert re.search(rb'\{\s*for _ in 0\.\.count \{\s*value = value.mul\(value\);\s*\}\s*value\s*\}',body)
 assert not any(s in body for s in [b'clone',b'copy_',b'Option<fn',b'Vec',b'alloc',b'unsafe'])
 for p,h in r['receipt_sha256'].items():assert sha(read(p))==h
packet='evidence/native-tx2c-20261027/';d=json.loads(read(packet+'NBG_K028/receipt.json'));g=json.loads(read(packet+'NBG_K028-graph-check.json'));patch=read(packet+'NBG_K028-harness.patch').decode()
assert d['exit_status']==0 and d['swaps']=='0' and d['env']['CARGO_NET_OFFLINE']=='true' and d['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
assert g['graph_matches_frozen'] and g['resolved_packages']==441 and not g['edge_errors'] and not g['new_package_tuples']
lock=sha(subprocess.check_output(['git','show',B['frozen_revision']+':Cargo.lock'],cwd=R));assert g['lock_sha256']==d['source_hashes']['NBG_src/Cargo.lock']==lock
# Historical post-lock/graph acceptance is inherited from the authoritative
# adopted NDT packet, not invented as a new historical gate or new native run.
for s in ['let start:usize=kani::any();let end:usize=kani::any();let mut iter=start..end;','let mut value=super::M31(kani::any());','let next=iter.next();','value=value.mul(value);','assert!(iter.start==start+1&&iter.end==end);','assert!(iter.start==start&&iter.end==end);','assert!(NBG_MUL_CALLS==1);','assert!(NBG_MUL_CALLS==0);','kani::assume((r as u64)==((x.0 as u64)*(y.0 as u64))%(super::P as u64));']:assert s in patch
fragment=patch[patch.index('+static mut NBG_PRODUCT'):];assert not any(s in fragment for s in ['copy_from_slice','copy_nonoverlapping','clone','to_vec','Option<fn','stub_verified','proof_for_contract'])
assert 'VERIFICATION:- SUCCESSFUL' in read(packet+'NBG_K028/stdout.log').decode()
out=dict(schema='NEB-square-adopted-native-review-v1',function=fn,adopted_claim=rows[0]['selected_claims'],authoritative_ledger_sha256=obj(E/'NEB_SCOPE.json')['ledger_sha256'],frozen_body_sha256=rows[0]['frozen_body_sha256'],native_receipt_sha256=sha(read(packet+'NBG_K028/receipt.json')),native_patch_sha256=sha(patch.encode()),graph_sha256=sha(read(packet+'NBG_K028-graph-check.json')),new_native_attempts=0,copy_dependency=False,function_pointer_dependency=False,actual_iteration='arbitrary Range start/end; exact next reply, increment/end or stop; same raw value twice, one exact product reply; no whole loop unwind',domain='Every typed raw u32 and machine count; no canonical input strengthening; zero count returns the same raw word',field_stub_pair='NBG_product -> NEB_SquareComposition.cell / LPf_BaseMultiply.source, domain all raw u32 pairs; exact natural mod P and canonical reply',trust='Existing adopted hybrid P6/D188 transport; option-A RECLASSIFICATION, never removal',excluded='NBC_L001 historical failure; no inverse zero-panic or whole inverse native credit; no new Kani PASS or retrospective gate claimed')
p=E/'NEB_SQUARE_REVIEW.json'
if '--check' in sys.argv:assert obj(p)==out
else:p.write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps(dict(adopted_square_occurrences=len(rows),new_native_attempts=0)))
