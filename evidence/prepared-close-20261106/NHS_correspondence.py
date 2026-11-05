"""Owned source-fission checks. No compilation and no shared source mutation."""
from pathlib import Path
import subprocess,json,hashlib,re
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
frozen=subprocess.check_output(['git','show',rev+':crates/aspis-r1-cost-probe/src/verifier.rs']).decode()
s=(E/'NHS_pending.rs.txt').read_text();compact=lambda x:re.sub(r'\s+','',x)
body=frozen.split('while index<weights.len() {',1)[1].split('}',1)[0]
ours=s.split('fn pending_step(',1)[1].split('{',1)[1].split('index\n}',1)[0]
assert compact(body)==compact(ours)
assert 'Ok(Self{raw,terms:0})' in compact(frozen)
assert 'fnpending_return(raw:Vec<[u64;4]>)->BatchedWeights{BatchedWeights{raw,terms:0}}' in compact(s)
assert 'letmutraw=aspis_core::r0::heap::filled(weights.len(),[0u64;4]).map_err(|_|Error::Allocation)?;letmutindex=0;' in compact(frozen)
assert 'letraw=reply.map_err(|_|Error::Allocation)?;letindex=0;' in compact(s)
assert 'ifindex<weights.len(){next=pending_step(&weights,&mutraw,index);continued=true;}' in compact(s)
assert 'static mut' not in s and not re.search(r'\b(static|stub_verified|proof_for_contract)\b',s)
assert not re.search(r'Option\s*<\s*fn|fn\s*\(',s)
assert '#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]' in s
assert hashlib.sha256((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
u=json.loads((E/'NHS_NATIVE_UPLOAD.json').read_text())
for n,text in u.items():
 if n.endswith('/NHS_pending.rs'):assert text==s
 elif n.endswith('/lib.rs'):assert text=='#![cfg_attr(kani, feature(allocator_api))]\n'+subprocess.check_output(['git','show',rev+':'+n]).decode()
 else:assert text==frozen+'\n#[cfg(kani)] #[path="NHS_pending.rs"] mod NHS_pending;\n'
report=dict(status='PASS',frozen_revision=rev,frozen_verifier_sha256=hashlib.sha256(frozen.encode()).hexdigest(),harness_sha256=hashlib.sha256(s.encode()).hexdigest(),patch_sha256=hashlib.sha256((E/'NHS_native.patch').read_bytes()).hexdigest(),checks=['literal native iteration','literal final record','allocation prefix fission','literal exit guard','no field multiply or SHA','no writable static or function pointer','exact KMX','frozen functions unchanged'],native_domain='TX1 initial zero64 weights; arbitrary raw64/index/window; selected weight unrestricted; no general TX2 claim')
(E/'NHS_CORRESPONDENCE.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps(report))
