#!/usr/bin/env python3
"""Immutable exact source inclusion, never an owned replacement."""
import hashlib,json,pathlib,subprocess
R=pathlib.Path(__file__).resolve().parents[2]; B=pathlib.Path(__file__).resolve().parent
K=B/'Port23PUSH-native'; E=R/'evidence/port23push-20261024'
REV='3166426e45d8c1eb2ce8b6201f7198c0536aa2c5'
sha=lambda b:hashlib.sha256(b).hexdigest(); pins=[]
def save(src,dest,a=None,z=None,suffix=b''):
 data=subprocess.check_output(['git','show',REV+':'+src],cwd=R); lines=data.splitlines(keepends=True)
 a=a or 1; z=z or len(lines); span=b''.join(lines[a-1:z]); p=K/dest
 p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(span+suffix)
 pins.append(dict(source=src,whole_sha256=sha(data),whole_bytes=len(data),start_line=a,end_line=z,span_sha256=sha(span),destination=dest,suffix=suffix.decode()))
save('crates/aspis-core/src/field.rs','src/field.rs')
save('crates/aspis-core/src/field/wide_exact.rs','src/field/wide_exact.rs')
v='crates/aspis-r1-cost-probe/src/verifier.rs'
save(v,'src/carrier.rs',204,204)
save(v,'src/push.rs',216,220)
save(v,'src/update.rs',230,245)
(K/'Cargo.toml').write_text('''[package]
name = "port23push-native"
version = "0.0.0"
edition = "2021"
[workspace]
[profile.release]
opt-level = 3
debug = 0
overflow-checks = true
''')
(K/'src/lib.rs').write_text('''#![allow(non_snake_case, unexpected_cfgs, private_interfaces)]
extern crate alloc;
pub mod field;
pub mod verifier {
    use super::field::{QM31 as K, M31};
    use alloc::vec::Vec;
    include!("carrier.rs");
    impl BatchedWeights {
        include!("push.rs");
    }
    include!("update.rs");
    pub fn Port23PUSH_push(b: &mut BatchedWeights,index:usize,power:K,basis:M31) {
        b.push(index,power,basis)
    }
}
''')
# include! cannot expand to impl items on all Rust versions. Assemble only the
# enclosing impl syntax around the exact unchanged method span.
p=K/'src/lib.rs';p.write_text(p.read_text().replace('        include!("push.rs");',(K/'src/push.rs').read_text().rstrip()))
result=dict(source_revision=REV,source_inclusions=pins,kit={str(p.relative_to(K)):dict(sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in sorted(K.rglob('*')) if p.is_file()},scope='exact mutable push and update graph; unchanged full field carriers; enclosing syntax and direct free root only')
(E/'source-pins.json').write_text(json.dumps(result,indent=2)+'\n')
