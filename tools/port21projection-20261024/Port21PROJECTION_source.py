#!/usr/bin/env python3
"""Immutable exact-source helper kit; no std/allocator/Drop substitution."""
import hashlib, json, pathlib, subprocess
R=pathlib.Path(__file__).resolve().parents[2]
B=R/'tools/port21projection-20261024'; K=B/'Port21PROJECTION-native'
def sha(b):return hashlib.sha256(b).hexdigest()
pins=[]
def save(src,dest,start=None,end=None):
    data=subprocess.check_output(['git','show','e2747dd63d2468cff93d5c76880234c5c710defe:'+src],cwd=R); lines=data.splitlines(keepends=True)
    a=start or 1; z=end or len(lines); body=b''.join(lines[a-1:z])
    p=K/dest;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(body)
    pins.append(dict(source=src,whole_sha256=sha(data),whole_bytes=len(data),
                     start_line=a,end_line=z,span_sha256=sha(body),destination=dest))
save('crates/aspis-core/src/r0/heap.rs','src/r0/heap.rs')
save('crates/aspis-core/src/field.rs','src/field.rs')
save('crates/aspis-core/src/field/wide_exact.rs','src/field/wide_exact.rs')
# Real error carrier, including all variants; no Allocation-only surrogate.
src='crates/aspis-core/src/r0/mod.rs'; ls=(R/src).read_text().splitlines()
a=next(i+1 for i,l in enumerate(ls) if l.startswith('#[derive(Clone, Copy, Debug, PartialEq, Eq)]'))
z=next(i+1 for i,l in enumerate(ls) if i>=a and l=='}')
save(src,'src/r0/error.rs',a,z)
save('crates/aspis-r1-cost-probe/src/verifier.rs','src/verifier_error.rs',19,27)
save('crates/aspis-r1-cost-probe/src/verifier.rs','src/accumulator.rs',91,95)
save('crates/aspis-r1-cost-probe/src/verifier.rs','src/pending.rs',204,215)
save('crates/aspis-r1-cost-probe/src/transport.rs','src/variant.rs',2,9)
(K/'Cargo.toml').write_text('''[package]
name = "port21projection-native"
version = "0.0.0"
edition = "2021"
[workspace]
[profile.release]
opt-level = 3
debug = 0
overflow-checks = true
''')
(K/'src/lib.rs').write_text('''#![allow(non_snake_case, unexpected_cfgs)]
extern crate alloc;
extern crate self as aspis_core;
pub mod field;
pub mod r0 {
    include!("r0/error.rs");
    pub mod heap;
}
pub mod transport {
    include!("variant.rs");
    // Only closes the source impl after final_len; row/permutation methods
    // are outside this call cone. No existing function body is edited.
}
pub mod verifier {
    use super::{field::{QM31 as K, WideExact as E},transport::Variant};
    use alloc::vec::Vec;
    include!("verifier_error.rs");
    include!("accumulator.rs");
    include!("pending.rs");
    // Job-only entry roots, after exact unchanged parent bodies.
    pub fn Port21PROJECTION_acc(v: Variant) -> Result<Accumulator,Error> { Accumulator::new(v) }
    pub fn Port21PROJECTION_rows(weights: &[K]) -> Result<(Vec<[u64;4]>,usize),Error> {
        let b = BatchedWeights::new(weights)?;
        Ok((b.raw,b.terms))
    }
}
// Monomorphizations only. The included generic helper and all Copy/Clone
// implementations are the unmodified source. No allocator or std stub.
pub fn Port21PROJECTION_qm31(n: usize, value: field::QM31) -> Result<alloc::vec::Vec<field::QM31>,r0::Error> {
    r0::heap::filled(n,value)
}
pub fn Port21PROJECTION_row(n: usize, value: [u64;4]) -> Result<alloc::vec::Vec<[u64;4]>,r0::Error> {
    r0::heap::filled(n,value)
}
''')
# include! requires balanced items: append only the omitted enclosing braces.
for name in ['variant.rs','pending.rs']:
    p=K/'src'/name;p.write_bytes(p.read_bytes()+b'}\n')
result=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
            source_inclusions=pins,kit={str(p.relative_to(K)):dict(sha256=sha(p.read_bytes()),bytes=p.stat().st_size)
            for p in sorted(K.rglob('*')) if p.is_file()},
            scope='unchanged filled, exact parent constructor spans, real full QM31 and ArrayU64[4]; enclosing braces only; no stubs')
(R/'evidence/port21projection-20261024/source-pins.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
