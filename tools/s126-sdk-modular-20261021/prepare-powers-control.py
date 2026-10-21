#!/usr/bin/env python3
"""Parametric control certificate, not an opaque arithmetic installation claim."""
from pathlib import Path
import re,subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=True);REV='b2727acd3abf79315d18b754a260f58f4b1c6326'
p='crates/aspis-r1-cost-probe/src/weights.rs';src=subprocess.check_output(['git','-C',str(R),'show',REV+':'+p],text=True);a=src.index('pub fn powers<');end=src.index('\n',a);original=src[a:end]
patch=(R/'docs/research/100bit-spend-path-20261013/lean-candidates/s1-claim-fission-sum-proved-candidate-20261020/powers-early.patch').read_text();candidate='\n'.join(line[1:] for line in patch.splitlines() if line.startswith('+') and not line.startswith('+++'));candidate=candidate.replace('pub fn powers<','pub fn candidate_powers<',1)
code='''#![allow(dead_code,static_mut_refs)]
use aspis_core::field::WideExact as E;
'''+original+'\n'+candidate+'''
#[cfg(kani)] mod proofs {
use super::*;
static mut TABLE:[E;29]=[E::ZERO;29];
static mut X:E=E::ZERO;
static mut COUNT:usize=0;
// This stream overapproximates any total pure concrete multiplication. The
// original's final unused multiply is allowed; purity/totality must be supplied
// by the independently checked actual arithmetic before declaring equivalence.
pub fn stream_mul(left:E,right:E)->E {
 let i=unsafe{COUNT};assert!(i<29);
 assert!(right==unsafe{X});
 assert!(left==if i==0 {E::ONE}else{unsafe{TABLE[i-1]}});
 unsafe{COUNT=i+1;TABLE[i]}
}
fn certificate<const N:usize>() {
 let table:[[u32;8];29]=kani::any();let input:[u32;8]=kani::any();
 // Full actual enum-free field carriers; every u32 pattern is a valid Rust
 // value. Arithmetic invariants are intentionally not assumed by this control
 // certificate and are not established by this transmute.
 let table:[E;29]=unsafe{std::mem::transmute(table)};let x:E=unsafe{std::mem::transmute(input)};
 unsafe{TABLE=table;X=x;COUNT=0;}
 let original=powers::<N>(x);assert_eq!(unsafe{COUNT},N);
 unsafe{COUNT=0;}
 let candidate=candidate_powers::<N>(x);assert_eq!(unsafe{COUNT},N.saturating_sub(1));
 assert!(original==candidate);
 kani::cover!(input[0]==0,"zero leading limb reaches comparison");kani::cover!(input[0]==u32::MAX,"maximum leading limb reaches comparison");
}
#[kani::proof]
#[kani::unwind(64)]
#[kani::stub(aspis_core::field::wide_exact::WideExact::mul,stream_mul)]
fn powers7_control(){certificate::<7>();}
#[kani::proof]
#[kani::unwind(64)]
#[kani::stub(aspis_core::field::wide_exact::WideExact::mul,stream_mul)]
fn powers29_control(){certificate::<29>();}
#[kani::proof]
#[kani::unwind(64)]
#[kani::stub(aspis_core::field::wide_exact::WideExact::mul,stream_mul)]
fn powers0_control(){certificate::<0>();}
}
'''
(O/'src/lib.rs').write_text(code);(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-powers-control"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
aspis-core={path="/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/crates/aspis-core",features=["r0"]}
[profile.release]
opt-level=3
overflow-checks=true
''')
sha=lambda s:hashlib.sha256(s.encode()).hexdigest();(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',freeze=REV,path=p,source_sha256=sha(src),original=original,original_sha256=sha(original),candidate=candidate,candidate_sha256=sha(candidate),code_sha256=sha(code),qualification='Parametric original/candidate callback-control and full actual carrier certificate at N0,N7,N29. Actual multiplication is an explicit total-pure child contract; this result alone does not install it or prove whole source equivalence.'),indent=2)+'\n')
