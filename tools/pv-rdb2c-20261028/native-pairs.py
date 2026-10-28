from pathlib import Path
import os,json,subprocess,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028');P=D/'weights-fixture';S=D.parent/'codex-pv-rdb2-20261028/src'
s='''extern crate alloc;
pub use aspis_r1_cost_probe::{weights,transport,verifier};
#[path="POWERS"]pub mod prover_powers;
#[path="HOST"]pub mod owned;
use aspis_core::field::{QM31 as K,WideExact as E,CM31,M31,P};
use aspis_core::circle::SecureCirclePoint;
use transport::Variant;
fn main(){let raw=K{c0:CM31{a:M31(u32::MAX),b:M31(P)},c1:CM31{a:M31(P+1),b:M31(P-1)}};let z=[SecureCirclePoint{x:K::ONE,y:K::ZERO};2];let mut cases=0u64;let mut raw_checks=0u64;
for alpha in [[K::ZERO;10],[K::ONE;10],[raw;10]] {for variant in [Variant::S1,Variant::S2,Variant::D] {
let a=owned::Weights::new(variant,&alpha,&z).unwrap();let b=weights::Weights::new(variant,&alpha,&z).unwrap();assert_eq!(a.factors,b.factors);assert_eq!(a.points,b.points);assert_eq!(a.extra,b.extra);
for kind in 0..7 {for j in 0..1024 {assert_eq!(a.raw(kind,j),b.raw(kind,j));raw_checks+=1;}}
let kappa=E::from_limbs([2,3,4,5,6,7,8,9]).unwrap();let mut out=[E::ONE;1024];a.materialize(kappa,&mut out).unwrap();let expected=b.materialize(kappa).unwrap();assert_eq!(out.as_slice(),expected.as_slice());cases+=1;
}}
for variant in [Variant::S1,Variant::S2,Variant::D] {let a=owned::Weights{variant,factors:[[[K::ONE;4];5];5],points:[[K::ONE;10];3],extra:[K::ONE;2]};let b=weights::Weights{variant,factors:a.factors,points:a.points,extra:a.extra};let mut out=[E::ZERO;1024];a.materialize(E::ONE,&mut out).unwrap();assert_eq!(out.as_slice(),b.materialize(E::ONE).unwrap().as_slice());cases+=1;}
println!("finite deployed-source/owned comparisons: {cases} complete1024-element outputs; {raw_checks} raw-cell comparisons; constructor factors/points/extra matched; includes noncanonical raw words; no disagreement");}
'''.replace('POWERS',str(S/'crates/aspis-r1-cost-probe/src/prover_powers.rs')).replace('HOST',str(S/'crates/aspis-r1-cost-probe/src/host_weights.rs'))
(P/'pairs.rs').write_text(s);m=(P/'Cargo.toml').read_text();assert 'name="pairs"' not in m;m+='\n[[bin]]\nname="pairs"\npath="pairs.rs"\n';(P/'Cargo.toml').write_text(m)
j=json.loads((D/'deployed-native-inputs.json').read_text());j.update(fixture_sha256=hashlib.sha256(s.encode()).hexdigest(),sources=[dict(path=p,sha256=hashlib.sha256((S/p).read_bytes()).hexdigest()) for p in ['crates/aspis-r1-cost-probe/src/weights.rs','crates/aspis-r1-cost-probe/src/host_weights.rs','crates/aspis-r1-cost-probe/src/prover_powers.rs']],evidence_class='finite validation; original and owned references compiled without body edits',expected_phase='optimized fixture compile, then full source/owned same-input field/output comparisons')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'target-weights'),CARGO_BUILD_JOBS='4',RUSTC_BOOTSTRAP='1',RUSTFLAGS='-Zdump-mir=box_from_parts -Zdump-mir-dir='+str(D/'box-mir')+' --emit=llvm-ir,link');cmd=['cargo','run','--manifest-path',str(P/'Cargo.toml'),'--release','--locked','--bin','pairs','-j','4'];j['command']=cmd;(D/'deployed-pairs-inputs.json').write_text(json.dumps(j,indent=2));print('expected phase: optimized fixture compile then complete source/owned finite comparisons',flush=True);raise SystemExit(subprocess.run(cmd,env=env).returncode)
