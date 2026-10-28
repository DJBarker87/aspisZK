from pathlib import Path
import os,json,subprocess,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028');P=D/'weights-fixture'
s='''use aspis_core::field::{QM31 as Q,CM31,M31};
use aspis_statement::constraints_v4::multilinear_evaluate_qm31 as native;
fn q(a:u32,b:u32,c:u32,d:u32)->Q{Q{c0:CM31{a:M31(a),b:M31(b)},c1:CM31{a:M31(c),b:M31(d)}}}
fn next(s:&mut u64)->u32{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;(*s%2147483647)as u32}
fn random(s:&mut u64)->Q{q(next(s),next(s),next(s),next(s))}
fn dense(column:&[Q],point:&[Q;10])->Option<Q>{if column.len()!=1024{return None}let mut sum=Q::ZERO;for row in 0..1024 {let mut w=Q::ONE;for d in 0..10 {w=w.mul(if (row>>(9-d))&1==0{Q::ONE.sub(point[d])}else{point[d]});}sum=sum.add(w.mul(column[row]));}Some(sum)}
fn main(){let mut s=0x52444232433239u64;let mut count=0;
for prefix in 0..=10 {for pattern in 0..7 {let point=core::array::from_fn(|d|if d<prefix{random(&mut s)}else if (pattern>>(d%3))&1==0{Q::ZERO}else{Q::ONE});
for kind in 0..4 {let column:Vec<Q>=(0..1024).map(|row|match kind{0=>q((row*3+7)as u32,0,0,0),1=>if row==pattern*137%1024{Q::ONE}else{Q::ZERO},2=>random(&mut s),_=>q(row as u32,(1023-row)as u32,(row^341)as u32,((row*31337)%2147483647)as u32)}).collect();
assert_eq!(native(&column,&point),dense(&column,&point),"prefix={prefix} pattern={pattern} column={kind}");count+=1;}
}}
for n in [0,1,1023,1025] {let c=vec![Q::ONE;n];assert!(native(&c,&[Q::ONE;10]).is_none());}
println!("finite validation only: {count} nonconstant-column/native-dense pairs, all 11 trailing-Boolean prefix lengths; 4 wrong-length checks; canonical carriers; no universal or arbitrary-raw-carrier proof claimed");}
''';(P/'v239.rs').write_text(s)
m=(P/'Cargo.toml').read_text();assert 'name="v239"' not in m;m+='\n[[bin]]\nname="v239"\npath="v239.rs"\n';(P/'Cargo.toml').write_text(m)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'target-weights'),CARGO_BUILD_JOBS='4',RUSTC_BOOTSTRAP='1',RUSTFLAGS='-Zdump-mir=box_from_parts -Zdump-mir-dir='+str(D/'box-mir'))
cmd=['cargo','run','--release','--locked','--manifest-path',str(P/'Cargo.toml'),'--bin','v239','-j','4']
j=json.loads((D/'weights-inputs.json').read_text());j.update(command=cmd,fixture_sha256=hashlib.sha256(s.encode()).hexdigest(),expected_phase='optimized fixture compilation then 308 native/dense finite pairs; field elimination is not involved',allocator_instrumentation='none for this binary',evidence_class='finite validation only')
(D/'v239-inputs.json').write_text(json.dumps(j,indent=2));print('expected time: optimized fixture compile then native/dense pairs',flush=True)
sys_exit=subprocess.run(cmd,env=env).returncode;raise SystemExit(sys_exit)
