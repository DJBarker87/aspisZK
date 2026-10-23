from pathlib import Path
import hashlib,json
E=Path('docs/research/100bit-spend-path-20261013/evidence/prover-commit49-20261022');P=E.parent/'prover-commit48-20261022'
D=E/'native';D.mkdir(exist_ok=True)
s=(P/'native/lib.rs').read_text();s=s[:s.index('include!("iterations.rs")')]
s+='''
#[derive(Clone,Copy)] struct M31(u32);
fn native_tail(mut point:[E;10],r:usize,remaining:usize,assignment:usize,offset:usize)->[E;10] {
 point[r+1+offset]=if (assignment>>(remaining-1-offset))&1==0 {E(0)} else {E::ONE};point
}
fn owner_tail(mut point:[E;10],round:usize,remaining:usize,assignment:usize,offset:usize)->[E;10] {
 point[round+1+offset]=if (assignment>>((remaining-1-offset) as u32))&1==0 {E(0)} else {E::ONE};point
}
fn native_sum(value:E,oracle:Result<E,u8>)->Result<E,u8> {Ok(value.add(oracle?))}
fn owner_sum(value:E,oracle:Result<E,u8>)->Result<E,u8> {match oracle {Err(e)=>Err(e),Ok(x)=>Ok(value.add(x))}}
fn native_shift(mut polys:[[E;28];10],original:E,eta:E,term0:E,inv:E,half:E)->[[E;28];10] {
 let c=original.sub(eta.mul(term0)).mul(inv);
 polys[9][0]=polys[9][0].sub(c.mul(half));
 polys[9][1]=polys[9][1].add(c);polys
}
fn owner_shift(mut p:[E;28],original:E,eta_term0:E,inv:E,half:E)->[E;28] {
 let c=original.sub(eta_term0).mul(inv);
 p[0]=p[0].sub(c.mul(half));
 p[1]=p[1].add(c);p
}
#[cfg(kani)] mod proofs {
 use super::*;
 #[kani::proof] #[kani::unwind(12)] fn tail_transition() {
  let raw:[u32;10]=kani::any();let p:[E;10]=unsafe {core::mem::transmute(raw)};
  let r:usize=kani::any();let n:usize=kani::any();let a:usize=kani::any();let o:usize=kani::any();
  kani::assume(r<10 && n==9-r && o<n && a<(1usize<<n));
  assert_eq!(native_tail(p,r,n,a,o),owner_tail(p,r,n,a,o));
 }
 #[kani::proof] #[kani::unwind(12)] fn oracle_sum_transition() {
  let v=E(kani::any());let x=E(kani::any());let err:u8=kani::any();let fail:bool=kani::any();
  let oracle=if fail {Err(err)}else{Ok(x)};let answers=kani::any();
  reset(answers);let a=native_sum(v,oracle);let ta=trace();
  reset(answers);let b=owner_sum(v,oracle);let tb=trace();
  assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,if fail {0}else{1});
 }
 #[kani::proof] #[kani::unwind(282)] fn final_shift() {
  let raw:[[u32;28];10]=kani::any();let p:[[E;28];10]=unsafe {core::mem::transmute(raw)};
  let original=E(kani::any());let eta=E(kani::any());let term0=E(kani::any());let inv=E(kani::any());let half=E(kani::any());let answers=kani::any();
  reset(answers);let a=native_shift(p,original,eta,term0,inv,half);let ta=trace();
  reset(answers);let eta_term0=eta.mul(term0);let row=owner_shift(p[9],original,eta_term0,inv,half);let tb=trace();
  let mut b=p;b[9]=row;assert_eq!(a,b);assert_eq!(ta,tb);assert_eq!(ta.1,6);
 }
}
'''
(D/'lib.rs').write_text(s)
(D/'Cargo.toml').write_text('[package]\nname="simulator-native49"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
src=Path('crates/aspis-r1-cost-probe/src/sim.rs');text=src.read_text()
spans={}
for name,a,b in [('tail','                for offset in 0..remaining {','                *value=value.add(f(&point)?);'),('shift','        let c=original.sub(ch.eta.mul(term0(&alpha)?)).mul(inv);','    }\n    if ablation==Ablation::None')]:
 start=text.index(a);end=text.index(b,start);spans[name]=dict(start_line=text[:start].count('\n')+1,end_line=text[:end].count('\n'),literal=text[start:end])
(E/'pins/native-spans.json').write_text(json.dumps(dict(source=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest(),spans=spans,abstractions=['K => opaque u32 handle with universal symbolic arithmetic call results','f and term0 Result effects exposed at caller boundary; no oracle law assumed','tail iteration evaluated at arbitrary legal current cursor','shift selects row 9; caller computes eta*term0 before owner shift']),indent=2)+'\n')
