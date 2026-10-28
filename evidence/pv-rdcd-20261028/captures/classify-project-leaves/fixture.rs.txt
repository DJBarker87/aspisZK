use aspis_core::field::{M31,CM31,QM31,P};
mod compress;mod boundary;mod polynomial;
fn word(s:&mut u64)->u32{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s as u32}
fn q(s:&mut u64)->QM31 {QM31{c0:CM31{a:M31(word(s)%P),b:M31(word(s)%P)},c1:CM31{a:M31(word(s)%P),b:M31(word(s)%P)}}}
fn main(){
 let mut seed=0x38120261028u64;let mut n=0;
 for _ in 0..128 {
  let p=core::array::from_fn(|_|q(&mut seed));let x=q(&mut seed);
  assert_eq!(aspis_core::state_only_sumcheck::state_only_boundary_sum(&p),boundary::boundary_flat(&p));
  assert_eq!(aspis_core::state_only_sumcheck::evaluate_state_only_polynomial(&p,x),polynomial::evaluate(&p,x));
  for len in [0,1,2,16,31,64] {
   let v:Vec<_>=(0..len).map(|_|M31(word(&mut seed)%P)).collect();let tag=M31(word(&mut seed)%P);
   assert_eq!(aspis_statement::logup::compress_tagged_tuple(tag,&v,x),compress::compress(tag,&v,x));n+=1;
  }
 }
 println!("FINITE: 128 boundary + 128 polynomial pairs; {n} canonical compressor pairs at lengths0,1,2,16,31,64; retained original owned-reference bodies; no universal claim");
}
