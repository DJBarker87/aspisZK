use super::*;
const P:u64=2147483647;
fn rand(s:&mut u64)->u32{*s=s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);((*s>>32)%P)as u32}
fn k(words:[u32;4])->K{K{c0:aspis_core::field::CM31{a:M31(words[0]),b:M31(words[1])},c1:aspis_core::field::CM31{a:M31(words[2]),b:M31(words[3])}}}
#[test]
fn NEG_row_native_differential(){
 let mut state=1;let mut changed=0;
 for n in 0..1024{
  let p=if n==0{[2147483646;4]}else{core::array::from_fn(|_|rand(&mut state))};
  let basis=if n==0{2147483646}else{rand(&mut state)};
  let old=core::array::from_fn(|j| if n==0{17179869183+j as u64}else{u64::from(rand(&mut state))+(n%4) as u64*(P-1)*(P-1)});
  for flush in [false,true]{
   let mut row=old;update_residue_row(&mut row,k(p),M31(basis),flush);
   for j in 0..4{
    let sum=u128::from(old[j])+u128::from(p[j])*u128::from(basis);assert!(sum<1u128<<64);
    let expected=if flush{((sum&u128::from(P))+(sum>>31))as u64}else{sum as u64};
    let expected=if cfg!(NEG_wrong_native){expected^1}else{expected};
    assert_eq!(row[j],expected,"row case={n} flush={flush} lane={j}");
    if flush && row[j]!=sum as u64{changed+=1;}
   }
  }
 }
 assert!(changed>0);println!("NEG_row_native_differential cases=2048 changed_flush_cells={changed}");
}
#[test]
fn NEG_dots_native_differential(){
 let mut state=3;
 for n in 0..64{
  let mut q=[0u8;608];for word in q.chunks_exact_mut(4){let x=if n==0{2147483646}else{rand(&mut state)};word.copy_from_slice(&x.to_le_bytes());}
  let g:[E;29]=core::array::from_fn(|_|E::from_limbs(core::array::from_fn(|_|if n==0{2147483646}else{rand(&mut state)})).unwrap());
  let out=fast_dots::four_dots(&q,&g);
  for slot in 0..4{
   let mut expected=E::ZERO;
   for term in 0..26{let at=slot*120+term*4;let s=M31::from_le_bytes(q[at..at+4].try_into().unwrap()).unwrap();expected=expected.add(g[term].mul_m31(s));}
   let k28=K::from_le_bytes(&q[slot*120+104..slot*120+120]).unwrap();expected=expected.add(g[28].mul_qm31(k28));
   for i in 0..2{let at=480+slot*32+i*16;expected=expected.add(g[26+i].mul_qm31(K::from_le_bytes(&q[at..at+16]).unwrap()));}
   if cfg!(NEG_wrong_native){expected=expected.add(E::ONE);}
   assert_eq!(out[slot].to_limbs(),expected.to_limbs(),"dots case={n} slot={slot}");
  }
 }
 println!("NEG_dots_native_differential cases=256 includes_all_max_limbs");
}

include!("NEG_fixture_tests.rs");
