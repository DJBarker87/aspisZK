use aspis_core::field::{M31,CM31,QM31,WideExact as W};
#[path="original-powers.rs"] mod original_powers;
#[path="copy-powers.rs"] mod copy_powers;
#[path="original-pole.rs"] mod original_pole;
#[path="copy-pole.rs"] mod copy_pole;
#[path="original-sum.rs"] mod original_sum;
#[path="copy-sum.rs"] mod copy_sum;
fn word(s:&mut u64)->u32{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s as u32}
fn q(s:&mut u64)->QM31{QM31{c0:CM31{a:M31(word(s)),b:M31(word(s))},c1:CM31{a:M31(word(s)),b:M31(word(s))}}}
fn powers<const N:usize>(x:W){assert_eq!(original_powers::powers::<N>(x),copy_powers::powers::<N>(x));}
fn main(){
 std::panic::set_hook(Box::new(|_|{}));
 let mut seed=0x7100abcde1234567u64;
 let mut pc=0;let mut sc=0;let mut vc=0;let mut ec=0;
 for _ in 0..1024 {let x=W::new(q(&mut seed),q(&mut seed));
  powers::<0>(x);powers::<1>(x);powers::<2>(x);powers::<3>(x);powers::<16>(x);powers::<64>(x);pc+=6;
 }
 // A changed-output case: zero initial array must retain the write of ONE.
 assert_eq!(copy_powers::powers::<1>(W::ZERO),[W::ONE]);
 assert_eq!(copy_powers::powers::<2>(W::ZERO),[W::ONE,W::ZERO]);
 for len in [0,1,1023,1024,1025] {for _ in 0..64 {
  let xs:Vec<_>=(0..len).map(|_|q(&mut seed)).collect();
  assert_eq!(original_sum::state_only_copy_helper_sum(&xs),copy_sum::state_only_copy_helper_sum(&xs));sc+=1;
 }}
 for len in [0,1,15,16,17,1023,1024,1025] {for mode in 0..4 {for _ in 0..32 {
  let chi=q(&mut seed);let mut v:Vec<_>=(0..len).map(|_|[[q(&mut seed),q(&mut seed)],[q(&mut seed),q(&mut seed)]]).collect();
  let mut masks=[0u16;64];for m in &mut masks {*m=word(&mut seed) as u16;}
  if mode==0 {masks=[0;64];}
  if mode==1 && len>0 {v[0][0][0]=chi;masks[0]|=1;}
  if mode==2 && len>0 && len<=1024 {let r=len-1;v[r][1][1]=chi;masks[r>>4]|=1<<(r&15);}
  let a=std::panic::catch_unwind(||original_pole::all_slots_clear(&v,&masks,chi));
  let b=std::panic::catch_unwind(||copy_pole::all_slots_clear(&v,&masks,chi));
  match (a,b) {(Ok(x),Ok(y))=>{assert_eq!(x,y);vc+=1},(Err(_),Err(_))=>{assert!(len>1024);ec+=1},_=>panic!("Result mismatch")}
 }}}
 println!("{{\"powers_pairs\":{},\"sum_pairs\":{},\"pole_value_pairs\":{},\"pole_error_pairs\":{},\"restored_one\":[1],\"restored_two\":[1,0],\"pass\":true}}",pc,sc,vc,ec);
}
