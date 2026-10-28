//! Scratch finite probe. Original and copied functions, optimized same build.
use aspis_core::field::{QM31 as K,WideExact as E};
use std::{hint::black_box as b,time::Instant};
#[path="../../source/crates/aspis-r1-cost-probe/src/prover_helper_sum.rs"] mod helper_copy;
#[path="../../source/crates/aspis-r1-cost-probe/src/prover_powers.rs"] mod powers_copy;
#[path="../../source/crates/aspis-r1-cost-probe/src/ct_pole.rs"] mod pole_copy;
mod pole_original;
fn bench<T>(name:&str,n:usize,mut f:impl FnMut()->T){let s=Instant::now();for _ in 0..n{b(f());}println!("{} {} {}",name,n,s.elapsed().as_secs_f64());}
fn main(){
 assert!(!cfg!(debug_assertions));
 let h=b([K::ONE;1024]);let x=b(E::from_limbs([2,3,4,5,6,7,8,9]).unwrap());
 let v=b([[[K::ONE;2];2];1024]);let masks=b([0xffff;64]);let chi=b(K::ZERO);
 assert_eq!(aspis_statement::state_only_copy_helper_sum(&h),helper_copy::state_only_copy_helper_sum(&h));
 assert_eq!(aspis_r1_cost_probe::weights::powers::<29>(x),powers_copy::powers::<29>(x));
 assert_eq!(pole_original::all_slots_clear(&v,&masks,chi),pole_copy::all_slots_clear(&v,&masks,chi));
 for round in 0..5{
  println!("ROUND {}",round);
  bench("230_original",100000,||aspis_statement::state_only_copy_helper_sum(b(&h)));
  bench("230_copy",100000,||helper_copy::state_only_copy_helper_sum(b(&h)));
  bench("254_original",10000,||aspis_r1_cost_probe::weights::powers::<29>(b(x)));
  bench("254_copy",10000,||powers_copy::powers::<29>(b(x)));
  bench("258_original",100000,||pole_original::all_slots_clear(b(&v),b(&masks),b(chi)));
  bench("258_copy",100000,||pole_copy::all_slots_clear(b(&v),b(&masks),b(chi)));
 }
}
