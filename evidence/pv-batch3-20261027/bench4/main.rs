//! Interleaved per-call benchmarks; this binary never times a whole prover.
use aspis_prover::host_forest as copy;
use aspis_statement::pool_v1::{pair_forest_hiding as original,pair_forest_trace as trace};
use std::{hint::black_box,time::Instant};
fn batch<T>(f:&impl Fn()->T,n:u32)->f64 {let start=Instant::now();for _ in 0..n{black_box(f());}start.elapsed().as_secs_f64()*1e6/f64::from(n)}
fn bench<A,B>(name:&str,n:u32,a:impl Fn()->A,b:impl Fn()->B){
 for _ in 0..100{black_box(a());black_box(b());}
 let mut pairs=Vec::new();
 for i in 0..101 {let (x,y)=if i%2==0{let x=batch(&a,n);let y=batch(&b,n);(x,y)}else{let y=batch(&b,n);let x=batch(&a,n);(x,y)};pairs.push((x,y));}
 let mut av:Vec<_>=pairs.iter().map(|p|p.0).collect();let mut bv:Vec<_>=pairs.iter().map(|p|p.1).collect();let mut dv:Vec<_>=pairs.iter().map(|p|p.1-p.0).collect();for v in [&mut av,&mut bv,&mut dv]{v.sort_by(f64::total_cmp);}
 println!("{{\"op\":\"{name}\",\"original_us\":{},\"copy_us\":{},\"paired_delta_us\":{},\"pairs\":101,\"calls_per_pair\":{n},\"order\":\"alternating AB BA\"}}",av[50],bv[50],dv[50]);
}
fn main(){
 use aspis_core::field::{M31,CM31,QM31};
 use aspis_prover::host_arithmetic as arithmetic;
 assert!(!cfg!(debug_assertions));let lift=|n|QM31::from_cm31(CM31::from_m31(M31(n)));
 for withdrawal in [false,true] {let fixture=aspis_prover::r0_fixture::prepare(withdrawal);let tag=if withdrawal{"withdrawal"}else{"transfer"};let c1=std::array::from_fn(|i|lift(fixture.compiled.semantic_c1.c1[i][13].0));let mask=std::array::from_fn(|i|lift(i as u32+5));let g=lift(71);
  for prefix in 0..11{let mut point=[QM31::ZERO;10];for i in 0..prefix{point[i]=lift(17+i as u32);}for i in prefix..10{point[i]=if i%2==0{QM31::ZERO}else{QM31::ONE};}
   let old=||aspis_core::state_only_hiding::state_only_selected_mask_value(black_box(&c1),black_box(&mask),black_box(g),black_box(&point));let new=||arithmetic::state_only_selected_mask_value(black_box(&c1),black_box(&mask),black_box(g),black_box(&point));assert_eq!(old(),new());bench(&format!("117-{tag}-prefix-{prefix}"),100,old,new);
  }
  let polynomial=std::array::from_fn(|i|lift(i as u32*11+2));let challenge=lift(19);
  let old=||aspis_core::state_only_sumcheck::evaluate_state_only_polynomial(black_box(&polynomial),black_box(challenge));let new=||arithmetic::evaluate_state_only_polynomial(black_box(&polynomial),black_box(challenge));assert_eq!(old(),new());bench(&format!("121-{tag}"),100,old,new);
 }
 // Retain D234's noncanonical challenge as a source-copy comparison; never
 // assert that naïve Horner agrees there or that it is the admitted domain.
 let mut polynomial=[QM31::ZERO;28];polynomial[2]=QM31::ONE;let challenge=QM31{c0:CM31::new(M31::ZERO,M31(2147483648)),c1:CM31::ZERO};
 assert_eq!(aspis_core::state_only_sumcheck::evaluate_state_only_polynomial(&polynomial,challenge),arithmetic::evaluate_state_only_polynomial(&polynomial,challenge));
}
