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
 use aspis_r1_cost_probe::host_multilinear::multilinear_evaluate_qm31 as new_mle;
 use aspis_statement::multilinear_evaluate_qm31 as old_mle;
 assert!(!cfg!(debug_assertions));
 let lift=|n|QM31::from_cm31(CM31::from_m31(M31(n)));
 let column:Vec<_>=(0..1024).map(|i|lift(i*31+7)).collect();
 for prefix in 0..11 {let mut point=[QM31::ZERO;10];for i in 0..prefix{point[i]=lift(17+i as u32);}for i in prefix..10{point[i]=if i%2==0{QM31::ZERO}else{QM31::ONE};}
  assert_eq!(old_mle(&column,&point),new_mle(&column,&point));
  assert_eq!(old_mle(&column[..1023],&point),new_mle(&column[..1023],&point));
  bench(&format!("222-prefix-{prefix}"),10,||old_mle(black_box(&column),black_box(&point)),||new_mle(black_box(&column),black_box(&point)));
 }
 for withdrawal in [false,true]{let fixture=aspis_prover::r0_fixture::prepare(withdrawal);let trace=&fixture.compiled.trace;let index=fixture.public().transition().live_snapshot.next_pair_index;let lambda=lift(17);let chi=lift(23);
  let old=||aspis_statement::pool_v1::pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1(black_box(trace),black_box(index),black_box(lambda),black_box(chi));
  let new=||aspis_prover::host_forest::materialize_copy_helper(black_box(trace),black_box(index),black_box(lambda),black_box(chi));
  assert_eq!(old(),new());
  bench(if withdrawal{"224-withdrawal"}else{"224-transfer"},5,old,new);
 }
}
