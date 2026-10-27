mod forest {
//! Interleaved per-call benchmarks; this binary never times a whole prover.
use aspis_prover::host_forest as copy;
use aspis_statement::pool_v1::{pair_forest_hiding as original,pair_forest_trace as trace};
use std::{hint::black_box,time::Instant};
fn batch<T>(f:&impl Fn()->T,n:u32)->f64 {let start=Instant::now();for _ in 0..n{black_box(f());}start.elapsed().as_secs_f64()*1e6/f64::from(n)}
fn bench<A,B>(name:&str,a:impl Fn()->A,b:impl Fn()->B){
 for _ in 0..100{black_box(a());black_box(b());}
 let mut pairs=Vec::new();
 for i in 0..101 {let (x,y)=if i%2==0{let x=batch(&a,100);let y=batch(&b,100);(x,y)}else{let y=batch(&b,100);let x=batch(&a,100);(x,y)};pairs.push((x,y));}
 let mut av:Vec<_>=pairs.iter().map(|p|p.0).collect();let mut bv:Vec<_>=pairs.iter().map(|p|p.1).collect();let mut dv:Vec<_>=pairs.iter().map(|p|p.1-p.0).collect();for v in [&mut av,&mut bv,&mut dv]{v.sort_by(f64::total_cmp);}
 println!("{{\"op\":\"{name}\",\"original_us\":{},\"copy_us\":{},\"paired_delta_us\":{},\"pairs\":101,\"calls_per_pair\":100,\"order\":\"alternating AB BA\"}}",av[50],bv[50],dv[50]);
}
pub fn run(){
 assert!(!cfg!(debug_assertions));
 let schedule=copy::build_pool_v1_pair_forest_copy_row_schedule_v1().unwrap();assert_eq!(&schedule.data[..schedule.len],original::build_pool_v1_pair_forest_copy_row_schedule_v1().unwrap());
 assert_eq!(copy::materialize_active_rows(),original::pool_v1_pair_forest_copy_active_rows_v1());
 assert_eq!(copy::materialize_mask_cells(),original::pool_v1_pair_forest_relation_free_mask_cells_v1());
 assert_eq!(copy::pool_v1_pair_forest_copy_active_row_masks_v1(),original::pool_v1_pair_forest_copy_active_row_masks_v1());
 assert_eq!(copy::pool_v1_pair_forest_copy_inactive_row_masks_v1(),original::pool_v1_pair_forest_copy_inactive_row_masks_v1());
 let registry=copy::build_pool_v1_pair_forest_copy_registry_v1().unwrap();assert_eq!(&registry.data[..registry.len],trace::build_pool_v1_pair_forest_copy_registry_v1().unwrap());
 println!("{}", "{\"differential\":\"schedule, cells, rows, active/inactive masks, registry agree\",\"kind\":\"finite native check, not source theorem\"}");
 bench("132",original::pool_v1_pair_forest_relation_free_mask_cells_v1,copy::materialize_mask_cells);
 bench("133",original::pool_v1_pair_forest_copy_active_rows_v1,copy::materialize_active_rows);


 bench("228",trace::build_pool_v1_pair_forest_copy_registry_v1,copy::build_pool_v1_pair_forest_copy_registry_v1);

 use aspis_core::field::{M31,CM31,QM31};
 let lift=|n|QM31::from_cm31(CM31::from_m31(M31(n)));
 for withdrawal in [false,true]{let fixture=aspis_prover::r0_fixture::prepare(withdrawal);let trace=&fixture.compiled.trace;let index=fixture.public().transition().live_snapshot.next_pair_index;let lambda=lift(17);let chi=lift(23);
  let old=||aspis_statement::pool_v1::pair_forest_semantic_oracle::build_pool_v1_pair_forest_copy_helper_v1(black_box(trace),black_box(index),black_box(lambda),black_box(chi));
  let new=||aspis_prover::host_forest::materialize_copy_helper(black_box(trace),black_box(index),black_box(lambda),black_box(chi));
  assert_eq!(old(),new());
  bench(if withdrawal{"224-withdrawal"}else{"224-transfer"},old,new);
 }
}
}
mod public_terminal {
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
pub fn run(){
 use aspis_core::field::{M31,CM31,QM31};
 use aspis_core::state_only_prefix::r0::Challenges;
 use aspis_r1_cost_probe::host_public;
 assert!(!cfg!(debug_assertions));let lift=|n|QM31::from_cm31(CM31::from_m31(M31(n)));
 let c=Challenges{lambda:lift(17),chi:lift(23),theta:lift(29),zc:[lift(31);10],eta:lift(37),mu:lift(41)};
 let mut claims=[[QM31::ZERO;29];3];for p in 0..3{for l in 0..29{claims[p][l]=lift((p*29+l+2) as u32);}}
 for withdrawal in [false,true]{let fixture=aspis_prover::r0_fixture::prepare(withdrawal);let public=fixture.public();let tag=if withdrawal{"withdrawal"}else{"transfer"};
  assert_eq!(public.public_bytes(),host_public::materialize_public_bytes(public));
  bench(&format!("226-{tag}"),20,||public.public_bytes(),||host_public::materialize_public_bytes(public));
  for prefix in 0..11 {let mut point=[QM31::ZERO;10];for i in 0..prefix{point[i]=lift(17+i as u32);}for i in prefix..10{point[i]=if i%2==0{QM31::ZERO}else{QM31::ONE};}
   let old=||public.terminal_qm31(black_box(&claims),black_box(&point),black_box(&c));let new=||host_public::terminal_qm31(black_box(public),black_box(&claims),black_box(&point),black_box(&c));
   assert_eq!(old(),new());bench(&format!("227-{tag}-prefix-{prefix}"),10,old,new);
  }
 }
}
}
fn main(){forest::run();public_terminal::run();}
