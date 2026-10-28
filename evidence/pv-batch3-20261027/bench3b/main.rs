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
fn main(){
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
