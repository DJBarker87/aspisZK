//! Finite native microbenchmark, only used if the indicative precheck stops.
extern crate alloc;
pub mod transport {pub use aspis_r1_cost_probe::transport::*;}
pub mod verifier {pub use aspis_r1_cost_probe::verifier::*;}
pub mod weights {pub use aspis_r1_cost_probe::weights::*;}
#[path="../candidate/src/crates/aspis-r1-cost-probe/src/host_sampler.rs"] mod host_sampler;
#[path="../candidate/src/crates/aspis-r1-cost-probe/src/host_weights.rs"] mod host_weights;
use aspis_core::{field::{QM31 as K,WideExact as E},circle::SecureCirclePoint};
use std::{hint::black_box as b,time::Instant};
fn bench<T>(name:&str,n:usize,mut f:impl FnMut()->T) {
 let start=Instant::now();for _ in 0..n {b(f());}println!("{} {} {}",name,n,start.elapsed().as_secs_f64());
}
fn main(){
 assert!(!cfg!(debug_assertions));let block=b([0xff;32]);
 bench("249_original",100000,||aspis_r1_cost_probe::sampler::gamma_sample(b(&block)));
 bench("249_copy",100000,||host_sampler::gamma_sample(b(&block)));
 bench("250_original",100000,||aspis_r1_cost_probe::sampler::ordinary_sample(b(&block)));
 bench("250_copy",100000,||host_sampler::ordinary_sample(b(&block)));
 let a=b([K::ONE;10]);let z=b([SecureCirclePoint{x:K::ONE,y:K::ONE};2]);let v=transport::Variant::S2;
 bench("252_original",10000,||weights::Weights::new(b(v),b(&a),b(&z)).unwrap());
 bench("252_copy",10000,||host_weights::Weights::new(b(v),b(&a),b(&z)).unwrap());
 let old=weights::Weights::new(v,&a,&z).unwrap();let new=host_weights::Weights::new(v,&a,&z).unwrap();
 bench("253_original",100000,||old.raw(b(2),b(317)));
 bench("253_copy",100000,||new.raw(b(2),b(317)));
 bench("251_original",100,||old.materialize(b(E::ONE)).unwrap());
 bench("251_copy_with_allocation",100,||{
 let mut out=aspis_core::r0::heap::filled(1024,E::ZERO).unwrap();
 new.materialize(b(E::ONE),out.as_mut_slice().try_into().unwrap()).unwrap();out});
}
