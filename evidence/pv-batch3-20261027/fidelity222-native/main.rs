use aspis_core::field::{M31,CM31,QM31};
use std::hint::black_box;
fn limbs(q:QM31)->[u32;4]{[q.c0.a.0,q.c0.b.0,q.c1.a.0,q.c1.b.0]}
fn main(){
 assert!(!cfg!(debug_assertions));
 let q=QM31{c0:CM31{a:M31(7),b:M31(0)},c1:CM31{a:M31(0),b:M31(0)}};
 let column=vec![q;1024];let point=[QM31::ZERO;10];
 let old=aspis_statement::multilinear_evaluate_qm31(black_box(&column),black_box(&point));
 let copy=aspis_r1_cost_probe::host_multilinear::multilinear_evaluate_qm31(black_box(&column),black_box(&point));
 assert_eq!(old,copy);assert_eq!(old,Some(q));
 println!("{{\"case\":\"all-zero-point/constant-seven-column\",\"original\":{:?},\"copy\":{:?}}}",old.map(limbs).unwrap(),copy.map(limbs).unwrap());
}
