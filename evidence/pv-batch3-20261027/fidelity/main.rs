fn main() {
 assert!(!cfg!(debug_assertions));
 let new=aspis_prover::host_forest::pool_v1_pair_forest_copy_active_row_masks_v1().unwrap();
 let old=aspis_statement::pool_v1::pair_forest_hiding::pool_v1_pair_forest_copy_active_row_masks_v1().unwrap();
 assert_eq!(new,old);
 println!("{:?}",new);
 assert!(new.iter().any(|x|*x!=0));
 use aspis_core::field::{M31,CM31,QM31};
 for v in [QM31::ONE,QM31{c0:CM31{a:M31::ZERO,b:M31(2147483648)},c1:CM31::ZERO}] {
  let c=[QM31::ONE;16];let m=[QM31::ONE;10];let p=[v;10];
  let a=aspis_prover::host_arithmetic::state_only_selected_mask_value(&c,&m,QM31::ONE,&p);
  let b=aspis_core::state_only_hiding::state_only_selected_mask_value(&c,&m,QM31::ONE,&p);
  assert_eq!(a,b);println!("{:?}",[a.c0.a.0,a.c0.b.0,a.c1.a.0,a.c1.b.0]);
 }
 for raw in [false,true] {
  let (p,x)=if raw {let mut p=[QM31::ZERO;28];p[2]=QM31::ONE;(p,QM31{c0:CM31{a:M31::ZERO,b:M31(2147483648)},c1:CM31::ZERO})}else{([QM31::ONE;28],QM31::ONE)};
  let a=aspis_prover::host_arithmetic::evaluate_state_only_polynomial(&p,x);
  let b=aspis_core::state_only_sumcheck::evaluate_state_only_polynomial(&p,x);
  assert_eq!(a,b);println!("{:?}",[a.c0.a.0,a.c0.b.0,a.c1.a.0,a.c1.b.0]);
 }
}
