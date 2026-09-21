extern crate aspis_core as corelib;
#[path="r16_basis_transport.rs"] mod basis_transport;
mod r17_tensor_prefix;
mod r17_owned_weights;
mod r17_structured_g;
use r17_structured_g as structured_g;
mod r17_mask_workspace;
mod r17_opening_weights;
mod r17_weighted_groups;
mod r17_compact_ordinary;
use corelib::field::{QM31 as K,CM31,M31,P};
use corelib::sumcheck::WeightAccumulator;
fn sample(n:u32)->K {
    K{c0:CM31::new(M31(n%P),M31((n*3+7)%P)),c1:CM31::new(M31((n*5+11)%P),M31((n*7+13)%P))}
}
fn main() {
    let t=basis_transport::transport();
    for j in 0..479 {assert!(t.order[j]<479);}
    for j in 479..1024 {assert_eq!(t.order[j],j);}
    assert_eq!(t.order[1023],1023);assert!(t.inactive[1023]);
    for case in 0..32u32 {
        let z=core::array::from_fn(|i|match case {
            0=>K::ZERO,1=>K::ONE,
            2=>K{c0:CM31::new(M31(P-1),M31(P-1)),c1:CM31::new(M31(P-1),M31(P-1))},
            _=>sample(case*10+i as u32),
        });
        let kappa=if case==3 {K::ZERO}else if case==4 {K::ONE}else{sample(case+100)};
        let abc=core::array::from_fn(|i|if case==0 {K::ZERO}else{sample(case*3+i as u32+400)});
        let alpha=core::array::from_fn(|i|if case==0 {K::ZERO}else if case==1 {K::ONE}else{sample(case*4+i as u32+800)});
        let compact=r17_compact_ordinary::Description::new(&z,kappa);
        let original=r17_opening_weights::original_weights(&z,kappa,false);
        let dual=t.dual(&original);
        for j in 0..1024 {
            assert_eq!(compact.original_entry(j),original[j]);
            assert_eq!(compact.dual_entry(j),dual[j]);
        }
        let mut weights=WeightAccumulator::empty(10);
        weights.add_dense(r17_owned_weights::chord(dual,abc)).unwrap();
        for a in alpha {weights.fold_deferred_relation_arity4(a);}
        assert_eq!(compact.terminal(abc,alpha),weights.weight_prefix::<4>());
    }
    println!("PASS: 32 complete source ordinary-channel descriptions x 1024 original entries and 1024 dual entries; all 128 compact terminal entries equal source chord/four-fold pipeline");
    println!("BOUNDARY: ordinary channel before image residual/query injection only; G remains separate; source transcript/verifier unchanged; no new CU or privacy claim");
}
