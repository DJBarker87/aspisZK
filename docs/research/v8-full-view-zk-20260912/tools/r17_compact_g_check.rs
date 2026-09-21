//! Complete G functional control, including tail and pivot (not just prefix).
extern crate aspis_core as corelib;
#[path="r16_basis_transport.rs"] mod basis_transport;
mod r17_tensor_prefix;mod r17_owned_weights;mod r17_structured_g;
use r17_structured_g as structured_g;
mod r17_mask_workspace;mod r17_opening_weights;mod r17_weighted_groups;
mod r17_compact_workspace;mod r17_g_geometric;mod r17_compact_g;
use corelib::field::{QM31 as K,CM31,M31,P};
use corelib::sumcheck::WeightAccumulator;
include!("r17_reused_deny_allocator.rs");
fn sample(n:u32)->K {K{c0:CM31::new(M31(n%P),M31((n*3+7)%P)),c1:CM31::new(M31((n*5+11)%P),M31((n*7+13)%P))}}
fn main() {
    let t=basis_transport::transport();
    for case in 0..16u32 {
        let z=core::array::from_fn(|i|match case {
            0=>K::ZERO,1=>K::ONE,
            2=>K{c0:CM31::new(M31(P-1),M31(P-1)),c1:CM31::new(M31(P-1),M31(P-1))},
            _=>sample(case*10+i as u32),
        });
        let k=if case==3 {K::ZERO}else if case==4 {K::ONE}else{sample(case+100)};
        let abc=core::array::from_fn(|i|if case==0 {K::ZERO}else{sample(case*3+i as u32+400)});
        let alpha=core::array::from_fn(|i|if case==0 {K::ZERO}else if case==1 {K::ONE}else{sample(case*4+i as u32+800)});
        let audit=core::array::from_fn(|i|if i<10 {z[i]}else{k});
        let d=r17_compact_g::Description::new(&audit);
        let original=r17_opening_weights::original_weights(&z,k,true);
        let dual=t.dual(&original);
        for use_x in [false,true] {assert_eq!(d.dual_pair(use_x),[dual[0],dual[if use_x {2}else{1}]]);}
        let mut dense=WeightAccumulator::empty(10);
        dense.add_dense(r17_owned_weights::chord(dual,abc)).unwrap();
        for a in alpha {dense.fold_deferred_relation_arity4(a);}
        let expected=dense.weight_prefix::<4>();
        ARMED.store(true,SeqCst);
        let actual=d.terminal(std::hint::black_box(&audit),abc,alpha);
        ARMED.store(false,SeqCst);
        assert_eq!(CALLS.load(SeqCst),0);
        assert_eq!(actual,expected,"G complete source case={case}");
    }
    println!("PASS: 16 complete G terminals and 32 dual claim pairs equal actual original/dual/chord/four-fold source; full tail+pivot retained, zero terminal allocation attempts");
}
