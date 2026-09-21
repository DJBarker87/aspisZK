//! Source differential and allocation-denial controls, not a formal proof.
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
mod r17_compact_workspace;
use corelib::field::{QM31 as K,CM31,M31,P};
use corelib::sumcheck::WeightAccumulator;
// Extracted unchanged from the retained R17 workspace allocation probe.
include!("r17_reused_deny_allocator.rs");
fn sample(n:u32)->K {
    K{c0:CM31::new(M31(n%P),M31((n*3+7)%P)),c1:CM31::new(M31((n*5+11)%P),M31((n*7+13)%P))}
}
fn main() {
    let t=basis_transport::transport();
    for j in 0..479 {assert!(t.order[j]<479);}
    for j in 479..1024 {assert_eq!(t.order[j],j);}
    assert_eq!(t.order[1023],1023);assert!(t.inactive[1023]);
    r17_weighted_groups::check_edges();
    for case in 0..32u32 {
        let z=core::array::from_fn(|i|match case {
            0=>K::ZERO,1=>K::ONE,
            2=>K{c0:CM31::new(M31(P-1),M31(P-1)),c1:CM31::new(M31(P-1),M31(P-1))},
            _=>sample(case*10+i as u32),
        });
        let kappa=if case==3 {K::ZERO}else if case==4 {K::ONE}else{sample(case+100)};
        let abc=core::array::from_fn(|i|if case==0 {K::ZERO}else{sample(case*3+i as u32+400)});
        let alpha=core::array::from_fn(|i|if case==0 {K::ZERO}else if case==1 {K::ONE}else{sample(case*4+i as u32+800)});
        let audit=core::array::from_fn(|i|if i<10 {z[i]}else{kappa});
        let expected=r17_compact_ordinary::Description::new(&z,kappa).terminal(abc,alpha);
        let original=r17_opening_weights::original_weights(&z,kappa,false);
        let dual=t.dual(&original);
        let mut dense=WeightAccumulator::empty(10);
        dense.add_dense(r17_owned_weights::chord(dual,abc)).unwrap();
        for a in alpha {dense.fold_deferred_relation_arity4(a);}
        assert_eq!(expected,dense.weight_prefix::<4>());
        let dirty:Vec<_>=(0..1024).map(|j|sample(case*1024+j)).collect();
        let ptr=dirty.as_ptr();let cap=dirty.capacity();
        let mut owner=WeightAccumulator::empty(10);owner.add_dense(dirty).unwrap();
        ARMED.store(true,SeqCst);
        let mut workspace=owner.into_single_dense_for_workspace().unwrap();
        let actual=r17_compact_workspace::terminal(std::hint::black_box(&audit),abc,alpha,&mut workspace);
        std::hint::black_box(&workspace);
        ARMED.store(false,SeqCst);
        assert_eq!(CALLS.load(SeqCst),0);
        assert_eq!(workspace.as_ptr(),ptr);assert_eq!(workspace.capacity(),cap);
        assert_eq!(actual,expected);
        let kernel=r17_weighted_groups::Kernel::new(abc,alpha);
        for len in [0usize,1,15,16,17,479,480,1024] {
            let input:Vec<_>=(0..len).map(|j|sample(j as u32+case*100)).collect();
            let expected=kernel.prefix(&input);
            let mut sums=[K::ONE;128];
            ARMED.store(true,SeqCst);
            let actual=kernel.prefix_into(&input,&mut sums);
            ARMED.store(false,SeqCst);
            assert_eq!(actual,expected);assert_eq!(CALLS.load(SeqCst),0);
        }
        let masks=core::array::from_fn(|j|(j as u16).wrapping_mul(313).wrapping_add(case as u16));
        let expected=kernel.binary_masks(&masks);let mut sums=[K::ONE;128];
        ARMED.store(true,SeqCst);
        let actual=kernel.binary_masks_into(&masks,&mut sums);
        ARMED.store(false,SeqCst);
        assert_eq!(actual,expected);assert_eq!(CALLS.load(SeqCst),0);
    }
    assert!(WeightAccumulator::empty(10).into_single_dense_for_workspace().is_none());
    let mut geometric=WeightAccumulator::empty(10);geometric.add_geometric(K::ONE,K::ONE);
    assert!(geometric.into_single_dense_for_workspace().is_none());
    let mut two=WeightAccumulator::empty(0);
    two.add_dense(vec![K::ONE]).unwrap();two.add_dense(vec![K::ONE]).unwrap();
    assert!(two.into_single_dense_for_workspace().is_none());
    println!("PASS: all 64 carry schedules and repeated exhaustion equal retained Vec routine; 32 complete terminals equal R33 and dense source, dirty consumed buffers retain pointer/capacity, zero allocation attempts");
    println!("PASS: 256 prefix-workspace and 32 binary-mask workspace controls with zero allocation attempts; three non-single-dense shapes rejected");
}
