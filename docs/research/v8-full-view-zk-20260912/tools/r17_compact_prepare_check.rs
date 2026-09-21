//! Finite source controls, not a universal source or privacy proof.
extern crate aspis_core as corelib;
#[path="r16_basis_transport.rs"] mod basis_transport;
mod r17_tensor_prefix;
mod r17_owned_weights;
mod r17_structured_g;
use r17_structured_g as structured_g;
mod r17_mask_workspace;
mod r17_opening_weights;
mod r17_compact_prepare;
use corelib::field::{QM31 as K,CM31,M31,P};
include!("r17_reused_deny_allocator.rs");
fn sample(n:u32)->K {
    K{c0:CM31::new(M31(n%P),M31((n*3+7)%P)),c1:CM31::new(M31((n*5+11)%P),M31((n*7+13)%P))}
}
fn main() {
    let t=basis_transport::transport();
    for case in 0..64u32 {
        let z=core::array::from_fn(|i|match case {
            0=>K::ZERO,1=>K::ONE,
            2=>K{c0:CM31::new(M31(P-1),M31(P-1)),c1:CM31::new(M31(P-1),M31(P-1))},
            _=>sample(case*10+i as u32),
        });
        let k=if case==3 {K::ZERO}else if case==4 {K::ONE}else{sample(case+100)};
        let original=r17_opening_weights::original_weights(&z,k,false);
        let dual=t.dual(&original);
        for use_x in [false,true] {
            ARMED.store(true,SeqCst);
            let pair=r17_compact_prepare::ordinary_pair(std::hint::black_box(&z),k,use_x);
            ARMED.store(false,SeqCst);
            assert_eq!(CALLS.load(SeqCst),0);
            assert_eq!(pair,[dual[0],dual[if use_x {2}else{1}]]);
        }
    }
    println!("PASS: 128 compact ordinary claim pairs equal actual source original/dual entries; both coordinate choices; zero allocation attempts");
}
