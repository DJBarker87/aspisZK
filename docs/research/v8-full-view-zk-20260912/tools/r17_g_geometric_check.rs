//! Differential specialization control; all 271 existing fixed nodes retained.
extern crate aspis_core as corelib;
mod r17_g_geometric;
use corelib::field::{QM31 as K,CM31,M31,P};
use corelib::sumcheck::WeightAccumulator;
include!("r17_reused_block_terminal.rs");
#[path="r16_basis_transport.rs"] mod basis_transport;
mod r17_tensor_prefix;mod r17_owned_weights;mod r17_structured_g;
use r17_structured_g as structured_g;
mod r17_mask_workspace;mod r17_opening_weights;
fn lift(x:M31)->K {K::from_cm31(CM31::from_m31(x))}
fn sample(n:u32)->K {K{c0:CM31::new(M31(n%P),M31((n*3+7)%P)),c1:CM31::new(M31((n*5+11)%P),M31((n*7+13)%P))}}
fn main() {
    for case in 0..8u32 {
        let alpha=core::array::from_fn(|i|if case==0 {K::ZERO}else if case==1 {K::ONE}else{sample(case*4+i as u32)});
        let abc=core::array::from_fn(|i|if case==0 {K::ZERO}else{sample(case*3+i as u32+50)});
        let kernel=r17_g_geometric::Kernel::new(alpha,abc);
        for node in (1..=271).chain([0,P-1]) {
            let mut p=M31(node);
            let pairs=core::array::from_fn(|_|{let out=[K::ONE,lift(p)];p=p.mul(p);out});
            let actual=kernel.terminal(M31(node));
            assert_eq!(actual,block_terminal(&pairs,alpha,abc).0,"case={case} node={node}");
            if [0,1,271,P-1].contains(&node) {
                let mut power=M31::ONE;
                let values=(0..1024).map(|_|{let out=lift(power);power=power.mul(M31(node));out}).collect::<Vec<_>>();
                let mut acc=WeightAccumulator::empty(10);
                acc.add_dense(r17_opening_weights::chord_transpose(&values,abc)).unwrap();
                for a in alpha {acc.fold_deferred_relation_arity4(a);}
                assert_eq!(actual,acc.weight_prefix::<4>());
            }
        }
    }
    println!("PASS: 2184 fixed/base-boundary geometric terminals match retained block formula; 32 direct source chord/four-fold controls");
}
