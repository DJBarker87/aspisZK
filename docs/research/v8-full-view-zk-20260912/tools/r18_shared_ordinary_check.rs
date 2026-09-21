//! Focused arbitrary-input differential draft for R18 A/E sharing.
extern crate aspis_core as corelib;
#[path="r16_basis_transport.rs"] mod basis_transport;
mod r17_tensor_prefix;
mod r17_owned_weights;
mod r17_structured_g;
use r17_structured_g as structured_g;
mod r18_sparse_coded_g;
mod r18_compact_g;
mod r17_mask_workspace;
mod r17_opening_weights;
mod r17_weighted_groups;
mod r18_shared_ordinary;
use corelib::field::{CM31,M31,QM31 as K,P};
use corelib::sumcheck::WeightAccumulator;

fn sample(n:u32)->K { K { c0:CM31::new(M31(n%P),M31((n*3+7)%P)), c1:CM31::new(M31((n*5+11)%P),M31((n*7+13)%P)) } }

fn main() {
    let t=basis_transport::transport();
    for case in 0..32u32 {
        let z=core::array::from_fn(|i| if case==0 {K::ZERO} else if case==1 {K::ONE} else {sample(case*17+i as u32)});
        let kappa=if case==2 {K::ZERO} else {sample(case+100)};
        let audit=core::array::from_fn(|i|if i<10 {z[i]}else{kappa});
        let abc=core::array::from_fn(|i|if case==0 {K::ZERO}else{sample(400+case*3+i as u32)});
        let alpha=core::array::from_fn(|i|if case==1 {K::ONE}else{sample(800+case*4+i as u32)});
        let mut workspace=vec![K::ZERO;1024];
        let got=r18_shared_ordinary::terminal_pair(&audit,abc,alpha,&mut workspace);
        let fold=|v:Vec<K>| {
            let mut w=WeightAccumulator::empty(10);w.add_dense(v).unwrap();
            for a in alpha {w.fold_deferred_relation_arity4(a);}
            w.weight_prefix::<4>()
        };
        let a=fold(r17_opening_weights::chord_transpose(&t.dual(
            &r17_opening_weights::original_weights_reference(&z,kappa,false)),abc));
        let mut e0=WeightAccumulator::empty(10);
        e0.add_multilinear(K::ONE,corelib::v6_transcript::v6_statement_points(&z)[0].to_vec()).unwrap();
        let e0=(0..1024).map(|i|e0.weight_at(i as u32)).collect::<Vec<_>>();
        let e1=t.dual(&e0); let e2=r17_opening_weights::chord_transpose(&e1,abc);
        let mut ew=WeightAccumulator::empty(10); ew.add_dense(e2).unwrap();
        for value in alpha {ew.fold_deferred_relation_arity4(value);}
        assert_eq!(got[0],a,"A case {case}"); assert_eq!(got[1],ew.weight_prefix::<4>(),"E case {case}");
        let h=r18_compact_g::terminal(&z,abc,alpha,&mut workspace);
        let h0=structured_g::mask_weights_reference(&z);
        let dual_h=t.dual(&h0);
        assert_eq!(&dual_h[..3],&[K::ZERO;3]);
        assert_eq!(h,fold(r17_opening_weights::chord_transpose(&dual_h,abc)));
        for use_x in [false,true] {
            let pair=r18_compact_g::first_pair(&z,use_x);
            assert_eq!(pair,[e1[0],e1[if use_x {2}else{1}]]);
        }
        let g=fold(r17_opening_weights::chord_transpose(&t.dual(
            &r17_opening_weights::original_weights_reference(&z,kappa,true)),abc));
        let reconstructed: [K;4]=core::array::from_fn(|i|got[0][i].add(kappa.mul(h[i].sub(got[1][i]))));
        assert_eq!(g,reconstructed,"complete G functional {case}");
        let dot=|a:[K;4],b:[K;4]|corelib::field::qm31_sum_products4(a,b);
        let r:[K;4]=core::array::from_fn(|i|sample(1900+case*4+i as u32));
        let f:[K;4]=core::array::from_fn(|i|sample(2900+case*4+i as u32));
        assert_eq!(dot(a,r).add(dot(g,f)),dot(got[0],core::array::from_fn(|i|r[i].add(f[i])))
            .add(kappa.mul(dot(core::array::from_fn(|i|h[i].sub(got[1][i])),f))));
    }
    println!("PASS: 32 arbitrary z/kappa/abc/alpha cases, zero/one and degenerate controls; A and E equal retained dense dual/chord/fold references");
}
