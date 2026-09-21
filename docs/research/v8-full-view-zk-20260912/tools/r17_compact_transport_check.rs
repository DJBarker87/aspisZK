//! Host-only source controls for the compact transport decomposition.
//! Dense correction contraction here is an oracle, NOT an optimized verifier.
extern crate aspis_core as corelib;
#[path="r16_basis_transport.rs"] mod basis_transport;
mod r17_tensor_prefix;
mod r17_owned_weights;
use corelib::field::{QM31 as K,CM31,M31,P};
use corelib::sumcheck::WeightAccumulator;
// Exact retained baseline functions, extracted and pinned by the stager.
include!("r17_reused_block_terminal.rs");

fn sample(n:u32)->K {
    K{c0:CM31::new(M31(n%P),M31((n*3+7)%P)),
        c1:CM31::new(M31((n*5+11)%P),M31((n*7+13)%P))}
}
fn dense_terminal(v:Vec<K>,abc:[K;3],alpha:[K;4])->[K;4] {
    let mut w=WeightAccumulator::empty(10);
    w.add_dense(r17_owned_weights::chord(v,abc)).unwrap();
    for a in alpha {w.fold_deferred_relation_arity4(a);}
    w.weight_prefix::<4>()
}
fn corrections(w:&[K],abc:[K;3],alpha:[K;4],plain:[K;4])->[K;4] {
    let t=basis_transport::transport();
    let mut delta=vec![K::ZERO;1024];
    for j in 0..479 {delta[j]=w[t.order[j]].sub(w[j]);}
    let others:Vec<_>=t.order.iter().map(|&r|
        if r!=1023 && t.inactive[r] {K::ONE} else {K::ZERO}).collect();
    let pivot:Vec<_>=t.order.iter().map(|&r|if r==1023 {K::ONE}else{K::ZERO}).collect();
    let d=dense_terminal(delta,abc,alpha);
    let o=dense_terminal(others,abc,alpha);
    let p=dense_terminal(pivot,abc,alpha);
    core::array::from_fn(|i|plain[i].add(d[i]).sub(w[1023].mul(o[i])).add(p[i]))
}
fn expected(w:&[K],abc:[K;3],alpha:[K;4])->[K;4] {
    let t=basis_transport::transport();
    let with_inactive:Vec<_>=w.iter().enumerate().map(|(j,&v)|
        if t.inactive[j] {v.add(K::ONE)}else{v}).collect();
    dense_terminal(t.dual(&with_inactive),abc,alpha)
}
fn main() {
    let t=basis_transport::transport();
    assert!(t.inactive[1023]);assert_eq!(t.order[1023],1023);
    for j in 479..1024 {assert_eq!(t.order[j],j);}
    let indicator:Vec<_>=t.inactive.iter().map(|&b|if b {K::ONE}else{K::ZERO}).collect();
    let dual=t.dual(&indicator);
    for j in 0..1024 {assert_eq!(dual[j],if j==1023 {K::ONE}else{K::ZERO});}
    println!("PASS: actual source permutation fixed at all 545 suffix slots; inactive indicator dual equals pivot at all 1024 entries");
    for case in 0..32u32 {
        let z=core::array::from_fn(|i|match case {
            0=>K::ZERO,1=>K::ONE,
            2=>K{c0:CM31::new(M31(P-1),M31(P-1)),c1:CM31::new(M31(P-1),M31(P-1))},
            _=>sample(100*case+i as u32),
        });
        let abc=core::array::from_fn(|i|if case==0 {K::ZERO}else{sample(case*3+i as u32)});
        let alpha=core::array::from_fn(|i|if case<2 {if case==0 {K::ZERO}else{K::ONE}}
            else {sample(case*4+i as u32+400)});
        let points=corelib::v6_transcript::v6_statement_points(&z);
        let pairs:[[K;2];10]=core::array::from_fn(|i|[K::ONE.sub(points[0][9-i]),points[0][9-i]]);
        let pairs2:[[K;2];10]=core::array::from_fn(|i|[K::ONE.sub(points[2][9-i]),points[2][9-i]]);
        for bit in 0..10 {for value in 0..2 {
            assert_eq!(pairs2[bit][value],pairs[bit][if bit==2 || bit==3 {value^1}else{value}]);
        }}
        let mut w=vec![K::ZERO;1024];
        r17_tensor_prefix::fill(K::ONE,&points[0],w.as_mut_slice().try_into().unwrap());
        let plain=block_terminal(&pairs,alpha,abc).0;
        assert_eq!(plain,dense_terminal(w.clone(),abc,alpha));
        assert_eq!(corrections(&w,abc,alpha,plain),expected(&w,abc,alpha));

        let k=if case==0 {K::ZERO}else{sample(case+800)};let k3=k.pow(3);
        let block:[K;4]=core::array::from_fn(|d|pairs[2][d&1].mul(pairs[3][d>>1]));
        let fused=core::array::from_fn(|d|k.mul(block[d]).add(k3.mul(block[d^3])));
        let fused_plain=block_terminal_impl(&pairs,alpha,abc,Some(fused)).0;
        let mut other=vec![K::ZERO;1024];
        r17_tensor_prefix::fill(K::ONE,&points[2],other.as_mut_slice().try_into().unwrap());
        for j in 0..1024 {w[j]=k.mul(w[j]).add(k3.mul(other[j]));}
        assert_eq!(fused_plain,dense_terminal(w.clone(),abc,alpha));
        assert_eq!(corrections(&w,abc,alpha,fused_plain),expected(&w,abc,alpha));

        // The decomposition also holds for arbitrary non-tensor weights:
        // no honesty, point-product or G-sparsity premise enters it.
        let arbitrary:Vec<_>=(0..1024).map(|j|sample(case*1024+j)).collect();
        let plain=dense_terminal(arbitrary.clone(),abc,alpha);
        assert_eq!(corrections(&arbitrary,abc,alpha,plain),expected(&arbitrary,abc,alpha));
    }
    println!("PASS: 32 actual statement-point complement schedules; 32 unchanged baseline tensor terminals and 32 fused-row terminals through actual repaired dual/chord/four-fold source; 32 arbitrary-weight controls");
    println!("BOUNDARY: correction contraction remains dense in this control; no SBF CU claim, transcript change, verifier integration, source extraction or privacy theorem");
}
