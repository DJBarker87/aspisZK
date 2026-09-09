//! Four terminal query weights under the existing shifted relation grammar.
use super::*;
pub(super) fn terminal(weights:&WeightAccumulator)->[K;4] {
    weights.weight_prefix::<4>()
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn terminal_matches_four_index_walks(){
        let mut rng=0x7465_726d_696e_616cu64;
        fn m(r:&mut u64)->M31{*r^=*r<<13;*r^=*r>>7;*r^=*r<<17;M31((*r%u64::from(corelib::field::P)) as u32)}
        fn k(r:&mut u64)->K{K{c0:CM31::new(m(r),m(r)),c1:CM31::new(m(r),m(r))}}
        for case in 0..1024 {
            let mut scales=core::array::from_fn::<_,Q,_>(|_|k(&mut rng));
            let mut xs=core::array::from_fn::<_,Q,_>(|_|m(&mut rng));
            let mut alphas=core::array::from_fn::<_,3,_>(|_|k(&mut rng));
            if case<3{
                let a=[K::ZERO,K::ONE,K::ONE.neg()][case];
                let x=[M31::ZERO,M31::ONE,M31(corelib::field::P-1)][case];
                scales=[a;Q];xs=[x;Q];alphas=[a;3];
            }
            let mut w=WeightAccumulator::empty(8);
            w.add_line_m31_batch(&scales,&xs).unwrap();
            for a in alphas{w.fold_deferred_relation_arity4(a);}
            let got=terminal(&w);
            for i in 0..4{assert_eq!(got[i],w.weight_at(i as u32));}
            let ordinary=core::array::from_fn::<_,4,_>(|_|k(&mut rng));
            let final4=core::array::from_fn::<_,4,_>(|_|k(&mut rng));
            let image=k(&mut rng);
            let lhs=(0..4).fold(K::ZERO,|s,i|s.add(ordinary[i].add(got[i]).mul(final4[i]))).add(image.mul(final4[3]));
            let rhs=(0..4).fold(K::ZERO,|s,i|s.add(ordinary[i].add(w.weight_at(i as u32)).mul(final4[i]))).add(image.mul(final4[3]));
            assert_eq!(lhs,rhs);
        }
        println!("TERMINAL_QUERY arbitrary_batches=1024 four_outputs=true shifted_scales_unchanged=true image_included=true");
    }
}
