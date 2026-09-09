//! Four terminal query weights under the existing shifted relation grammar.
use super::*;
pub(super) fn terminal(weights:&WeightAccumulator)->[K;4] {
    weights.weight_prefix::<4>()
}
#[cfg(v8_terminal_fused)]
pub(super) fn scalar(ordinary:[K;4],query:[K;4],final4:&[K],image:K)->K {
    let mut weights=core::array::from_fn(|i|ordinary[i].add(query[i]));
    weights[3]=weights[3].add(image);
    corelib::field::qm31_sum_products4(weights,[final4[0],final4[1],final4[2],final4[3]])
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
            #[cfg(v8_terminal_fused)] assert_eq!(scalar(ordinary,got,&final4,image),rhs);
        }
        let mut shapes=0;
        for log in [2,4,6,8,10]{for count in [0,1,22]{for extra in [0,1,2]{
            let mut w=WeightAccumulator::empty(log);
            let scales=vec![k(&mut rng);count];let xs=vec![m(&mut rng);count];
            if count!=0{w.add_line_m31_batch(&scales,&xs).unwrap();}
            if extra==1{w.add_dense(vec![k(&mut rng);1usize<<log]).unwrap();}
            if extra==2{w.add_line_m31_tensor(k(&mut rng),m(&mut rng)).unwrap();}
            for _ in 0..(log-2)/2{w.fold_deferred_relation_arity4(k(&mut rng));}
            for (i,v) in terminal(&w).into_iter().enumerate(){assert_eq!(v,w.weight_at(i as u32));}
            for (i,v) in w.weight_prefix::<3>().into_iter().enumerate(){assert_eq!(v,w.weight_at(i as u32));}
            shapes+=1;
        }}}
        println!("TERMINAL_QUERY arbitrary_batches=1024 four_outputs=true shifted_scales_unchanged=true image_included=true");
        println!("TERMINAL_QUERY_SHAPES cases={shapes} empty_dense_tensor_multi=true halvings_0_to_8=true prefix3_fallback=true");
        #[cfg(v8_terminal_fused)] {
            let p=corelib::field::P-1;
            let max=K{c0:CM31::new(M31(p),M31(p)),c1:CM31::new(M31(p),M31(p))};
            for x in [K::ZERO,K::ONE,max] {
                let o=[x;4];let q=[max;4];let f=[max;4];
                let reference=(0..4).fold(K::ZERO,|s,i|s.add(o[i].add(q[i]).mul(f[i]))).add(x.mul(f[3]));
                assert_eq!(scalar(o,q,&f,x),reference);
            }
            println!("TERMINAL_IMAGE_FUSION arbitrary_scalars=1024 canonical_extremes=3 checked=true");
        }
    }
}
