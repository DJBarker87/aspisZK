//! Same chunks, same powers, same output: inject c0 into existing raw channels.
use super::*;
use corelib::field::{PreparedQm31Multiplier as P,qm31_add_sum_products3_prepared};
pub(super) fn fold(v:&[K],a:K)->Vec<K>{
    let a2=a.square();let ps=[P::new(a),P::new(a2),P::new(a2.mul(a))];
    v.chunks_exact(4).map(|c|qm31_add_sum_products3_prepared(c[0],&ps,&[c[1],c[2],c[3]])).collect()
}
#[cfg(test)]
mod tests{
    use super::*;
    #[test]
    fn actual_affine_kernel_and_three_passes_match(){
        let mut rng=0xaff1_7370_7269_6d61u64;
        fn m(r:&mut u64)->M31{*r^=*r<<13;*r^=*r>>7;*r^=*r<<17;M31((*r%u64::from(corelib::field::P)) as u32)}
        fn k(r:&mut u64)->K{K{c0:CM31::new(m(r),m(r)),c1:CM31::new(m(r),m(r))}}
        let max=K{c0:CM31::new(M31(corelib::field::P-1),M31(corelib::field::P-1)),c1:CM31::new(M31(corelib::field::P-1),M31(corelib::field::P-1))};
        for case in 0..4096{
            let mut c=k(&mut rng);let mut l=core::array::from_fn(|_|k(&mut rng));let mut r=core::array::from_fn(|_|k(&mut rng));
            if case==0{c=K::ZERO;l=[K::ZERO;3];r=[K::ZERO;3];}
            if case==1{c=max;l=[max;3];r=[max;3];}
            let p=l.map(P::new);
            let reference=l.into_iter().zip(r).fold(c,|s,(a,b)|s.add(a.mul(b)));
            assert_eq!(qm31_add_sum_products3_prepared(c,&p,&r),reference);
            assert_eq!(c.add(corelib::field::qm31_sum_products3_prepared(&p,&r)),reference);
        }
        for case in 0..256{
            let mut v:Vec<_>=(0..256).map(|_|k(&mut rng)).collect();
            if case==0{v.fill(K::ZERO);}if case==1{v.fill(max);}
            let a:[K;3]=if case<8{core::array::from_fn(|i|if case&(1<<i)==0{K::ZERO}else{K::ONE})}else{core::array::from_fn(|_|k(&mut rng))};
            let mut old=v.clone();let mut new=v;
            for alpha in a{new=fold(&new,alpha);old=primal_reference(&old,alpha);assert_eq!(new,old);}
            assert_eq!(new.len(),4);
        }
        for n in [0,1,2,3,4,5,15,16,17,63,64,65,255,256,257]{
            let v:Vec<_>=(0..n).map(|_|k(&mut rng)).collect();let a=k(&mut rng);
            assert_eq!(fold(&v,a),primal_reference(&v,a));
        }
        println!("AFFINE_PRIMAL arbitrary_products=4096 complete_three_passes=256 chunk_lengths=15 maximal_channels=true zero_challenges=true");
    }
}
