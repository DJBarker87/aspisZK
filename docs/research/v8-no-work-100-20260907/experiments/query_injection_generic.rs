//! Fixed q22 shifted query injection. No transcript, sampling or query change.
use super::*;
use corelib::field::{PreparedQm31Multiplier as P,qm31_dot};
fn scales(rho:K)->[K;Q] {
    let prepared=P::new(rho);
    let mut out=[rho;Q];
    for i in 1..Q{out[i]=prepared.mul(out[i-1]);}
    out
}
pub(super) fn inject(weights:&mut WeightAccumulator,c:&mut K,values:&[K;Q],xs:&[M31],rho:K)->Result<K,Error>{
    let scales=scales(rho);
    weights.add_line_m31_batch(&scales,xs).map_err(|_|Error::Shape)?;
    let inc=qm31_dot(&scales,values);
    *c=c.add(inc);
    Ok(inc)
}
#[cfg(test)]
mod tests {
    use super::*;
    fn reference(weights:&mut WeightAccumulator,c:&mut K,v:&[K],xs:&[M31],rho:K)->Result<K,Error>{
        let mut p=rho;let s:Vec<K>=(0..v.len()).map(|_|{let a=p;p=p.mul(rho);a}).collect();
        weights.add_line_m31_batch(&s,xs).map_err(|_|Error::Shape)?;
        let inc=dot(&s,v);*c=c.add(inc);Ok(inc)
    }
    fn compare_weights(a:&WeightAccumulator,b:&WeightAccumulator,n:usize){
        for i in 0..n{assert_eq!(a.weight_at(i as u32),b.weight_at(i as u32));}
    }
    #[test]
    fn shifted_claims_and_carried_weights_match(){
        let mut rng=0x7175_6572_792d_696eu64;
        fn m(r:&mut u64)->M31{*r^=*r<<13;*r^=*r>>7;*r^=*r<<17;M31((*r%u64::from(corelib::field::P)) as u32)}
        fn k(r:&mut u64)->K{K{c0:CM31::new(m(r),m(r)),c1:CM31::new(m(r),m(r))}}
        let max=K{c0:CM31::new(M31(corelib::field::P-1),M31(corelib::field::P-1)),c1:CM31::new(M31(corelib::field::P-1),M31(corelib::field::P-1))};
        for case in 0..512 {
            let mut rho=k(&mut rng);let mut values:[K;Q]=core::array::from_fn(|_|k(&mut rng));
            if case==0{rho=K::ZERO;values=[K::ZERO;Q];}
            if case==1{rho=K::ONE;values=[max;Q];}
            if case==2{rho=max;values=[max;Q];}
            let s=scales(rho);let mut old=rho;
            for x in s{assert_eq!(x,old);old=old.mul(rho);}
            assert_eq!(qm31_dot(&s,&values),dot(&s,&values));
            // The vector order and degree-q shift, not an unshifted rho^0 dot.
            let direct=values.iter().rev().fold(K::ZERO,|a,v|a.mul(rho).add(*v)).mul(rho);
            assert_eq!(qm31_dot(&s,&values),direct);
            let xs:[M31;Q]=core::array::from_fn(|_|m(&mut rng));
            let c=k(&mut rng);let (mut ca,mut cb)=(c,c);
            let (mut a,mut b)=(WeightAccumulator::empty(8),WeightAccumulator::empty(8));
            assert_eq!(inject(&mut a,&mut ca,&values,&xs,rho),reference(&mut b,&mut cb,&values,&xs,rho));
            assert_eq!(ca,cb);
            if case<32 {
                compare_weights(&a,&b,256);
                for (r,alpha) in core::array::from_fn::<_,3,_>(|_|k(&mut rng)).into_iter().enumerate(){
                    a.fold_deferred_relation_arity4(alpha);b.fold_deferred_relation_arity4(alpha);
                    compare_weights(&a,&b,256>>(2*(r+1)));
                }
            }
        }
        let mut shapes=0;
        for log in [0,2,8]{for n in [0,1,21,22,23]{for xlen in [0,1,21,22,23]{
            let values=vec![max;n];let xs=vec![M31::ONE;xlen];
            let (mut a,mut b)=(WeightAccumulator::empty(log),WeightAccumulator::empty(log));
            let (mut ca,mut cb)=(K::ONE,K::ONE);
            assert_eq!(super::super::inject(&mut a,&mut ca,&values,&xs,max),reference(&mut b,&mut cb,&values,&xs,max));
            assert_eq!(ca,cb);compare_weights(&a,&b,1usize<<log);shapes+=1;
        }}}
        println!("QUERY_INJECTION arbitrary_profiles=512 complete_weight_tails=32 shape_cases={shapes} rho_zero_one_max=true shifted_degree_q=true");
    }
}
