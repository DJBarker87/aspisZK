//! Same prefix/backward kernel, one base inverse across both denominator lists.
//! Child module of circle_norm: uses the very same coefficient/point invariant.
use super::*;
pub(super) fn inverse(selected:&Selected,values:&[K],abc:[K;3],base:&[M31])->Result<(Vec<K>,Vec<M31>),Error>{
    let points=selected.points();
    if points.len()>Q || values.len()!=4*points.len() || base.len()!=2*points.len(){return Err(Error::Shape);}
    if values.is_empty() || values.iter().any(|v|*v==K::ZERO){return Err(Error::Domain);}
    let coeff=Coeff::new(abc);
    let norms:Vec<CM31>=points.iter().flat_map(|p|coeff.four(p.x,p.y)).collect();
    let mut all=Vec::with_capacity(norms.len()+base.len());
    for n in &norms{all.push(n.a.mul(n.a).add(n.b.mul(n.b)));}
    all.extend_from_slice(base);
    // Checks every norm and base denominator. No assumed nonzero suffix.
    let inv=batch_inverse_m(&all)?;
    let out=values.iter().zip(norms).zip(inv.iter()).map(|((v,n),d)|{
        let ni=CM31::new(n.a.mul(*d),n.b.neg().mul(*d));
        K{c0:v.c0.mul(ni),c1:v.c1.neg().mul(ni)}
    }).collect();
    // Borrow the tail at the caller; do not copy/split_off a second output Vec.
    Ok((out,inv))
}
#[cfg(test)]
mod tests{
    use super::*;
    fn values(abc:[K;3],pts:&[BaseCirclePoint])->Vec<K>{pts.iter().flat_map(|p|
        [(p.x,p.y),(p.x,p.y.neg()),(p.x.neg(),p.y.neg()),(p.x.neg(),p.y)]
        .map(|(x,y)|abc[0].add(abc[1].mul_m31(x)).add(abc[2].mul_m31(y)))).collect()}
    #[test]
    fn joined_matches_separate_and_zero_rejection(){
        let mut rng=0x6a6f_696e_6564_7638u64;
        fn m(r:&mut u64)->M31{*r^=*r<<13;*r^=*r>>7;*r^=*r<<17;M31((*r%u64::from(corelib::field::P)) as u32)}
        fn k(r:&mut u64)->K{K{c0:CM31::new(m(r),m(r)),c1:CM31::new(m(r),m(r))}}
        for case in 0..1024{
            let n=if case<22{case+1}else{Q};
            let ids:Vec<_>=(0..n).map(|i|((i*11719+case*131)%262144) as u32).collect();
            let selected=Selected::new(&ids).unwrap();let pts=selected.points();
            let mut abc=core::array::from_fn(|_|k(&mut rng));
            if case==0{abc=[K::ZERO;3];}
            if case==1{abc=[K::ONE;3];}
            if case%11==0{abc[0]=abc[1].mul_m31(pts[0].x).add(abc[2].mul_m31(pts[0].y)).neg();}
            let v=values(abc,pts);
            let mut base:Vec<_>=pts.iter().flat_map(|p|[p.x.double(),p.y.double()]).collect();
            if case%13==0{base[case%(2*n)]=M31::ZERO;}
            let old=selected.inverse(&v,abc).and_then(|a|batch_inverse_m(&base).map(|b|(a,b)));
            let joined=selected.inverse_joined(&v,abc,&base).map(|(a,b)|{
                assert_eq!(b.len(),6*n);
                for (x,y) in base.iter().zip(&b[4*n..]){assert_eq!(x.mul(*y),M31::ONE);}
                (a,b[4*n..].to_vec())
            });
            assert_eq!(joined,old);
        }
        // Every position of a general132-element list may be zero, even though
        // source-derived fold denominators have stronger invariants.
        for bad in 0..132{
            let mut all=vec![M31::ONE;132];all[bad]=M31::ZERO;
            let separate=batch_inverse_m(&all[..88]).and_then(|a|batch_inverse_m(&all[88..]).map(|b|(a,b)));
            assert_eq!(separate,Err(Error::Domain));assert_eq!(batch_inverse_m(&all),Err(Error::Domain));
        }
        for case in 0..512{
            let all:Vec<_>=(0..132).map(|_|{let x=m(&mut rng);if x==M31::ZERO{M31::ONE}else{x}}).collect();
            let joined=batch_inverse_m(&all).unwrap();
            assert_eq!(&joined[..88],batch_inverse_m(&all[..88]).unwrap());
            assert_eq!(&joined[88..],batch_inverse_m(&all[88..]).unwrap());
            for(x,y)in all.iter().zip(joined){assert_eq!(x.mul(y),M31::ONE);}
            if case==0{assert_eq!(batch_inverse_m(&vec![M31(corelib::field::P-1);132]).unwrap(),vec![M31(corelib::field::P-1);132]);}
        }
        let p=Selected::new(&[0]).unwrap();
        assert_eq!(p.inverse_joined(&[K::ONE;4],[K::ONE;3],&[M31::ONE]),Err(Error::Shape));
        assert_eq!(p.inverse_joined(&[K::ONE;3],[K::ONE;3],&[M31::ONE;2]),Err(Error::Shape));
        let empty=Selected::new(&[]).unwrap();
        assert_eq!(empty.inverse_joined(&[],[K::ZERO;3],&[]),Err(Error::Domain));
        println!("JOINED_INVERSE chord_profiles=1024 general_batches=512 zero_positions=132 lengths=1..22 shape_and_empty_rejection=true borrowed_tail=true");
    }
}
