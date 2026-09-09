//! Same prefix/backward kernel, one base inverse across both denominator lists.
//! Child module of circle_norm: uses the very same coefficient/point invariant.
use super::*;
fn batch_two(xs:&[M31],ys:&[M31])->Result<(Vec<M31>,Vec<M31>),Error>{
    if xs.is_empty() || ys.is_empty() || xs.iter().chain(ys).any(|x|*x==M31::ZERO){return Err(Error::Domain);}
    let mut px=Vec::with_capacity(xs.len());px.push(xs[0]);
    for x in &xs[1..]{px.push(px.last().unwrap().mul(*x));}
    let mut py=Vec::with_capacity(ys.len());py.push(ys[0]);
    for y in &ys[1..]{py.push(py.last().unwrap().mul(*y));}
    let p=*px.last().unwrap();let q=*py.last().unwrap();
    let total=p.mul(q).inv();let mut ix=total.mul(q);let mut iy=total.mul(p);
    let mut ox=vec![M31::ZERO;xs.len()];
    for i in (1..xs.len()).rev(){ox[i]=px[i-1].mul(ix);ix=ix.mul(xs[i]);}ox[0]=ix;
    let mut oy=vec![M31::ZERO;ys.len()];
    for i in (1..ys.len()).rev(){oy[i]=py[i-1].mul(iy);iy=iy.mul(ys[i]);}oy[0]=iy;
    Ok((ox,oy))
}
pub(super) fn inverse_split(selected:&Selected,values:&[K],abc:[K;3],base:&[M31])->Result<(Vec<K>,Vec<M31>),Error>{
    let points=selected.points();
    if points.len()>Q || values.len()!=4*points.len() || base.len()!=2*points.len(){return Err(Error::Shape);}
    if values.is_empty() || values.iter().any(|v|*v==K::ZERO){return Err(Error::Domain);}
    let coeff=Coeff::new(abc);
    let norms:Vec<CM31>=points.iter().flat_map(|p|coeff.four(p.x,p.y)).collect();
    let norms_m:Vec<M31>=norms.iter().map(|n|n.a.mul(n.a).add(n.b.mul(n.b))).collect();
    let (inv,base_inv)=batch_two(&norms_m,base)?;
    let out=values.iter().zip(norms).zip(inv).map(|((v,n),d)|{
        let ni=CM31::new(n.a.mul(d),n.b.neg().mul(d));
        K{c0:v.c0.mul(ni),c1:v.c1.neg().mul(ni)}
    }).collect();
    Ok((out,base_inv))
}
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
            let joined=inverse(&selected,&v,abc,&base).map(|(a,b)|{
                assert_eq!(b.len(),6*n);
                for (x,y) in base.iter().zip(&b[4*n..]){assert_eq!(x.mul(*y),M31::ONE);}
                (a,b[4*n..].to_vec())
            });
            assert_eq!(joined,old);
            assert_eq!(inverse_split(&selected,&v,abc,&base),old);
        }
        // Every position of a general132-element list may be zero, even though
        // source-derived fold denominators have stronger invariants.
        for bad in 0..132{
            let mut all=vec![M31::ONE;132];all[bad]=M31::ZERO;
            let separate=batch_inverse_m(&all[..88]).and_then(|a|batch_inverse_m(&all[88..]).map(|b|(a,b)));
            assert_eq!(separate,Err(Error::Domain));assert_eq!(batch_inverse_m(&all),Err(Error::Domain));
            assert_eq!(batch_two(&all[..88],&all[88..]),Err(Error::Domain));
        }
        for case in 0..512{
            let all:Vec<_>=(0..132).map(|_|{let x=m(&mut rng);if x==M31::ZERO{M31::ONE}else{x}}).collect();
            let joined=batch_inverse_m(&all).unwrap();
            assert_eq!(&joined[..88],batch_inverse_m(&all[..88]).unwrap());
            assert_eq!(&joined[88..],batch_inverse_m(&all[88..]).unwrap());
            assert_eq!(batch_two(&all[..88],&all[88..]).unwrap(),(joined[..88].to_vec(),joined[88..].to_vec()));
            for(x,y)in all.iter().zip(joined){assert_eq!(x.mul(y),M31::ONE);}
            if case==0{assert_eq!(batch_inverse_m(&vec![M31(corelib::field::P-1);132]).unwrap(),vec![M31(corelib::field::P-1);132]);}
        }
        let p=Selected::new(&[0]).unwrap();
        assert_eq!(p.inverse_joined(&[K::ONE;4],[K::ONE;3],&[M31::ONE]),Err(Error::Shape));
        assert_eq!(p.inverse_joined(&[K::ONE;3],[K::ONE;3],&[M31::ONE;2]),Err(Error::Shape));
        let empty=Selected::new(&[]).unwrap();
        assert_eq!(empty.inverse_joined(&[],[K::ZERO;3],&[]),Err(Error::Domain));
        assert_eq!(batch_two(&[],&[M31::ONE]),Err(Error::Domain));
        assert_eq!(batch_two(&[M31::ONE],&[]),Err(Error::Domain));
        assert_eq!(batch_two(&[M31::ONE],&[M31::ONE]),Ok((vec![M31::ONE],vec![M31::ONE])));
        println!("JOINED_INVERSE chord_profiles=1024 general_batches=512 zero_positions=132 lengths=1..22 shape_and_empty_rejection=true borrowed_tail=true");
    }
}
