//! Borrow the SAME line-coordinate vector built by the callback's point loop.
//! No public hint: a mismatched line vector is not covered by the source contract.
use super::*;
struct LineCoeff([CM31;5]);
impl LineCoeff{
    fn new(abc:[K;3])->Self{
        let c=Coeff::new(abc).0;let half=c[1].half();
        Self([c[0].add(half),half,c[2],c[3],c[4]])
    }
    #[inline]
    fn four(&self,x:M31,y:M31,t:M31)->[CM31;4]{
        let c=&self.0;let even=c[0].add(c[1].mul_m31(t));
        let odd_x=c[2].mul_m31(x);let odd_y=c[3].mul_m31(y);let cross=c[4].mul_m31(x.mul(y));
        let positive=even.add(odd_x);let negative=even.sub(odd_x);
        let plus=odd_y.add(cross);let minus=odd_y.sub(cross);
        [positive.add(plus),positive.sub(plus),negative.sub(minus),negative.add(minus)]
    }
}
pub(super) fn inverse(selected:&Selected,values:&[K],abc:[K;3],base:&[M31],lines:&[M31])->Result<(Vec<K>,Vec<M31>),Error>{
    let points=selected.points();
    if points.len()>Q || values.len()!=4*points.len() || base.len()!=2*points.len() || lines.len()!=points.len(){return Err(Error::Shape);}
    if values.is_empty() || values.iter().any(|v|*v==K::ZERO){return Err(Error::Domain);}
    let coeff=LineCoeff::new(abc);
    let norms:Vec<CM31>=points.iter().zip(lines).flat_map(|(p,t)|coeff.four(p.x,p.y,*t)).collect();
    let norms_m:Vec<M31>=norms.iter().map(|n|n.a.mul(n.a).add(n.b.mul(n.b))).collect();
    let (inv,base_inv)=batch_two(&norms_m,base)?;
    let out=values.iter().zip(norms).zip(inv).map(|((v,n),d)|{
        let ni=CM31::new(n.a.mul(d),n.b.neg().mul(d));
        K{c0:v.c0.mul(ni),c1:v.c1.neg().mul(ni)}
    }).collect();
    Ok((out,base_inv))
}
#[cfg(test)]
mod tests{
    use super::*;
    fn values(abc:[K;3],pts:&[BaseCirclePoint])->Vec<K>{pts.iter().flat_map(|p|
        [(p.x,p.y),(p.x,p.y.neg()),(p.x.neg(),p.y.neg()),(p.x.neg(),p.y)]
        .map(|(x,y)|abc[0].add(abc[1].mul_m31(x)).add(abc[2].mul_m31(y)))).collect()}
    #[test]
    fn shared_line_matches_circle_norm(){
        let mut rng=0x6c69_6e65_6e6f_726du64;
        fn m(r:&mut u64)->M31{*r^=*r<<13;*r^=*r>>7;*r^=*r<<17;M31((*r%u64::from(corelib::field::P)) as u32)}
        fn k(r:&mut u64)->K{K{c0:CM31::new(m(r),m(r)),c1:CM31::new(m(r),m(r))}}
        for case in 0..1024{
            let n=if case<22{case+1}else{Q};
            let ids:Vec<_>=(0..n).map(|i|((i*11719+case*131)%262144) as u32).collect();
            let selected=Selected::new(&ids).unwrap();let pts=selected.points();
            let mut abc=core::array::from_fn(|_|k(&mut rng));
            if case==0{abc=[K::ZERO;3];}if case==1{abc=[K::ONE;3];}
            if case%11==0{abc[0]=abc[1].mul_m31(pts[0].x).add(abc[2].mul_m31(pts[0].y)).neg();}
            let v=values(abc,pts);
            let mut base:Vec<_>=pts.iter().flat_map(|p|[p.x.double(),p.y.double()]).collect();
            if case%13==0{base[case%(2*n)]=M31::ZERO;}
            let lines:Vec<_>=pts.iter().map(|p|p.x.mul(p.x).double().sub(M31::ONE)).collect();
            let c=LineCoeff::new(abc);let old=Coeff::new(abc);
            for(p,t)in pts.iter().zip(&lines){assert_eq!(c.four(p.x,p.y,*t),old.four(p.x,p.y));}
            assert_eq!(selected.inverse_lines(&v,abc,&base,&lines),inverse_split(&selected,&v,abc,&base));
        }
        // The affine identity also works at arbitrary base points, independently
        // of the circle-only justification of the preceding norm coefficients.
        for _ in 0..512{
            let abc=core::array::from_fn(|_|k(&mut rng));let x=m(&mut rng);let y=m(&mut rng);
            assert_eq!(LineCoeff::new(abc).four(x,y,x.mul(x).double().sub(M31::ONE)),Coeff::new(abc).four(x,y));
            let z=m(&mut rng);assert!(z.half().0<corelib::field::P);assert_eq!(z.half().double(),z);
        }
        for z in [0,1,2,3,(1<<30)-1,1<<30,(1<<30)+1,corelib::field::P-2,corelib::field::P-1]{
            assert_eq!(M31(z).half().double(),M31(z));
        }
        let c=LineCoeff::new([K::ZERO,K::ONE,K::ZERO]);
        assert_ne!(c.four(M31::ONE,M31::ZERO,M31::ZERO),Coeff::new([K::ZERO,K::ONE,K::ZERO]).four(M31::ONE,M31::ZERO));
        let p=Selected::new(&[0]).unwrap();
        assert_eq!(p.inverse_lines(&[K::ONE;4],[K::ONE;3],&[M31::ONE;2],&[]),Err(Error::Shape));
        let empty=Selected::new(&[]).unwrap();
        assert_eq!(empty.inverse_lines(&[],[K::ZERO;3],&[],&[]),Err(Error::Domain));
        println!("LINE_NORM chord_profiles=1024 arbitrary_point_profiles=512 lengths=1..22 mismatched_line_counterexample=true half_boundary_tests=9 zero_and_shape_rejection=true");
    }
}
