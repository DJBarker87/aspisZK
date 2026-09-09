//! Research control: polarize the QM31->CM31 norm once per public chord.
//! Six coefficients keep the identity valid even away from the circle.
use super::*;
use corelib::circle_fri::BaseCirclePoint;
fn times_r(z:CM31)->CM31{CM31::new(z.a.double().sub(z.b),z.a.add(z.b.double()))}
fn norm(v:K)->CM31{v.c0.square().sub(times_r(v.c1.square()))}
fn polar(v:K,w:K)->CM31{v.c0.mul(w.c0).sub(times_r(v.c1.mul(w.c1))).double()}
struct Coeff([CM31;6]);
impl Coeff{
    fn new([a,b,c]:[K;3])->Self{Self([norm(a),norm(b),norm(c),polar(a,b),polar(a,c),polar(b,c)])}
    #[inline]
    fn four(&self,x:M31,y:M31)->[CM31;4]{
        let c=&self.0;
        let even=c[0].add(c[1].mul_m31(x.mul(x))).add(c[2].mul_m31(y.mul(y)));
        let odd_x=c[3].mul_m31(x);let odd_y=c[4].mul_m31(y);let cross=c[5].mul_m31(x.mul(y));
        let positive=even.add(odd_x);let negative=even.sub(odd_x);
        let plus=odd_y.add(cross);let minus=odd_y.sub(cross);
        [positive.add(plus),positive.sub(plus),negative.sub(minus),negative.add(minus)]
    }
}
// Caller constructs values from these SAME abc/points in the original slot
// order. This helper is private; a supplied mismatching values vector is not
// a public hint or a new verifier API. Original zero guards remain below.
pub(super) fn inverse(values:&[K],abc:[K;3],points:&[BaseCirclePoint])->Result<Vec<K>,Error>{
    if points.len()>Q || values.len()!=4*points.len(){return Err(Error::Shape);}
    if values.is_empty() || values.iter().any(|v|*v==K::ZERO){return Err(Error::Domain);}
    let coeff=Coeff::new(abc);
    let norms:Vec<CM31>=points.iter().flat_map(|p|coeff.four(p.x,p.y)).collect();
    let norms_m:Vec<M31>=norms.iter().map(|n|n.a.mul(n.a).add(n.b.mul(n.b))).collect();
    let inv=batch_inverse_m(&norms_m)?;
    Ok(values.iter().zip(norms).zip(inv).map(|((v,n),d)|{
        let ni=CM31::new(n.a.mul(d),n.b.neg().mul(d));
        K{c0:v.c0.mul(ni),c1:v.c1.neg().mul(ni)}
    }).collect())
}
#[cfg(test)]
mod tests{
    use super::*;
    fn values(abc:[K;3],pts:&[BaseCirclePoint])->Vec<K>{pts.iter().flat_map(|p|
        [(p.x,p.y),(p.x,p.y.neg()),(p.x.neg(),p.y.neg()),(p.x.neg(),p.y)]
        .map(|(x,y)|abc[0].add(abc[1].mul_m31(x)).add(abc[2].mul_m31(y)))).collect()}
    fn check(abc:[K;3],pts:&[BaseCirclePoint]){
        let v=values(abc,pts);let cs=Coeff::new(abc);
        let actual:Vec<_>=pts.iter().flat_map(|p|cs.four(p.x,p.y)).collect();
        assert_eq!(actual,v.iter().copied().map(norm).collect::<Vec<_>>());
        let new=inverse(&v,abc,pts);assert_eq!(new,tower_inverse_k(&v));
        if let Ok(iv)=new{for (x,y) in v.iter().zip(iv){assert_eq!(x.mul(y),K::ONE);}}
    }
    #[test]
    fn arbitrary_chords_points_and_zero_denominators(){
        let mut rng=0x6e6f_726d_7336_7638u64;
        fn m(r:&mut u64)->M31{*r^=*r<<13;*r^=*r>>7;*r^=*r<<17;M31((*r%u64::from(corelib::field::P)) as u32)}
        fn k(r:&mut u64)->K{K{c0:CM31::new(m(r),m(r)),c1:CM31::new(m(r),m(r))}}
        for case in 0..1024{
            let mut abc=core::array::from_fn(|_|k(&mut rng));
            let mut pts:Vec<_>=(0..Q).map(|_|BaseCirclePoint{x:m(&mut rng),y:m(&mut rng)}).collect();
            if case==0{abc=[K::ZERO;3];}
            if case==1{abc=[K::ONE;3];}
            if (2..14).contains(&case){abc=[K::ZERO;3];let mut b=[M31::ZERO;4];b[(case-2)%4]=M31(corelib::field::P-1);abc[(case-2)/4]=K{c0:CM31::new(b[0],b[1]),c1:CM31::new(b[2],b[3])};}
            if case==14{abc=[K{c0:CM31::new(M31(corelib::field::P-1),M31(corelib::field::P-1)),c1:CM31::new(M31(corelib::field::P-1),M31(corelib::field::P-1))};3];}
            if case%7==0{pts[0]=BaseCirclePoint{x:M31::ZERO,y:M31::ZERO};}
            if case%11==0{abc[0]=abc[1].mul_m31(pts[3].x).add(abc[2].mul_m31(pts[3].y)).neg();}
            check(abc,&pts);
        }
        for seed in 0..16{
            let ids:Vec<_>=(0..Q).map(|i|((i*11719+seed*131)%262144) as u32).collect();
            let pts=corelib::circle_fri::selected_circle_fiber_points_shared(20,&ids).unwrap();
            check(core::array::from_fn(|_|k(&mut rng)),&pts);
        }
        assert_eq!(inverse(&[],[K::ZERO;3],&[]),Err(Error::Domain));
        assert_eq!(inverse(&[K::ONE],[K::ONE;3],&[]),Err(Error::Shape));
        let pts=vec![BaseCirclePoint{x:M31::ZERO,y:M31::ONE};Q+1];
        assert_eq!(inverse(&vec![K::ONE;4*(Q+1)],[K::ONE;3],&pts),Err(Error::Shape));
        println!("CHORD_NORM arbitrary_profiles=1024 actual_domain_profiles=16 slots=4 off_circle_supported=true zero_denominators_reject=true");
    }
}
