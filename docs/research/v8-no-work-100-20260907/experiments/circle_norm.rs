//! Circle-only specialization of the retained six-coefficient norm.
//! No prover-provided point can construct Selected; its fields are private.
use super::*;
use corelib::circle_fri::BaseCirclePoint;
fn times_r(z:CM31)->CM31{CM31::new(z.a.double().sub(z.b),z.a.add(z.b.double()))}
fn norm(v:K)->CM31{v.c0.square().sub(times_r(v.c1.square()))}
fn polar(v:K,w:K)->CM31{v.c0.mul(w.c0).sub(times_r(v.c1.mul(w.c1))).double()}
struct Coeff([CM31;5]);
impl Coeff{
    fn new([a,b,c]:[K;3])->Self{
        let nc=norm(c);
        Self([norm(a).add(nc),norm(b).sub(nc),polar(a,b),polar(a,c),polar(b,c)])
    }
    #[inline]
    fn four(&self,x:M31,y:M31)->[CM31;4]{
        let c=&self.0;
        let even=c[0].add(c[1].mul_m31(x.mul(x)));
        let odd_x=c[2].mul_m31(x);let odd_y=c[3].mul_m31(y);let cross=c[4].mul_m31(x.mul(y));
        let positive=even.add(odd_x);let negative=even.sub(odd_x);
        let plus=odd_y.add(cross);let minus=odd_y.sub(cross);
        [positive.add(plus),positive.sub(plus),negative.sub(minus),negative.add(minus)]
    }
}
pub(super) struct Selected(Vec<BaseCirclePoint>);
impl Selected{
    pub(super) fn new(queries:&[u32])->Result<Self,Error>{
        Ok(Self(corelib::circle_fri::selected_circle_fiber_points_shared(20,queries).map_err(|_|Error::Domain)?))
    }
    pub(super) fn points(&self)->&[BaseCirclePoint]{&self.0}
    // Sole non-test caller constructs denoms from SAME abc and self.points().
    // An immutable borrow prevents replacing the validated point collection.
    pub(super) fn inverse(&self,values:&[K],abc:[K;3])->Result<Vec<K>,Error>{
        if self.0.len()>Q || values.len()!=4*self.0.len(){return Err(Error::Shape);}
        if values.is_empty() || values.iter().any(|v|*v==K::ZERO){return Err(Error::Domain);}
        let coeff=Coeff::new(abc);
        let norms:Vec<CM31>=self.0.iter().flat_map(|p|coeff.four(p.x,p.y)).collect();
        let norms_m:Vec<M31>=norms.iter().map(|n|n.a.mul(n.a).add(n.b.mul(n.b))).collect();
        let inv=batch_inverse_m(&norms_m)?;
        Ok(values.iter().zip(norms).zip(inv).map(|((v,n),d)|{
            let ni=CM31::new(n.a.mul(d),n.b.neg().mul(d));
            K{c0:v.c0.mul(ni),c1:v.c1.neg().mul(ni)}
        }).collect())
    }
}
#[cfg(test)]
mod tests{
    use super::*;
    fn values(abc:[K;3],pts:&[BaseCirclePoint])->Vec<K>{pts.iter().flat_map(|p|
        [(p.x,p.y),(p.x,p.y.neg()),(p.x.neg(),p.y.neg()),(p.x.neg(),p.y)]
        .map(|(x,y)|abc[0].add(abc[1].mul_m31(x)).add(abc[2].mul_m31(y)))).collect()}
    #[test]
    fn all_selected_points_and_arbitrary_chords(){
        let reference:Vec<u32>=include_str!("circle-window-points.json").split(|c:char|!c.is_ascii_digit())
            .filter(|s|!s.is_empty()).map(|s|s.parse().unwrap()).collect();
        let actual:Vec<u32>=[corelib::circle_fri::V6_CIRCLE_LOW6_WINDOW,
            corelib::circle_fri::V6_CIRCLE_MIDDLE6_WINDOW,corelib::circle_fri::V6_CIRCLE_HIGH6_WINDOW]
            .into_iter().flatten().flatten().collect();
        assert_eq!(actual,reference);
        assert!(actual.iter().all(|v|*v<corelib::field::P));
        // Exhaustive finite index/control-flow test, not QM31 enumeration.
        for start in (0..262144).step_by(512){
            let ids:Vec<_>=(start..start+512).collect();
            let selected=Selected::new(&ids).unwrap();
            for p in selected.points(){assert_eq!(p.x.mul(p.x).add(p.y.mul(p.y)),M31::ONE);}
        }
        assert!(matches!(Selected::new(&[262144]),Err(Error::Domain)));
        assert!(matches!(Selected::new(&[u32::MAX]),Err(Error::Domain)));
        assert!(matches!(Selected::new(&[0,262144,1]),Err(Error::Domain)));
        let mut rng=0x6372_636c_6535_7638u64;
        fn m(r:&mut u64)->M31{*r^=*r<<13;*r^=*r>>7;*r^=*r<<17;M31((*r%u64::from(corelib::field::P)) as u32)}
        fn k(r:&mut u64)->K{K{c0:CM31::new(m(r),m(r)),c1:CM31::new(m(r),m(r))}}
        for case in 0..1024{
            let ids:Vec<_>=(0..Q).map(|i|((i*11719+case*131)%262144) as u32).collect();
            let selected=Selected::new(&ids).unwrap();let pts=selected.points();
            let mut abc=core::array::from_fn(|_|k(&mut rng));
            if case==0{abc=[K::ZERO;3];}
            if case==1{abc=[K::ONE;3];}
            if (2..14).contains(&case){abc=[K::ZERO;3];let mut b=[M31::ZERO;4];b[(case-2)%4]=M31(corelib::field::P-1);abc[(case-2)/4]=K{c0:CM31::new(b[0],b[1]),c1:CM31::new(b[2],b[3])};}
            if case==14{abc=[K{c0:CM31::new(M31(corelib::field::P-1),M31(corelib::field::P-1)),c1:CM31::new(M31(corelib::field::P-1),M31(corelib::field::P-1))};3];}
            if case%11==0{abc[0]=abc[1].mul_m31(pts[3].x).add(abc[2].mul_m31(pts[3].y)).neg();}
            let v=values(abc,pts);let c=Coeff::new(abc);
            let ns:Vec<_>=pts.iter().flat_map(|p|c.four(p.x,p.y)).collect();
            assert_eq!(ns,v.iter().copied().map(norm).collect::<Vec<_>>());
            let iv=selected.inverse(&v,abc);
            assert_eq!(iv,chord_norm::inverse(&v,abc,pts));
            assert_eq!(iv,tower_inverse_k(&v));
            if let Ok(iv)=iv{for (x,y) in v.iter().zip(iv){assert_eq!(x.mul(y),K::ONE);}}
        }
        // Legal unit points with zero coordinates, not in selected domain.
        for (x,y) in [(M31::ZERO,M31::ONE),(M31::ONE,M31::ZERO),(M31::ZERO,M31::ONE.neg()),(M31::ONE.neg(),M31::ZERO)]{
            let abc=core::array::from_fn(|_|k(&mut rng));let pts=[BaseCirclePoint{x,y}];
            assert_eq!(Coeff::new(abc).four(x,y).to_vec(),values(abc,&pts).into_iter().map(norm).collect::<Vec<_>>());
        }
        assert_ne!(Coeff::new([K::ZERO,K::ZERO,K::ONE]).four(M31::ZERO,M31::ZERO),[CM31::ZERO;4]);
        let empty=Selected::new(&[]).unwrap();
        assert_eq!(empty.inverse(&[],[K::ZERO;3]),Err(Error::Domain));
        assert_eq!(empty.inverse(&[K::ONE],[K::ZERO;3]),Err(Error::Shape));
        let long=Selected::new(&vec![0;Q+1]).unwrap();
        assert_eq!(long.inverse(&vec![K::ONE;4*(Q+1)],[K::ONE;3]),Err(Error::Shape));
        println!("CIRCLE_NORM unit_domain_indices=262144 chord_profiles=1024 slots=4 legal_zero_coordinate_points=4 invalid_ids=3 zero_denominators_reject=true off_circle_counterexample=true");
    }
}
