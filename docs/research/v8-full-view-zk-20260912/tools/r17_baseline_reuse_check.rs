extern crate aspis_core as corelib;
use corelib::field::{QM31 as K,CM31,M31,P};
use corelib::sumcheck::WeightAccumulator;
const Q:usize=22;
#[derive(Debug,PartialEq)] enum Error {Shape,Domain}
// Installed verbatim from the baseline callback by the staging script.
include!("r17_reused_batch_inverse.rs");
#[path="circle_norm.rs"] mod circle_norm;
#[path="quotient_fold.rs"] mod quotient_fold;
#[path="affine_primal.rs"] mod affine_primal;
fn sample(n:u32)->K {
    K{c0:CM31::new(M31(n%P),M31((n*3+7)%P)),c1:CM31::new(M31((n*5+11)%P),M31((n*7+13)%P))}
}
fn main() {
    for case in 0..256usize {
        let ids:Vec<_>=(0..Q).map(|i|((i*11719+case*131)%262144) as u32).collect();
        let selected=circle_norm::Selected::new(&ids).unwrap();let pts=selected.points();
        let mut abc=core::array::from_fn(|j|sample((case*3+j) as u32));
        if case==0 {abc=[K::ZERO;3];}
        if case%11==0 {abc[0]=abc[1].mul_m31(pts[0].x).add(abc[2].mul_m31(pts[0].y)).neg();}
        let denoms:Vec<_>=pts.iter().flat_map(|p|[(p.x,p.y),(p.x,p.y.neg()),(p.x.neg(),p.y.neg()),(p.x.neg(),p.y)]
            .map(|(x,y)|abc[0].add(abc[1].mul_m31(x)).add(abc[2].mul_m31(y)))).collect();
        let mut base:Vec<_>=pts.iter().flat_map(|p|[p.x.double(),p.y.double()]).collect();
        if case%13==0 {base[case%(2*Q)]=M31::ZERO;}
        let xs:Vec<_>=pts.iter().map(|p|p.x.mul(p.x).double().sub(M31::ONE)).collect();
        let got=selected.inverse_lines(&denoms,abc,&base,&xs);
        if denoms.iter().any(|v|*v==K::ZERO) || base.iter().any(|v|*v==M31::ZERO) {
            assert_eq!(got,Err(Error::Domain));continue;
        }
        let (iv,ib)=got.unwrap();
        for i in 0..4*Q {assert_eq!(iv[i],denoms[i].try_inv().unwrap());}
        for i in 0..2*Q {assert_eq!(ib[i],base[i].inv());}
        let alpha=if case==1 {K::ZERO} else if case==2 {K::ONE} else {sample(case as u32+800)};
        let fold=quotient_fold::Prepared::new(alpha);
        // Two distinct arbitrary numerator channels consume the SAME inverses.
        for channel in 0..2 {for i in 0..Q {
            let q=core::array::from_fn(|j|sample((case*300+channel*100+i*4+j) as u32).mul(iv[4*i+j]));
            assert_eq!(fold.fold(q,ib[2*i],ib[2*i+1]),corelib::field::qm31_circle_to_line_fold4(q,alpha,ib[2*i],ib[2*i+1]));
        }}
    }
    for case in 0..64u32 {
        let alpha=if case==0 {K::ZERO} else if case==1 {K::ONE} else {sample(case+100)};
        let values:Vec<_>=(0..256).map(|i|sample(case*256+i)).collect();
        let expected:Vec<_>=values.chunks_exact(4).map(|v|v[0].add(alpha.mul(v[1].add(alpha.mul(v[2].add(alpha.mul(v[3]))))))).collect();
        assert_eq!(affine_primal::fold(&values,alpha),expected);
        let mut weights=WeightAccumulator::empty(8);
        weights.add_dense(values).unwrap();
        weights.add_line_m31_batch(&[sample(case+31);Q],&[M31(case+1);Q]).unwrap();
        for _ in 0..3 {weights.fold_deferred_relation_arity4(alpha);}
        let prefix=weights.weight_prefix::<4>();
        for i in 0..4 {assert_eq!(prefix[i],weights.weight_at(i as u32));}
        let finals=core::array::from_fn(|i|sample(case*4+i as u32));
        assert_eq!(corelib::field::qm31_sum_products4(prefix,finals),
            (0..4).fold(K::ZERO,|s,i|s.add(prefix[i].mul(finals[i]))));
    }
    println!("PASS: 256 shared two-channel inversion/fold profiles with zero-denominator controls; 64 affine-primal and mixed dense/query terminal controls");
}
