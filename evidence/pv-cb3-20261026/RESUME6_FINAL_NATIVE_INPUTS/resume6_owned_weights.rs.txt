//! Additive cfg(kani) P6 reference, separating each owned branch's loan scope.
use aspis_core::field::QM31 as K;
use aspis_r1_cost_probe::transport::Variant;
use crate::resume6_weights::OwnedWeights;

pub fn tensor(factors:[[[K;4];5];5],k:usize,j:usize)->K {
    let mut v=K::ONE;let mut d=0;
    while d<5 {let factor=factors[k][d][(j>>(2*d))&3];v=v.mul(factor);d+=1;}
    v
}
pub fn dense(points:[[K;10];3],kind:usize,row:usize)->K {
    let mut v=K::ONE;let mut b=0;
    while b<10 {
        let point=points[kind-1][9-b];
        let factor=if row&(1<<b)==0 {K::ONE.sub(point)}else{point};
        v=v.mul(factor);b+=1;
    }
    v
}
pub fn extra(extra:[K;2],j:usize)->K {
    if j<56 {let point=extra[j/28];point.pow((j%28) as u64)}else{K::ZERO}
}
pub fn mask(variant:Variant,j:usize)->K {
    let r=crate::resume6_weights::row(variant,j);
    if r>=1024 {panic!("reference index out of range");}
    if (aspis_core::r0::opening::COPY_ACTIVE_ROW_MASKS[r/16]>>(r%16))&1==0 {K::ONE}else{K::ZERO}
}
pub fn raw(w:OwnedWeights,kind:usize,j:usize)->K {
    match kind {
        0=>mask(w.variant,j),
        4=>extra(w.extra,j),
        1..=3 if w.variant==Variant::D=>dense(w.points,kind,crate::resume6_weights::row(w.variant,j)),
        _=>tensor(w.factors,if kind<4 {kind-1}else{kind-2},j),
    }
}
