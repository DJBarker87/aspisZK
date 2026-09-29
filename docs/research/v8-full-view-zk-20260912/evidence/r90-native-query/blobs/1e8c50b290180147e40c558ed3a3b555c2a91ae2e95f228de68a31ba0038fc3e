//! Verifier-derived ordinary claim entries; no expanded weight vector.
//! Uses the SAME three source points, scales, inactive inventory and dual map.
use super::{corelib,basis_transport};
use corelib::field::QM31 as K;

#[inline(never)]
pub(super) fn ordinary_pair(z:&[K;10],kappa:K,use_x:bool)->[K;2] {
    let t=basis_transport::transport();
    let points=corelib::v6_transcript::v6_statement_points(z);
    let k2=kappa.square();let scales=[kappa,k2,k2.mul(kappa)];
    let entry=|index:usize| {
        let mut out=if t.inactive[index] {K::ONE}else{K::ZERO};
        for r in 0..3 {
            let mut v=scales[r];
            for bit in 0..10 {
                v=v.mul(if index&(1<<(9-bit))==0 {K::ONE.sub(points[r][bit])}else{points[r][bit]});
            }
            out=out.add(v);
        }
        out
    };
    let pivot=entry(1023);
    [0,if use_x {2}else{1}].map(|j| {
        let r=t.order[j];let v=entry(r);
        if r!=1023 && t.inactive[r] {v.sub(pivot)}else{v}
    })
}
