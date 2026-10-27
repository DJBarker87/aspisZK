//! Owned-index P6 candidate; included by cfg(kani) proof parent only.
use aspis_core::field::QM31 as K;
use aspis_r1_cost_probe::{weights::Weights, transport::Variant};
pub fn row(variant:Variant,j:usize)->usize {
    if variant==Variant::D {return aspis_core::r0::transport::COEFFICIENT_TO_ROW[j] as usize;}
    let tau=[3usize,4,2,0,1];let mut out=0;let mut d=0;
    while d<5 {out |= ((j>>(2*d))&3) << (2*tau[d]);d+=1;}
    out
}
pub fn raw(w:&Weights,kind:usize,j:usize)->K {
    match kind {
        0=>{
            let r=row(w.variant,j);
            // The P6 domain j<1024 makes this panic branch unreachable.
            // Native panic-message correspondence outside the domain is not claimed.
            if r>=1024 {panic!("reference index out of range");}
            if (aspis_core::r0::opening::COPY_ACTIVE_ROW_MASKS[r/16] >> (r%16))&1==0 {K::ONE}else{K::ZERO}
        },
        4=>if j<56 {w.extra[j/28].pow((j%28) as u64)}else{K::ZERO},
        1..=3 if w.variant==Variant::D => {
            let r=row(w.variant,j);let mut v=K::ONE;let mut b=0;
            while b<10 {
                let x=if r&(1<<b)==0 {K::ONE.sub(w.points[kind-1][9-b])}else{w.points[kind-1][9-b]};
                v=v.mul(x);b+=1;
            }
            v
        },
        _=>{
            let k=if kind<4 {kind-1}else{kind-2};let mut v=K::ONE;let mut d=0;
            while d<5 {v=v.mul(w.factors[k][d][(j>>(2*d))&3]);d+=1;}
            v
        }
    }
}
