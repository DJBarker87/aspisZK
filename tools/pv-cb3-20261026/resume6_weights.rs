//! Owned-index P6 candidate; included by cfg(kani) proof parent only.
use aspis_core::field::QM31 as K;
use aspis_r1_cost_probe::{weights::Weights, transport::Variant};
pub fn raw(w:&Weights,kind:usize,j:usize)->K {
    match kind {
        0=>if aspis_core::r0::opening::inactive(w.variant.row(j)).unwrap() {K::ONE}else{K::ZERO},
        4=>if j<56 {w.extra[j/28].pow((j%28) as u64)}else{K::ZERO},
        1..=3 if w.variant==Variant::D => {
            let r=w.variant.row(j);let mut v=K::ONE;let mut b=0;
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
