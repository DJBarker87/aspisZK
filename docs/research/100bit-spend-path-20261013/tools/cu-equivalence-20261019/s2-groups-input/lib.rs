extern crate self as aspis_core;
pub mod field;
pub mod transport;
use field::{QM31 as K,WideExact as E};
use transport::Variant;
pub struct Weights {
    pub variant:Variant,
    pub factors:[[[K;4];5];5],
    pub points:[[K;10];3],
    pub extra:[K;2],
}
impl Weights {
    pub fn raw(&self,kind:usize,j:usize)->K {
        match kind {
            0=>if aspis_core::r0::opening::inactive(self.variant.row(j)).unwrap() {K::ONE} else {K::ZERO},
            4=>if j<56 { self.extra[j/28].pow((j%28) as u64) } else {K::ZERO},
            1..=3 if self.variant==Variant::D => {
                let r=self.variant.row(j);
                (0..10).fold(K::ONE,|v,b|v.mul(if r&(1<<b)==0 {K::ONE.sub(self.points[kind-1][9-b])}else{self.points[kind-1][9-b]}))
            },
            _=> {
                let k=if kind<4 {kind-1}else{kind-2};
                (0..5).fold(K::ONE,|v,d|v.mul(self.factors[k][d][(j>>(2*d))&3]))
            }
        }
    }
}
pub mod old;
pub mod new;
pub mod r0;
