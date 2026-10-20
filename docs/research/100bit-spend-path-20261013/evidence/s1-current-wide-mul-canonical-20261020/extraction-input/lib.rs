pub mod field {
#[derive(Clone,Copy)]
pub struct M31(pub u32);
pub mod cm {use super::M31;
#[derive(Clone,Copy)]
pub struct CM31 {
    pub a: M31,
    pub b: M31,
}
impl CM31 {pub fn sub(self,_rhs:Self)->Self{unreachable!("opaque CM sub")}}
}
use cm::CM31;
#[derive(Clone,Copy)]
pub struct QM31 {
    pub c0: CM31,
    pub c1: CM31,
}
impl QM31 {
 pub fn add(self,_rhs:Self)->Self {unreachable!("opaque QM add")}
 pub fn sub(self, rhs: QM31) -> QM31 {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::KSub);
        QM31 {
            c0: self.c0.sub(rhs.c0),
            c1: self.c1.sub(rhs.c1),
        }
    }
 pub fn mul(self,_rhs:Self)->Self {unreachable!("opaque QM mul")}
}
pub fn mul_by_r(_x:CM31)->CM31 {unreachable!("opaque CM by-r")}
pub mod wide_exact {use super::{QM31,CM31};
#[derive(Clone,Copy)]
pub struct WideExact {
    c0: QM31,
    c1: QM31,
}
impl WideExact {
pub fn mul(self, rhs: Self) -> Self {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::EMul);
        #[cfg(all(feature = "r0-e4-reference", not(target_os = "solana")))]
        if crate::r0::equality_trace::is_reference() {
            return self.mul_re3(rhs);
        }
        let ac = self.c0.mul(rhs.c0);
        let bd = self.c1.mul(rhs.c1);
        let cross = self.c0.add(self.c1).mul(rhs.c0.add(rhs.c1));
        Self {
            c0: ac.add(mul_u(bd)),
            c1: cross.sub(ac).sub(bd),
        }
    }
}
fn mul_u(value: QM31) -> QM31 {
    QM31 {
        c0: super::mul_by_r(value.c1),
        c1: value.c0,
    }
}
}
}
pub fn wide_mul_entry(a:field::wide_exact::WideExact,b:field::wide_exact::WideExact)->field::wide_exact::WideExact{a.mul(b)}
