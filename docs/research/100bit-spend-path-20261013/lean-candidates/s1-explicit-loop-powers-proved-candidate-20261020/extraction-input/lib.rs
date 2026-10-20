pub mod field {
#[derive(Clone,Copy)]
pub struct M31(pub u32);
#[derive(Clone,Copy)]
pub struct CM31 {
    pub a: M31,
    pub b: M31,
}
#[derive(Clone,Copy)]
pub struct QM31 {
    pub c0: CM31,
    pub c1: CM31,
}
#[derive(Clone,Copy)]
pub struct WideExact {
    c0: QM31,
    c1: QM31,
}
impl QM31 {
pub const ZERO: QM31 = QM31 {
        c0: CM31 {
            a: M31(0),
            b: M31(0),
        },
        c1: CM31 {
            a: M31(0),
            b: M31(0),
        },
    };
pub const ONE: QM31 = QM31 {
        c0: CM31 {
            a: M31(1),
            b: M31(0),
        },
        c1: CM31 {
            a: M31(0),
            b: M31(0),
        },
    };
}
impl WideExact {
pub const ONE: Self = Self {
        c0: QM31::ONE,
        c1: QM31::ZERO,
    };
 pub fn mul(self,_rhs:Self)->Self {unreachable!("explicit opaque multiplication boundary")}
}
}
pub mod weights {use crate::field::WideExact as E;
pub fn powers<const N:usize>(x:E)->[E;N]{
 let mut out=[E::ONE;N];
 let mut p=E::ONE;
 let mut i=0usize;
 while i<N {
  out[i]=p;
  p=p.mul(x);
  i+=1;
 }
 out
}
}
pub fn powers_entry(x:field::WideExact)->[field::WideExact;29]{weights::powers::<29>(x)}
