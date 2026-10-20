pub mod field {
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct M31(pub u32);
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct CM31 {
    pub a: M31,
    pub b: M31,
}
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct QM31 {
    pub c0: CM31,
    pub c1: CM31,
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WideExact {
    c0: QM31,
    c1: QM31,
}
impl CM31 { pub const ZERO: CM31 = CM31 {
        a: M31(0),
        b: M31(0),
    }; }
impl QM31 { pub const ZERO: QM31 = QM31 {
        c0: CM31 {
            a: M31(0),
            b: M31(0),
        },
        c1: CM31 {
            a: M31(0),
            b: M31(0),
        },
    }; }
impl WideExact {
 pub const ZERO: Self = Self {
        c0: QM31::ZERO,
        c1: QM31::ZERO,
    };
 #[inline(never)] pub fn add(self, _rhs: Self) -> Self { unreachable!("explicit opaque addition boundary") }
 #[inline(never)] pub fn mul(self, _rhs: Self) -> Self { unreachable!("explicit opaque multiplication boundary") }
}
}
pub mod weights {
use crate::field::WideExact as E;
const S2_INACTIVE_GROUPS:[u8;64]=[0,1,2,3,4,5,5,6,4,5,5,5,7,7,7,7,7,7,7,4,4,5,5,6,4,5,5,5,7,7,7,4,7,7,7,7,4,5,5,5,4,5,5,5,8,9,10,8,11,2,2,10,4,5,5,6,4,5,5,6,7,7,7,7];
const S2_INACTIVE_MASKS:[u16;12]=[32769,49217,49280,16448,32767,16383,49151,65535,49152,57344,49216,33024];
#[inline(never)] pub fn field(_bytes: &[u8], _i: usize) -> E { unreachable!("explicit opaque byte-field decoder boundary") }
#[inline(never)]
pub fn s2_grouped_inactive_pair(f:&[u8],low:&[E;16])->E {
    let mut coefficients=[E::ZERO;12];
    for j in 0..64 {
        let group=S2_INACTIVE_GROUPS[j] as usize;
        coefficients[group]=coefficients[group].add(field(f,j));
    }
    let mut pair=E::ZERO;
    for group in 0..12 {
        let mut weight=E::ZERO;
        for (bit,&challenge) in low.iter().enumerate() {
            if S2_INACTIVE_MASKS[group]&(1<<bit)!=0 {weight=weight.add(challenge);}
        }
        pair=pair.add(coefficients[group].mul(weight));
    }
    pair
}
}
