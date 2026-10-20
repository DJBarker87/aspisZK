#![no_std]

pub mod field {
    #[derive(Clone, Copy)] pub struct M31(pub u32);
    #[derive(Clone, Copy)] pub struct CM31 { pub a: M31, pub b: M31 }
    #[derive(Clone, Copy)] pub struct QM31 { pub c0: CM31, pub c1: CM31 }
    #[derive(Clone, Copy)] pub struct WideExact { c0: QM31, c1: QM31 }
    impl QM31 {
        pub const ZERO: Self = Self { c0: CM31 { a:M31(0), b:M31(0) }, c1: CM31 { a:M31(0), b:M31(0) } };
        pub const ONE: Self = Self { c0: CM31 { a:M31(1), b:M31(0) }, c1: CM31 { a:M31(0), b:M31(0) } };
    }
    impl WideExact {
        pub const ZERO: Self = Self { c0: QM31::ZERO, c1: QM31::ZERO };
        pub fn add(self, _rhs: Self) -> Self { unreachable!("explicit opaque field add boundary") }
        pub fn mul(self, _rhs: Self) -> Self { unreachable!("explicit opaque field multiply boundary") }
    }
}

pub mod weights {
    use crate::field::WideExact as E;
    pub const S2_INACTIVE_GROUPS: [u8; 64] = [
        0,1,2,3,4,5,5,6,4,5,5,5,7,7,7,7,7,7,7,4,4,5,5,6,4,5,5,5,7,7,7,4,
        7,7,7,7,4,5,5,5,4,5,5,5,8,9,10,8,11,2,2,10,4,5,5,6,4,5,5,6,7,7,7,7,
    ];
    pub const S2_INACTIVE_MASKS: [u16; 12] = [32769,49217,49280,16448,32767,16383,49151,65535,49152,57344,49216,33024];
    // Extraction-only focused source cut: preserve table lookup and all loops;
    // the checked coefficient decoder is a [WideExact;64] input boundary.
    pub fn s2_grouped_inactive_pair(coeff: &[E;64], low: &[E;16]) -> E {
        let mut coefficients = [E::ZERO;12];
        for j in 0..64 {
            let group = S2_INACTIVE_GROUPS[j] as usize;
            coefficients[group] = coefficients[group].add(coeff[j]);
        }
        let mut pair = E::ZERO;
        for group in 0..12 {
            let mut weight = E::ZERO;
            for (bit, &challenge) in low.iter().enumerate() {
                if S2_INACTIVE_MASKS[group] & (1 << bit) != 0 {
                    weight = weight.add(challenge);
                }
            }
            pair = pair.add(coefficients[group].mul(weight));
        }
        pair
    }
}
