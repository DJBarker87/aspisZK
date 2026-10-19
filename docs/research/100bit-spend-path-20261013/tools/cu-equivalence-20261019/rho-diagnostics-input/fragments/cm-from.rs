    #[inline(always)]
    pub fn from_m31(a: M31) -> CM31 {
        CM31 { a, b: M31::ZERO }
    }