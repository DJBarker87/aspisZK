    #[inline(always)]
    pub fn mul_m31(self, rhs: M31) -> CM31 {
        CM31 {
            a: self.a.mul(rhs),
            b: self.b.mul(rhs),
        }
    }