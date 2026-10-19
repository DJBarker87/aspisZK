    /// Late-lift kernel: QM31 * M31 costs 2 scalar CM31 scalings.
    #[inline(always)]
    pub fn mul_m31(self, rhs: M31) -> QM31 {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::KMulF);
        QM31 {
            c0: self.c0.mul_m31(rhs),
            c1: self.c1.mul_m31(rhs),
        }
    }