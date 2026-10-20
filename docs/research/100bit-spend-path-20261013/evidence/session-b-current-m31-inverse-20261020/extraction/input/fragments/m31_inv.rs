    pub fn inv(self) -> M31 {
        #[cfg(feature = "r0-op-count")]
        let _count = crate::r0_op_count::enter(crate::r0_op_count::Op::FInv);
        assert!(self.0 != 0, "inverse of zero");

        // Build x^(2^k - 1) at k = 2, 4, 8, 16, 24, 28, 29.
        // The final exponent is 4*(2^29 - 1) + 1 = 2^31 - 3 = P - 2.
        // This takes 38 M31 multiplications instead of the generic binary
        // exponentiation's 61 for this fixed exponent.
        let t2 = self.mul(self).mul(self);
        let t4 = square_n(t2, 2).mul(t2);
        let t8 = square_n(t4, 4).mul(t4);
        let t16 = square_n(t8, 8).mul(t8);
        let t24 = square_n(t16, 8).mul(t8);
        let t28 = square_n(t24, 4).mul(t4);
        let t29 = t28.mul(t28).mul(self);
        let t30 = t29.mul(t29);
        t30.mul(t30).mul(self)
    }
