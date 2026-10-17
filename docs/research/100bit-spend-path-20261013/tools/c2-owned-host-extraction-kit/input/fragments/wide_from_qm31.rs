    /// The field embedding `x -> x + 0*v`; canonicalizes raw QM31 limbs.
    #[inline(always)]
    pub fn from_qm31(value: QM31) -> Self {
        Self {
            c0: canonical_qm31(value),
            c1: QM31::ZERO,
        }
    }