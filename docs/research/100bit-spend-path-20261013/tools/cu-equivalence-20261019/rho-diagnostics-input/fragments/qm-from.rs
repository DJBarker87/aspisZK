    #[inline(always)]
    pub fn from_cm31(c0: CM31) -> QM31 {
        QM31 { c0, c1: CM31::ZERO }
    }