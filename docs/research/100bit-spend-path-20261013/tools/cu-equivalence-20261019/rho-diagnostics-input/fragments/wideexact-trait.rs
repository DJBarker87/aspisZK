    fn from_m31(value: M31) -> Self {
        Self::from_qm31(<QM31 as CodeField>::from_m31(value))
    }