    fn from_m31(value: M31) -> Self {
        QM31::from_cm31(<CM31 as CodeField>::from_m31(value))
    }