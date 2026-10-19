    fn from_m31(value: M31) -> Self {
        CM31::from_m31(<M31 as CodeField>::from_m31(value))
    }