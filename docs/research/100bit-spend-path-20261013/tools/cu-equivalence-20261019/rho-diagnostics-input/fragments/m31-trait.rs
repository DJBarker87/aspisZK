    fn from_m31(value: M31) -> Self {
        M31(value.0 % P)
    }