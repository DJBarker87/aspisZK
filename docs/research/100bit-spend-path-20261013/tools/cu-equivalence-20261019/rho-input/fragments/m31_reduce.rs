    /// Canonically reduce any `u64`. This is used by four-term lazy dot
    /// products whose accumulator may exceed 2^62 but cannot overflow u64.
    #[inline(always)]
    pub fn reduce_u64(value: u64) -> M31 {
        M31(reduce_u64(value))
    }