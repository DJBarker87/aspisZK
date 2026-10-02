97:     /// Reduce an integer known to fit below 2^62 into canonical M31 form.
98:     ///
99:     /// This is the lazy-accumulation boundary used by SBF-specialized linear
100:     /// layers: several additions or small-constant products can be performed
101:     /// in `u64` and canonicalized once instead of after every operation.
102:     #[inline(always)]
103:     pub fn reduce_u62(value: u64) -> M31 {
104:         debug_assert!(value < (1u64 << 62));
105:         M31(reduce_u64(value))
106:     }
107: 
108:     /// Canonically reduce any `u64`. This is used by four-term lazy dot
109:     /// products whose accumulator may exceed 2^62 but cannot overflow u64.
110:     #[inline(always)]
111:     pub fn reduce_u64(value: u64) -> M31 {
112:         M31(reduce_u64(value))
