pub enum QuerySampleError {
    /// Masking is exact only when the domain size is a nonzero power of two.
    BoundNotPowerOfTwo { bound: u32 },
    /// A without-replacement sample cannot contain more points than its domain.
    CountExceedsBound { count: usize, bound: u32 },
    /// The configured candidate-draw cap was reached before `count` distinct
    /// positions were accepted. This is an explicit completeness abort.
    DrawLimitExhausted { accepted: usize, max_draws: usize },
}
