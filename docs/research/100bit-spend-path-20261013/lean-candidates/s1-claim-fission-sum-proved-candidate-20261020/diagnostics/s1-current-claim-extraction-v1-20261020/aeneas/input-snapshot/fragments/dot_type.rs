    // Private canonical operands; bounded raw representatives, canonical result.
    // At most 4096 partial folds, each <2^34, sum <2^46. No u64 wrap.
    pub struct Dot { sums:[u64;4] }