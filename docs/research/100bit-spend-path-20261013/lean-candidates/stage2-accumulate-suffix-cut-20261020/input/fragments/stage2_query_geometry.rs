/// The five base-field denominators used to fold one sampled query: circle
/// x/y, followed by line x/y/z. Their inverses are batch-computed once per
/// transaction so each query avoids five independent field inversions.
struct QueryGeometry { start:usize, inverses:Vec<[M31;5]>, line_z:Vec<M31> }