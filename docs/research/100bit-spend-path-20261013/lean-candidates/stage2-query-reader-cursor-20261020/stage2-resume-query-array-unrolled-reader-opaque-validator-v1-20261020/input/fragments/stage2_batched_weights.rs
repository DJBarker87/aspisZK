/// Transaction-local residues. At a group boundary each limb is <2^34.
/// Four products add at most 4*(P-1)^2; adding the retained folded residue
/// still fits u64 because 4*(P-1)^2+2^34 < 2^64. Flush after each four queries.
struct BatchedWeights { raw:Vec<[u64;4]>, terms:usize }