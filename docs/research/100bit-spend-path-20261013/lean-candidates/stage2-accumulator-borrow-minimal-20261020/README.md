# Mutable accumulator extraction minimization

Diagnostic candidate, isolated from production. The source reduces the actual failing loop to integer vectors and separates three possible triggers: mutation of one of two disjoint fields, a mutable helper call while an accumulator loop is active, and an observer call after the accumulator update. Results are interpreted only as Aeneas capability diagnostics; they are not a Rust semantic proof.
