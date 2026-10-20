/// Candidate exact accumulator for sums of `WideExact * QM31`.
/// Canonical QM31 coordinates and the 4096-term limit are checked at push.
pub struct EbyKDot {
    c0: canonical::Dot,
    c1: canonical::Dot,
    count: usize,
}