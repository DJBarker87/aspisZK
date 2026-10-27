use aspis_core::field::{M31,CM31,QM31,WideExact,P};
const TRACE_ROWS:usize=1024;
pub fn state_only_copy_helper_sum(h1: &[QM31]) -> Option<QM31> {
    if h1.len() == TRACE_ROWS {
        let mut sum = QM31::ZERO;
        let mut i = 0usize;
        while i < h1.len() { sum = sum.add(h1[i]); i += 1; }
        Some(sum)
    } else { None }
}
