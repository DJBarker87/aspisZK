use aspis_core::field::QM31;
const TRACE_ROWS: usize = 1024;
pub fn state_only_copy_helper_sum(h1: &[QM31]) -> Option<QM31> {
    (h1.len() == TRACE_ROWS).then(|| h1.iter().copied().fold(QM31::ZERO, QM31::add))
}
