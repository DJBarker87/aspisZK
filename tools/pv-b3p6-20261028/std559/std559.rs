// Entry adapters only: no standard-library implementation is copied or rewritten.
use aspis_core::field::QM31;
pub fn range_nth(start: usize, end: usize, n: usize) -> (Option<usize>, usize, usize) {
    let mut r = start..end;
    let result = r.nth(n);
    (result, r.start, r.end)
}
pub fn array_read16(a: &[QM31; 16], start: usize, end: usize) -> &[QM31] {
    &a[start..end]
}
pub fn array_write4(a: &mut [QM31; 4], end: usize) -> &mut [QM31] {
    &mut a[..end]
}
pub fn copy_qm31(dest: &mut [QM31], source: &[QM31]) {
    dest.copy_from_slice(source);
}
