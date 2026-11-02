// Entry adapters only; standard library bodies are not copied or rewritten.
pub fn range_next(mut r: core::ops::Range<usize>) -> (Option<usize>, core::ops::Range<usize>) {
    let item = r.next();
    (item, r)
}
pub fn inclusive_next(mut r: core::ops::RangeInclusive<usize>) -> (Option<usize>, core::ops::RangeInclusive<usize>) {
    let item = r.next();
    (item, r)
}
