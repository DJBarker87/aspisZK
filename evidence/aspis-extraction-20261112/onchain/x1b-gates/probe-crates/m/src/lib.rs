//! X1b planted positive for fault 1 (writes through a reversed mutable iterator) and its forward control.
/// Writes 0, 1, 2, 3 into a[3], a[2], a[1], a[0].
pub fn rev_write(a: &mut [u32; 4]) {
    for (i, x) in a.iter_mut().rev().enumerate() {
        *x = i as u32;
    }
}
/// Writes 0, 1, 2, 3 into a[0], a[1], a[2], a[3].
pub fn fwd_write(a: &mut [u32; 4]) {
    for (i, x) in a.iter_mut().enumerate() {
        *x = i as u32;
    }
}
/// The same as rev_write, over a slice.
pub fn rev_write_slice(a: &mut [u32]) {
    for x in a.iter_mut().rev() {
        *x = 7;
    }
}
