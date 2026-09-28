//! Checked dot boundary, preserving length and every canonicality check.
use aspis_core::field::QM31 as K;
#[inline(never)]
pub(super) fn dot(left:&[K],right:&[K])->Option<K> {
    aspis_core::field::r25_checked_dot(left,right)
}
