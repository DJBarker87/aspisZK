//! Shared-prefix evaluation of the existing big-endian multilinear weights.
//! Each leaf keeps the original multiplication order. No division, zero-case
//! exception, reassociation, or field-distributivity rewrite is needed.
use super::corelib::field::QM31 as K;

pub(super) fn fill(scale: K, point: &[K; 10], out: &mut [K; 1024]) {
    out[0] = scale;
    let mut width = 1;
    for &z in point {
        let left_factor = K::ONE.sub(z);
        // Descending parents: writes at 2*i and 2*i+1 cannot destroy an unread
        // parent. Every slot is written before it is read, including dirty input.
        for i in (0..width).rev() {
            let parent = out[i];
            out[2 * i] = parent.mul(left_factor);
            out[2 * i + 1] = parent.mul(z);
        }
        width *= 2;
    }
}
