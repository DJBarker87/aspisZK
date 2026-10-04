//! Shared-prefix evaluation of the existing big-endian multilinear weights.
//! Complementary children use p*(1-z) = p-p*z. No division, new rejection,
//! data-dependent zero skipping, or new mask/challenge is introduced.
use super::corelib::field::QM31 as K;

pub(super) fn fill(scale: K, point: &[K; 10], out: &mut [K; 1024]) {
    out[0] = scale;
    let mut width = 1;
    for &z in point {
        // Descending parents: writes at 2*i and 2*i+1 cannot destroy an unread
        // parent. Every slot is written before it is read, including dirty input.
        for i in (0..width).rev() {
            let parent = out[i];
            let right = parent.mul(z);
            out[2 * i] = parent.sub(right);
            out[2 * i + 1] = right;
        }
        width *= 2;
    }
}
