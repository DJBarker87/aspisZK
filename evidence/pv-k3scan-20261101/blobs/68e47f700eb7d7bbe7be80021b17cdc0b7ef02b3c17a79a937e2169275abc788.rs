use aspis_core::field::{M31,QM31};
// A single for-loop iteration with the actual slice iterator state retained.
// The live-element branch copies the original two statements verbatim.
pub fn iterator_state_step<'a>(mut iterator:core::slice::Iter<'a,M31>,mut compressed:QM31,mut power:QM31,lambda:QM31)->(bool,core::slice::Iter<'a,M31>,QM31,QM31) {
    match iterator.next() {
        None => (false,iterator,compressed,power),
        Some(value) => {
        compressed = compressed.add(power.mul_m31(*value));
        power = power.mul(lambda);
        (true,iterator,compressed,power)
        }
    }
}
