//! P6 control reference: full arbitrary-slice compressor; cfg(kani) harness only.
use aspis_core::field::{M31,CM31,QM31};
pub fn compress(tag: M31, values: &[M31], lambda: QM31) -> QM31 {
    let mut out = QM31::from_cm31(CM31::from_m31(tag));
    let mut power = lambda;
    let mut i = 0usize;
    while i < values.len() {
        out = out.add(power.mul_m31(values[i]));
        power = power.mul(lambda);
        i = i.wrapping_add(1);
    }
    out
}
