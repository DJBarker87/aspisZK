use super::reference::{M31,CM31,QM31};
fn lift(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}
pub fn compress_tagged_tuple(tag: M31, values: &[M31], lambda: QM31) -> QM31 {
    let mut compressed = lift(tag);
    let mut power = lambda;
    for value in values {
        compressed = compressed.add(power.mul_m31(*value));
        power = power.mul(lambda);
    }
    compressed
}
