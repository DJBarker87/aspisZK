use aspis_core::field::{M31,CM31,QM31};
fn lift(value: M31) -> QM31 {
    QM31::from_cm31(CM31::from_m31(value))
}
pub fn compress_tagged_tuple(tag: M31, values: &[M31], lambda: QM31) -> QM31 {
    super::pole_proofs::event(10);
    let mut compressed = lift(tag);
    let mut power = lambda;
    for (index, value) in values.iter().enumerate() {
        super::pole_proofs::event(4000 + index as u32);
        compressed = compressed.add(power.mul_m31(*value));
        super::pole_proofs::event(11);
        power = power.mul(lambda);
    }
    compressed
}
