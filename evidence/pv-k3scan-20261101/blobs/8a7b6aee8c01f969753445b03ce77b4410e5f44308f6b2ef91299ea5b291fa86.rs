// Generated from the frozen source; check with generate.py --check.
use aspis_core::field::{M31,CM31,QM31};
fn lift(value:M31)->QM31 {QM31::from_cm31(CM31::from_m31(value))}
pub fn compress_tagged_tuple(tag: M31, values: &[M31], lambda: QM31) -> QM31 {
    let mut compressed = lift(tag);
    let mut power = lambda;
    for value in values {
        compressed = compressed.add(power.mul_m31(*value));
        power = power.mul(lambda);
    }
    compressed
}
#[inline(always)]
pub fn shipped_step(mut compressed:QM31,mut power:QM31,value:&M31,lambda:QM31)->(QM31,QM31) {
        compressed = compressed.add(power.mul_m31(*value));
        power = power.mul(lambda);
    (compressed,power)
}
pub fn reference_step(out:QM31,power:QM31,value:M31,lambda:QM31)->(QM31,QM31) {
    (out.add(power.mul_m31(value)),power.mul(lambda))
}
pub fn reference16(tag:M31,values:[M31;16],lambda:QM31)->QM31 {
    let mut state=(lift(tag),lambda);let mut i=0usize;
    while i<16 {state=reference_step(state.0,state.1,values[i],lambda);i+=1;}
    state.0
}
#[inline(always)]
pub fn owned_step_matched(mut compressed:QM31,mut power:QM31,value:&M31,lambda:QM31)->(QM31,QM31) {
        compressed = compressed.add(power.mul_m31(*value));
        power = power.mul(lambda);
    (compressed,power)
}

pub fn compress_fission(tag: M31, values: &[M31], lambda: QM31) -> QM31 {
    let mut compressed = lift(tag);
    let mut power = lambda;
    for value in values {
        (compressed,power)=shipped_step(compressed,power,value,lambda);
    }
    compressed
}
