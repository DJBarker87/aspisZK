#![no_std]

pub mod weights {

pub const S2_INACTIVE_GROUPS: [u8; 64] = [
    0,1,2,3,4,5,5,6,4,5,5,5,7,7,7,7,7,7,7,4,4,5,5,6,4,5,5,5,7,7,7,4,
    7,7,7,7,4,5,5,5,4,5,5,5,8,9,10,8,11,2,2,10,4,5,5,6,4,5,5,6,7,7,7,7,
];

pub const S2_INACTIVE_MASKS: [u16; 12] = [
    32769,49217,49280,16448,32767,16383,49151,65535,49152,57344,49216,33024,
];

/// Source-cut form of `weights.rs::s2_grouped_inactive_pair`.
///
/// The three loops, table lookups, branch, update order, and return expression
/// are preserved. The byte parser and concrete field methods are explicit
/// parameters: `coeff[j]` is the result of the production `field(f,j)` call,
/// while `zero/add/mul` stand for the production `E::ZERO/.add/.mul` methods.
pub trait FieldOps<E> {
    fn zero() -> E;
    fn add(a: E, b: E) -> E;
    fn mul(a: E, b: E) -> E;
}

pub fn s2_grouped_inactive_pair<E: Copy, O: FieldOps<E>>(
    coeff: &[E; 64],
    low: &[E; 16],
) -> E {
    let mut coefficients = [O::zero(); 12];
    for j in 0..64 {
        let group = S2_INACTIVE_GROUPS[j] as usize;
        coefficients[group] = O::add(coefficients[group], coeff[j]);
    }
    let mut pair = O::zero();
    for group in 0..12 {
        let mut weight = O::zero();
        for (bit, &challenge) in low.iter().enumerate() {
            if S2_INACTIVE_MASKS[group] & (1 << bit) != 0 {
                weight = O::add(weight, challenge);
            }
        }
        pair = O::add(pair, O::mul(coefficients[group], weight));
    }
    pair
}
}
