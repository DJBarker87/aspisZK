#![no_std]
extern crate alloc;
pub mod field;

pub fn qm31_add_mul_probe(
    x: field::QM31,
    y: field::QM31,
) -> (field::QM31, field::QM31) {
    (x.add(y), x.mul(y))
}
