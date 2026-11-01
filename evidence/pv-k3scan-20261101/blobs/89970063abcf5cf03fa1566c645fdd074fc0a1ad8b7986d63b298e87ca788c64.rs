#![cfg(kani)]
//! Exact copied bodies from the shipped selected mask loops. The generator
//! checks each snippet against the frozen surrounding function before use.
use super::*;
pub fn c1_step(c1:&[QM31;16], mut coefficients:[QM31;27], column:usize)->[QM31;27] {
    coefficients[usize::from(FACTOR_EXPONENTS[column])] =
            mul_tower_basis(c1[column], column & 3);
    coefficients
}
pub fn mask_step(mask_only_c1:&[QM31;10], mut coefficients:[QM31;27], column:usize)->[QM31;27] {
    coefficients[usize::from(MASK_ONLY_FACTOR_EXPONENTS[column])] =
            mul_tower_basis(mask_only_c1[column], column & 3);
    coefficients
}
pub fn linear_step(point:&[QM31;10], variable:usize, mut suffix:QM31, mut weighted:QM31)->(QM31,QM31) {
    suffix = suffix.add(point[variable]);
        if variable != 0 {
            weighted = weighted.add(suffix);
        }
    (suffix,weighted)
}
pub fn horner_step(coefficients:&[QM31;27], prepared_linear:PreparedQm31Multiplier, exponent:usize, mut shared:QM31)->QM31 {
    shared = prepared_linear.mul(shared).add(coefficients[exponent]);
    shared
}
pub fn tower(value:QM31, coordinate:usize)->QM31 {mul_tower_basis(value,coordinate)}
pub fn linears(point:&[QM31;10])->(QM31,QM31) {selected_mask_linears(point)}
pub fn power26(value:QM31)->QM31 {mask_power_26(value)}
