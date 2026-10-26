//! Owned steps; the parent and its inclusion are cfg(kani)-only.
use super::*;
pub fn c1_step(c1:&[QM31;16],coefficients:[QM31;27],column:usize)->[QM31;27] {
    let exponents:[usize;16]=[0,2,4,6,8,10,12,14,16,18,20,22,24,26,13,25];
    cell(coefficients,exponents[column],tower(c1[column],column&3))
}
pub fn mask_step(mask:&[QM31;10],coefficients:[QM31;27],column:usize)->[QM31;27] {
    let exponents:[usize;10]=[1,3,5,7,9,11,15,17,19,21];
    cell(coefficients,exponents[column],tower(mask[column],column&3))
}
pub fn linear_step(point:&[QM31;10],variable:usize,suffix:QM31,weighted:QM31)->(QM31,QM31) {
    let suffix=suffix.add(point[variable]);
    let weighted=if variable!=0 {weighted.add(suffix)} else {weighted};
    (suffix,weighted)
}
pub fn horner_step(coefficients:&[QM31;27],prepared:PreparedQm31Multiplier,exponent:usize,shared:QM31)->QM31 {
    prepared.mul(shared).add(coefficients[exponent])
}
pub fn tower_step(value:QM31,coordinate:usize)->QM31 {tower(value,coordinate)}
pub fn linears_step(point:&[QM31;10])->(QM31,QM31) {linears(*point)}
pub fn power26_step(value:QM31)->QM31 {
    let x2=value.square();let x4=x2.square();let x8=x4.square();let x16=x8.square();
    x16.mul(x8).mul(x2)
}
