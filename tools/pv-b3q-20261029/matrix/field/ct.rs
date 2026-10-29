//! Straight-line host candidate kernels. Arithmetic callers supply canonical
//! operands; reducers accept the full stated integer width. No allocation,
//! operand-indexed access, division, short circuit, or variable iteration.
use super::P;

#[inline(always)]
pub fn subtract_p(x: u32) -> u32 {
    let mask = 0u32.wrapping_sub((x >= P) as u32);
    x.wrapping_sub(P & mask)
}
#[inline(always)]
pub fn reduce64(x: u64) -> u32 {
    let x = (x & P as u64) + (x >> 31);
    let x = (x & P as u64) + (x >> 31);
    subtract_p(x as u32)
}
#[inline(always)]
pub fn reduce128(x: u128) -> u32 {
    let x = (x & P as u128) + (x >> 31);
    let x = (x & P as u128) + (x >> 31);
    let x = (x & P as u128) + (x >> 31);
    let x = (x & P as u128) + (x >> 31);
    subtract_p(x as u32)
}
#[inline(always)]
pub fn add(a: u32, b: u32) -> u32 {
    subtract_p(a.wrapping_add(b))
}
#[inline(always)]
pub fn sub(a: u32, b: u32) -> u32 {
    subtract_p(a.wrapping_add(P).wrapping_sub(b))
}
#[inline(always)]
pub fn neg(a: u32) -> u32 {
    let mask = 0u32.wrapping_sub((a != 0) as u32);
    P.wrapping_sub(a) & mask
}
#[inline(always)]
pub fn is_zero(a: u32) -> bool {
    a == 0
}
