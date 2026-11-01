//! Host candidate kernels. No randomized checks; arbitrary u32 operands.
//! Two Mersenne folds suffice for every u64: the first is <= 5P+3,
//! the second <= P+7. One subtraction then produces the canonical residue.
pub const P: u64 = 0x7fff_ffff;
#[inline(always)]
pub fn reduce(x: u64) -> u32 {
    let x = (x & P) + (x >> 31);
    let x = (x & P) + (x >> 31);
    let x = x as u32;
    if x >= P as u32 { x - P as u32 } else { x }
}
#[inline(always)]
pub fn mul(x: u32, y: u32) -> u32 { reduce(x as u64 * y as u64) }
/// y is canonical, so x<y implies x+P fits u32 even for arbitrary x.
#[inline(always)]
pub fn sub_product(x: u32, s: u32, b: u32) -> u32 {
    let y = mul(s,b);
    if x >= y { x - y } else { x + P as u32 - y }
}
/// Exactly the old (acc + x*y % P) % P, including noncanonical u32 inputs.
#[inline(always)]
pub fn madd(acc: u32, x: u32, y: u32) -> u32 {
    reduce(acc as u64 + mul(x,y) as u64)
}
/// The bound permits <=2^20 canonical terms: sum <2^51, no u64 overflow.
/// Larger shapes keep the original checked accumulator and its failures.
pub const MAX_TERMS: usize = 1 << 20;
pub const TILE: usize = 8;
