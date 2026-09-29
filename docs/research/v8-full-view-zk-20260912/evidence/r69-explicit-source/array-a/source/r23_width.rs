/// Exact for ALL u64 operands: the fast branch proves product <= (2^32-1)^2
/// < 2^64. The fallback retains the original checked multiplication, including
/// its panic on overflow. This is not a canonical-only public field API.
#[inline(always)]
pub fn r23_product_u32_bounded(left:u64,right:u64)->u64 {
    if left <= u64::from(u32::MAX) && right <= u64::from(u32::MAX) {
        u64::from(left as u32) * u64::from(right as u32)
    } else {
        left * right
    }
}
