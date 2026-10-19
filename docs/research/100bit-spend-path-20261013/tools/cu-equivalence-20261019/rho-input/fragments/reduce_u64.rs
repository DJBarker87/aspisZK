#[inline(always)]
fn reduce_u64(x: u64) -> u32 {
    // reference_canonical: two mask/shift folds bring any u64 to at most
    // P+3, then one conditional subtract canonicalizes. Supporting the full
    // u64 range lets four maximal M31 products be accumulated before one
    // reduction: 4*(P-1)^2 < 2^64.
    let x = (x & P as u64) + (x >> 31u32);
    let x = (x & P as u64) + (x >> 31u32);
    let x = x as u32;
    if x >= P {
        x - P
    } else {
        x
    }
}