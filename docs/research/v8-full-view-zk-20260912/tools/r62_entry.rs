// The scalar path consumes the sum of exactly two retained tensor entries.
// Use the existing, unchanged two-product primitive; no tensor assumption.
#[inline(always)]
fn r62_entry(f:&[K],j:usize)->K {
    corelib::field::qm31_sum_products2(
        [f[j&15],f[80+(j&15)]],
        [f[16+(j>>4)],f[96+(j>>4)]])
}

#[cfg(not(target_os="solana"))]
pub(super) fn r62_entry_check(x:&[K;24]) {
    let f:[K;160]=core::array::from_fn(|i|x[i%24]);
    for j in 0..1024 {assert_eq!(r62_entry(&f,j),entry(&f,0,j),"entry coordinate {j}");}
}
