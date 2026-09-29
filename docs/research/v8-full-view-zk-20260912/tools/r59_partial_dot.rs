/// Guard every input, retain R56's raw product reconstruction, accumulate
/// four residue representatives and canonicalize once at the dot boundary.
#[inline(never)]
pub fn r25_checked_dot(left:&[QM31],right:&[QM31])->Option<QM31> {
    if left.len()!=right.len() || left.len()>4096 {return None;}
    let mut sums=[0u64;4];
    for (&a,&b) in left.iter().zip(right) {
        let raw=r59_raw_product(a,b)?;
        // Each raw output fits u64 (retained R56 reconstruction bounds).
        // One Mersenne fold is <2^34; <=4096 terms give <2^46.
        for i in 0..4 {
            sums[i]=sums[i].wrapping_add((raw[i]&u64::from(P)).wrapping_add(raw[i]>>31));
        }
    }
    let out=sums.map(M31::reduce_u64);
    Some(QM31{c0:CM31::new(out[0],out[1]),c1:CM31::new(out[2],out[3])})
}
