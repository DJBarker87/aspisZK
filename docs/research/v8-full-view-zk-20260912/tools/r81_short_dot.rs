// Same retained R59 raw products and partial-fold bound, now at fixed arities.
// No private canonicality premise: every raw input and the affine constant
// is checked; the caller retains its exact original fallback on None.
#[inline(never)]
fn r81_short_dot<const N:usize>(left:&[QM31;N],right:&[QM31;N],constant:QM31)->Option<QM31>{
    if N<2 || N>4 {return None;}
    let c=[constant.c0.a.0,constant.c0.b.0,constant.c1.a.0,constant.c1.b.0];
    if c.iter().any(|&x|x>=P){return None;}
    let mut sums=c.map(u64::from);
    for i in 0..N {
        let raw=r59_raw_product(left[i],right[i])?;
        // The raw outputs fit u64. Each partial fold is <2^34; four
        // partial folds plus a canonical constant stay below 2^37.
        for j in 0..4 {
            sums[j]=sums[j].wrapping_add((raw[j]&u64::from(P)).wrapping_add(raw[j]>>31));
        }
    }
    let out=sums.map(M31::reduce_u64);
    Some(QM31{c0:CM31::new(out[0],out[1]),c1:CM31::new(out[2],out[3])})
}
