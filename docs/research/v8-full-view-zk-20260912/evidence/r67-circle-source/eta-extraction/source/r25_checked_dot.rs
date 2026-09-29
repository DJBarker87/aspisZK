// Raw outputs stay private to this checked dot.
/// The same guarded schoolbook product with two noncanonical intermediates.
/// All input guards and final canonical reducers are retained.
#[inline(always)]
fn r59_raw_product(left:QM31,right:QM31)->Option<[u64;4]> {
    let x=[left.c0.a.0,left.c0.b.0,left.c1.a.0,left.c1.b.0];
    let y=[right.c0.a.0,right.c0.b.0,right.c1.a.0,right.c1.b.0];
    if x.iter().chain(y.iter()).any(|&v|v>=P) {return None;}
    let [a,b,c,d]=x.map(u64::from);let [e,f,g,h]=y.map(u64::from);
    const PP:u64=(P as u64)*(P as u64);
    // A single fold preserves the residue but permits representatives <3P.
    // This closure is used only on the two bounded intermediates below.
    let partial=|x:u64|(x & u64::from(P)).wrapping_add(x>>31);
    let u=partial((c*g).wrapping_add(PP).wrapping_sub(d*h));
    let v=partial((c*h).wrapping_add(d*g));
    // u,v<3P. The 3P offset (not the old P offset) dominates v.
    // Every addition/subtraction is nonnegative and below 2^64 as an integer.
    // Final outputs still use the unchanged full-range canonical reducer.
    let out=[
        (a*e).wrapping_add(PP).wrapping_sub(b*f).wrapping_add(2*u).wrapping_add(3*u64::from(P)).wrapping_sub(v),
        (a*f).wrapping_add(b*e).wrapping_add(u).wrapping_add(2*v),
        (a*g).wrapping_add(c*e).wrapping_add(2*PP).wrapping_sub(b*h).wrapping_sub(d*f),
        (a*h).wrapping_add(b*g).wrapping_add(c*f).wrapping_add(d*e)
    ];
    Some(out)
}

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
