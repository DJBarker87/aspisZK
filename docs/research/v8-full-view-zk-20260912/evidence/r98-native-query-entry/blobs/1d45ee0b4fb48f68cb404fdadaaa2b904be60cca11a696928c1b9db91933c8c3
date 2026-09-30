// Canonical inputs only. Seven integer products; no challenge inversion.
// P=2^31-1. Pair products <4(P-1)^2, all subtractions nonnegative.
// u<5P, v<3P; the largest biased sum is <4P^2+7P<2^64.
#[inline(always)]
fn r96_raw_square(x:[u32;4])->[u64;4] {
    const P:u64=0x7fff_ffff;const PP:u64=P*P;
    let [a,b,c,d]=x.map(u64::from);
    let partial=|x:u64|(x&P).wrapping_add(x>>31);
    let ab=(a+b).wrapping_mul(a+P-b);
    let u=partial((c+d).wrapping_mul(c+P-d));
    let v=partial((c*d).wrapping_mul(2));
    let ac=a*c;let bd=b*d;
    let cross=(a+b).wrapping_mul(c+d).wrapping_sub(ac).wrapping_sub(bd);
    [ab.wrapping_add(2*u).wrapping_add(3*P).wrapping_sub(v),
     (a*b).wrapping_mul(2).wrapping_add(u).wrapping_add(2*v),
     ac.wrapping_add(PP).wrapping_sub(bd).wrapping_mul(2),cross.wrapping_mul(2)]
}
