/// Canonical-only schoolbook tower product. The public caller retains its
/// original path whenever any limb is not canonical. No input check is waived.
#[inline(always)]
fn r24_canonical_mul(left:QM31,right:QM31)->Option<QM31> {
    let x=[left.c0.a.0,left.c0.b.0,left.c1.a.0,left.c1.b.0];
    let y=[right.c0.a.0,right.c0.b.0,right.c1.a.0,right.c1.b.0];
    if x.iter().chain(y.iter()).any(|&v|v>=P) {return None;}
    let [a,b,c,d]=x.map(u64::from);let [e,f,g,h]=y.map(u64::from);
    const PP:u64=(P as u64)*(P as u64);
    let reduce=|x|u64::from(M31::reduce_u64(x).0);
    // u,v are canonical. Every intermediate below is nonnegative and <2^64:
    // cg+PP-dh <= 2PP; ch+dg <=2(P-1)^2;
    // first output <=2PP+3P; second <=2(P-1)^2+3(P-1);
    // third <=2(P-1)^2+2PP; fourth <=4(P-1)^2.
    // The PP/2PP offsets dominate the subtracted canonical products.
    let u=reduce((c*g).wrapping_add(PP).wrapping_sub(d*h));
    let v=reduce((c*h).wrapping_add(d*g));
    let out=[
        (a*e).wrapping_add(PP).wrapping_sub(b*f).wrapping_add(2*u).wrapping_add(u64::from(P)).wrapping_sub(v),
        (a*f).wrapping_add(b*e).wrapping_add(u).wrapping_add(2*v),
        (a*g).wrapping_add(c*e).wrapping_add(2*PP).wrapping_sub(b*h).wrapping_sub(d*f),
        (a*h).wrapping_add(b*g).wrapping_add(c*f).wrapping_add(d*e)
    ].map(M31::reduce_u64);
    Some(QM31{c0:CM31::new(out[0],out[1]),c1:CM31::new(out[2],out[3])})
}

#[cold] #[inline(never)]
fn r24_noncanonical_mul(left:QM31,rhs:QM31)->QM31 {
        let m0 = left.c0.mul(rhs.c0);
        let m1 = left.c1.mul(rhs.c1);
        let m2 = left.c0.add(left.c1).mul(rhs.c0.add(rhs.c1));
        QM31 {
            c0: m0.add(mul_by_r(m1)),
            c1: m2.sub(m0).sub(m1),
        }
}
