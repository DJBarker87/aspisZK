/// The same guarded schoolbook product with two noncanonical intermediates.
/// All input guards and final canonical reducers are retained.
#[inline(always)]
fn r24_canonical_mul(left:QM31,right:QM31)->Option<QM31> {
    let a=left.c0.a.0; let b=left.c0.b.0;
    let c=left.c1.a.0; let d=left.c1.b.0;
    let e=right.c0.a.0; let f=right.c0.b.0;
    let g=right.c1.a.0; let h=right.c1.b.0;
    if a>=P || b>=P || c>=P || d>=P || e>=P || f>=P || g>=P || h>=P {
        return None;
    }
    let a=a as u64; let b=b as u64; let c=c as u64; let d=d as u64;
    let e=e as u64; let f=f as u64; let g=g as u64; let h=h as u64;
    const PP:u64=(P as u64)*(P as u64);
    // A single fold preserves the residue but permits representatives <3P.
    // This closure is used only on the two bounded intermediates below.
    let partial=|x:u64|(x & u64::from(P)).wrapping_add(x>>31);
    let u=partial((c*g).wrapping_add(PP).wrapping_sub(d*h));
    let v=partial((c*h).wrapping_add(d*g));
    // u,v<3P. The 3P offset (not the old P offset) dominates v.
    // Every addition/subtraction is nonnegative and below 2^64 as an integer.
    // Final outputs still use the unchanged full-range canonical reducer.
    let out0=M31::reduce_u64(
        (a*e).wrapping_add(PP).wrapping_sub(b*f).wrapping_add(2*u).wrapping_add(3*u64::from(P)).wrapping_sub(v));
    let out1=M31::reduce_u64(
        (a*f).wrapping_add(b*e).wrapping_add(u).wrapping_add(2*v));
    let out2=M31::reduce_u64(
        (a*g).wrapping_add(c*e).wrapping_add(2*PP).wrapping_sub(b*h).wrapping_sub(d*f));
    let out3=M31::reduce_u64(
        (a*h).wrapping_add(b*g).wrapping_add(c*f).wrapping_add(d*e)
    );
    Some(QM31{c0:CM31::new(out0,out1),c1:CM31::new(out2,out3)})
}
