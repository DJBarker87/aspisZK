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

// Two independent 32-bit lanes, each input in [0,P]. This inclusive bound
// deliberately preserves the old single-subtraction result even for P itself.
#[inline(always)] fn r24_pack(c:CM31)->u64 {u64::from(c.a.0)|(u64::from(c.b.0)<<32)}
#[inline(always)] fn r24_unpack(x:u64)->CM31 {CM31::new(M31(x as u32),M31((x>>32) as u32))}
#[inline(always)] fn r24_reduce_pair(x:u64)->u64 {
    // Each lane is <=2P, so adding one cannot cross a lane boundary.
    // A lane's bit31 after +1 is set exactly when its original value >=P.
    let high=x.wrapping_add(0x0000000100000001)&0x8000000080000000;
    x.wrapping_sub(high.wrapping_sub(high>>31))
}
#[inline(always)] fn r24_packed_pair(left:QM31,right:QM31,subtract:bool)->Option<QM31> {
    let bits=left.c0.a.0|left.c0.b.0|left.c1.a.0|left.c1.b.0|
        right.c0.a.0|right.c0.b.0|right.c1.a.0|right.c1.b.0;
    if bits&0x80000000!=0 {return None;}
    let pair=|a:CM31,b:CM31| {
        let (a,b)=(r24_pack(a),r24_pack(b));
        // For subtraction each lane a+P >= b; for addition a+b <=2P.
        // Thus no borrow/carry passes between lanes and no u64 wrap occurs.
        let raw=if subtract {a.wrapping_add(0x7fffffff7fffffff).wrapping_sub(b)}else{a.wrapping_add(b)};
        r24_unpack(r24_reduce_pair(raw))
    };
    Some(QM31{c0:pair(left.c0,right.c0),c1:pair(left.c1,right.c1)})
}
