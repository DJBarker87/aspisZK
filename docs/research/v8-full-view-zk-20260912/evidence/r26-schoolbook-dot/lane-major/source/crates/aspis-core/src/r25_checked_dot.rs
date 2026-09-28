/// Checked whole-dot accumulator using sixteen schoolbook product channels.
/// No untrusted operand is consumed without checking every limb.
#[inline(never)]
pub fn r25_checked_dot(left:&[QM31],right:&[QM31])->Option<QM31> {
    if left.len()!=right.len() || left.len()>4096 {return None;}
    // Validate once before all pure immutable-array passes. The same inputs
    // are rejected even if another factor is zero; no callback is reordered.
    for (&a,&b) in left.iter().zip(right) {
        let x=[a.c0.a.0,a.c0.b.0,a.c1.a.0,a.c1.b.0,b.c0.a.0,b.c0.b.0,b.c1.a.0,b.c1.b.0];
        if x.iter().any(|&v|v>=P){return None;}
    }
    macro_rules! lane { ($lh:ident.$ll:ident,$rh:ident.$rl:ident) => {{
        let mut raw=0u64;let mut partial=0u64;
        for (index,(a,b)) in left.iter().zip(right).enumerate() {
            raw=raw.wrapping_add(u64::from(a.$lh.$ll.0)*u64::from(b.$rh.$rl.0));
            if index&3==3 {partial=partial.wrapping_add((raw&u64::from(P)).wrapping_add(raw>>31));raw=0;}
        }
        if left.len()&3!=0 {partial=partial.wrapping_add((raw&u64::from(P)).wrapping_add(raw>>31));}
        u64::from(M31::reduce_u64(partial).0)
    }}; }
    let partial=[
        lane!(c0.a,c0.a),
        lane!(c0.a,c0.b),
        lane!(c0.a,c1.a),
        lane!(c0.a,c1.b),
        lane!(c0.b,c0.a),
        lane!(c0.b,c0.b),
        lane!(c0.b,c1.a),
        lane!(c0.b,c1.b),
        lane!(c1.a,c0.a),
        lane!(c1.a,c0.b),
        lane!(c1.a,c1.a),
        lane!(c1.a,c1.b),
        lane!(c1.b,c0.a),
        lane!(c1.b,c0.b),
        lane!(c1.b,c1.a),
        lane!(c1.b,c1.b)];
    let [ae,af,ag,ah,be,bf,bg,bh,ce,cf,cg,ch,de,df,dg,dh]=partial;
    let p=u64::from(P);
    // Linear tower reconstruction. Offsets vanish mod P; every intermediate
    // is nonnegative and below 8P, so wrapping evaluation equals integers.
    let x=ae.wrapping_add(cg).wrapping_add(cg).wrapping_add(5*p)
        .wrapping_sub(bf).wrapping_sub(dh).wrapping_sub(dh).wrapping_sub(ch).wrapping_sub(dg);
    let y=af.wrapping_add(be).wrapping_add(cg).wrapping_add(ch).wrapping_add(ch)
        .wrapping_add(dg).wrapping_add(dg).wrapping_add(p).wrapping_sub(dh);
    let z=ag.wrapping_add(ce).wrapping_add(2*p).wrapping_sub(bh).wrapping_sub(df);
    let t=ah.wrapping_add(bg).wrapping_add(cf).wrapping_add(de);
    Some(QM31{c0:CM31::new(M31::reduce_u64(x),M31::reduce_u64(y)),
        c1:CM31::new(M31::reduce_u64(z),M31::reduce_u64(t))})
}
