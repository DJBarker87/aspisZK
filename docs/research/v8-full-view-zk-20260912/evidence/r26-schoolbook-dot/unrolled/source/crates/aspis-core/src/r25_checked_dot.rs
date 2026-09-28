/// Checked whole-dot accumulator using sixteen schoolbook product channels.
/// No untrusted operand is consumed without checking every limb.
#[inline(never)]
pub fn r25_checked_dot(left:&[QM31],right:&[QM31])->Option<QM31> {
    if left.len()!=right.len() || left.len()>4096 {return None;}
    let mut raw=[0u64;16];
    let mut partial=[0u64;16];
    for (index,(&a,&b)) in left.iter().zip(right).enumerate() {
        let x=[a.c0.a.0,a.c0.b.0,a.c1.a.0,a.c1.b.0];
        let y=[b.c0.a.0,b.c0.b.0,b.c1.a.0,b.c1.b.0];
        if x.iter().chain(y.iter()).any(|&v|v>=P){return None;}
        raw[0]=raw[0].wrapping_add(u64::from(x[0])*u64::from(y[0]));
        raw[1]=raw[1].wrapping_add(u64::from(x[0])*u64::from(y[1]));
        raw[2]=raw[2].wrapping_add(u64::from(x[0])*u64::from(y[2]));
        raw[3]=raw[3].wrapping_add(u64::from(x[0])*u64::from(y[3]));
        raw[4]=raw[4].wrapping_add(u64::from(x[1])*u64::from(y[0]));
        raw[5]=raw[5].wrapping_add(u64::from(x[1])*u64::from(y[1]));
        raw[6]=raw[6].wrapping_add(u64::from(x[1])*u64::from(y[2]));
        raw[7]=raw[7].wrapping_add(u64::from(x[1])*u64::from(y[3]));
        raw[8]=raw[8].wrapping_add(u64::from(x[2])*u64::from(y[0]));
        raw[9]=raw[9].wrapping_add(u64::from(x[2])*u64::from(y[1]));
        raw[10]=raw[10].wrapping_add(u64::from(x[2])*u64::from(y[2]));
        raw[11]=raw[11].wrapping_add(u64::from(x[2])*u64::from(y[3]));
        raw[12]=raw[12].wrapping_add(u64::from(x[3])*u64::from(y[0]));
        raw[13]=raw[13].wrapping_add(u64::from(x[3])*u64::from(y[1]));
        raw[14]=raw[14].wrapping_add(u64::from(x[3])*u64::from(y[2]));
        raw[15]=raw[15].wrapping_add(u64::from(x[3])*u64::from(y[3]));
        if index&3==3 {
            partial[0]=partial[0].wrapping_add((raw[0]&u64::from(P)).wrapping_add(raw[0]>>31)); raw[0]=0;
            partial[1]=partial[1].wrapping_add((raw[1]&u64::from(P)).wrapping_add(raw[1]>>31)); raw[1]=0;
            partial[2]=partial[2].wrapping_add((raw[2]&u64::from(P)).wrapping_add(raw[2]>>31)); raw[2]=0;
            partial[3]=partial[3].wrapping_add((raw[3]&u64::from(P)).wrapping_add(raw[3]>>31)); raw[3]=0;
            partial[4]=partial[4].wrapping_add((raw[4]&u64::from(P)).wrapping_add(raw[4]>>31)); raw[4]=0;
            partial[5]=partial[5].wrapping_add((raw[5]&u64::from(P)).wrapping_add(raw[5]>>31)); raw[5]=0;
            partial[6]=partial[6].wrapping_add((raw[6]&u64::from(P)).wrapping_add(raw[6]>>31)); raw[6]=0;
            partial[7]=partial[7].wrapping_add((raw[7]&u64::from(P)).wrapping_add(raw[7]>>31)); raw[7]=0;
            partial[8]=partial[8].wrapping_add((raw[8]&u64::from(P)).wrapping_add(raw[8]>>31)); raw[8]=0;
            partial[9]=partial[9].wrapping_add((raw[9]&u64::from(P)).wrapping_add(raw[9]>>31)); raw[9]=0;
            partial[10]=partial[10].wrapping_add((raw[10]&u64::from(P)).wrapping_add(raw[10]>>31)); raw[10]=0;
            partial[11]=partial[11].wrapping_add((raw[11]&u64::from(P)).wrapping_add(raw[11]>>31)); raw[11]=0;
            partial[12]=partial[12].wrapping_add((raw[12]&u64::from(P)).wrapping_add(raw[12]>>31)); raw[12]=0;
            partial[13]=partial[13].wrapping_add((raw[13]&u64::from(P)).wrapping_add(raw[13]>>31)); raw[13]=0;
            partial[14]=partial[14].wrapping_add((raw[14]&u64::from(P)).wrapping_add(raw[14]>>31)); raw[14]=0;
            partial[15]=partial[15].wrapping_add((raw[15]&u64::from(P)).wrapping_add(raw[15]>>31)); raw[15]=0;
        }
    }
    if left.len()&3!=0 {for k in 0..16 {
        partial[k]=partial[k].wrapping_add((raw[k]&u64::from(P)).wrapping_add(raw[k]>>31));
    }}
    partial[0]=u64::from(M31::reduce_u64(partial[0]).0);
    partial[1]=u64::from(M31::reduce_u64(partial[1]).0);
    partial[2]=u64::from(M31::reduce_u64(partial[2]).0);
    partial[3]=u64::from(M31::reduce_u64(partial[3]).0);
    partial[4]=u64::from(M31::reduce_u64(partial[4]).0);
    partial[5]=u64::from(M31::reduce_u64(partial[5]).0);
    partial[6]=u64::from(M31::reduce_u64(partial[6]).0);
    partial[7]=u64::from(M31::reduce_u64(partial[7]).0);
    partial[8]=u64::from(M31::reduce_u64(partial[8]).0);
    partial[9]=u64::from(M31::reduce_u64(partial[9]).0);
    partial[10]=u64::from(M31::reduce_u64(partial[10]).0);
    partial[11]=u64::from(M31::reduce_u64(partial[11]).0);
    partial[12]=u64::from(M31::reduce_u64(partial[12]).0);
    partial[13]=u64::from(M31::reduce_u64(partial[13]).0);
    partial[14]=u64::from(M31::reduce_u64(partial[14]).0);
    partial[15]=u64::from(M31::reduce_u64(partial[15]).0);
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
