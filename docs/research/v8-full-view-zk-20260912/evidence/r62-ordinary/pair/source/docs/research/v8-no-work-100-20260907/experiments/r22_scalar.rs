// Included inside the actual r19_channel_ordinary module. T163 is unchanged.
fn scalar_geometry(high:&[K;16], finals:&[K;4], out:&mut[K]) {
    assert!(out.len()>=128);out[..128].fill(K::ZERO);
    for j in 0..64 {out[j]=high[j&15].mul(finals[j>>4]);}
    // Adjoint of the EXACT nested-half carry read, including zero at row 64.
    for j in 0usize..64 {
        let mut value=out[j];let bits=j.trailing_ones() as usize;
        for bit in 0..bits {
            value=value.half();let row=j&!((1usize<<(bit+1))-1);
            out[64+row]=out[64+row].add(value);
        }
        if j+1<64 {out[64+j+1]=out[64+j+1].add(value);}
    }
}
fn scalar_low(normal:&[K;16],carry:&[K;3],values:&[K;19])->K {
    let mut out=corelib::field::qm31_dot(normal,&values[..16]);
    out=out.add(corelib::field::qm31_sum_products3([carry[0],carry[1],carry[2]],[values[16],values[17],values[18]]));
    for _ in 0..8 {out=out.half();}out
}
#[inline(never)]
pub(super) fn terminal_scalar(audit:&[K;11],abc:[K;3],alpha:[K;4],beta:K,
    finals:&[K;4],workspace:&mut[K],kernel:&r17_weighted_groups::Kernel)->K {
    assert!(workspace.len()>=531);
    let (factors,rest)=workspace.split_at_mut(240);let(delta,hb)=rest.split_at_mut(163);
    let plain=prepare_rows_scalar(audit,abc,alpha,beta,factors,finals);
    let (normal,carry,high)=kernel.geometry_parts();scalar_geometry(high,finals,hb);
    for j in 0..163 {delta[j]=r62_entry(factors,SUPPORT[j]);}
    cycle(delta,&basis_transport::transport().order);
    let mut selected=[K::ZERO;19];
    for i in 0..163 {
        let row=SUPPORT[i];let group=row>>4;let low=row&15;let value=delta[i];
        selected[low]=selected[low].add(value.mul(hb[group]));
        if low<3 {selected[16+low]=selected[16+low].add(value.mul(hb[64+group]));}
    }
    let correction=scalar_low(normal,carry,&selected);
    let mut inactive=[K::ZERO;19];r24_inactive_values(hb,&mut inactive);
    let inactive=scalar_low(normal,carry,&inactive);
    let wp=r62_entry(factors,1023);
    let mut pivot=normal[15].mul(hb[63]);for _ in 0..8 {pivot=pivot.half();}
    let result=plain.add(correction).sub(wp.mul(inactive)).add(pivot);result
}

#[cfg(not(target_os="solana"))]
pub(super) fn adjoint_check(abc:[K;3],alpha:[K;4],finals:&[K;4]) {
    let kernel=r17_weighted_groups::Kernel::new(abc,alpha);let(n,c,h)=kernel.geometry_parts();
    let mut hb=[K::ZERO;128];scalar_geometry(h,finals,&mut hb);
    for row in 0..1024 {
        let low=row&15;let group=row>>4;
        let mut actual=n[low].mul(hb[group]);if low<3 {actual=actual.add(c[low].mul(hb[64+group]));}
        for _ in 0..8 {actual=actual.half();}
        assert_eq!(actual,corelib::field::qm31_sum_products4(kernel.coordinate(row),*finals),"adjoint row {row}");
    }
}

#[inline(never)]
fn r24_inactive_values(hb:&[K],values:&mut[K;19]) {
    const MASKS:[u64;16]=[9079256850020433983, 9367487224930631679, 144115188075855871, 18446744073709551615, 9223372036854775807, 9367487224930631679, 144115188075855871, 9223372036854775807, 18446744073709551615, 144115188075855871, 144115188075855871, 18383693678993473567, 18302628891673493535, 9367487224859057663, 9367487224859189247, 9223372036785430271];
    const IDS:[usize;16]=[0, 1, 2, 3, 4, 1, 2, 4, 3, 2, 2, 5, 6, 7, 8, 9];
    const ENDS:[usize;11]=[0, 15, 21, 28, 28, 29, 44, 60, 71, 81, 87];
    const ROWS:[usize;87]=[0, 1, 2, 3, 4, 5, 25, 27, 30, 57, 58, 59, 60, 61, 62, 57, 58, 59, 60, 61, 62, 57, 58, 59, 60, 61, 62, 63, 63, 0, 1, 2, 3, 4, 26, 53, 56, 57, 58, 59, 60, 61, 62, 63, 0, 1, 2, 3, 4, 27, 29, 30, 32, 57, 58, 59, 60, 61, 62, 63, 9, 13, 18, 22, 26, 57, 58, 59, 60, 61, 62, 13, 17, 22, 26, 57, 58, 59, 60, 61, 62, 8, 13, 17, 21, 26, 63];
    const COMPLEMENT:[bool;10]=[false,true,true,true,true,false,false,true,true,true];
    #[cfg(not(target_os="solana"))] {
        let t=basis_transport::transport();
        for low in 0..16 {let mut mask=0u64;for g in 0..64 {let row=t.order[16*g+low];if row!=1023 && t.inactive[row]{mask|=1u64<<g;}}assert_eq!(mask,MASKS[low]);}
    }
    let total=hb[..64].iter().copied().fold(K::ZERO,|s,x|s.add(x));
    let mut shared=[K::ZERO;10];
    for i in 0..10 {
        let mut sum=K::ZERO;
        for j in ENDS[i]..ENDS[i+1] {sum=sum.add(hb[ROWS[j]]);}
        shared[i]=if COMPLEMENT[i]{total.sub(sum)}else{sum};
    }
    for low in 0..16 {values[low]=shared[IDS[low]];}
    let total_b=hb[64..128].iter().copied().fold(K::ZERO,|s,x|s.add(x));
    for low in 0..3 {
        let i=IDS[low];let mut sum=K::ZERO;
        for j in ENDS[i]..ENDS[i+1] {sum=sum.add(hb[64+ROWS[j]]);}
        values[16+low]=if COMPLEMENT[i]{total_b.sub(sum)}else{sum};
    }
}
