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
pub(super) fn terminal_scalar(audit:&[K;11],abc:[K;3],alpha:[K;4],beta:K,
    finals:&[K;4],workspace:&mut[K],kernel:&r17_weighted_groups::Kernel)->K {
    assert!(workspace.len()>=531);
    let (factors,rest)=workspace.split_at_mut(240);let(delta,hb)=rest.split_at_mut(163);
    let plain=prepare_rows_scalar(audit,abc,alpha,beta,factors,finals);
    super::r22_tick("scalar.tensor_and_plain");
    let (normal,carry,high)=kernel.geometry_parts();scalar_geometry(high,finals,hb);
    super::r22_tick("scalar.adjoint_geometry");
    for j in 0..163 {delta[j]=entry(factors,0,SUPPORT[j]);}
    cycle(delta,&basis_transport::transport().order);
    super::r22_tick("scalar.permutation_values");
    let mut selected=[K::ZERO;19];
    for i in 0..163 {
        let row=SUPPORT[i];let group=row>>4;let low=row&15;let value=delta[i];
        selected[low]=selected[low].add(value.mul(hb[group]));
        if low<3 {selected[16+low]=selected[16+low].add(value.mul(hb[64+group]));}
    }
    let correction=scalar_low(normal,carry,&selected);
    super::r22_tick("scalar.permutation_contract");
    let t=basis_transport::transport();let mut inactive=[K::ZERO;19];
    for group in 0..64 {for low in 0..16 {
        let row=t.order[16*group+low];
        if row!=1023 && t.inactive[row] {
            inactive[low]=inactive[low].add(hb[group]);
            if low<3 {inactive[16+low]=inactive[16+low].add(hb[64+group]);}
        }
    }}
    let inactive=scalar_low(normal,carry,&inactive);
    let wp=entry(factors,0,1023);
    let mut pivot=normal[15].mul(hb[63]);for _ in 0..8 {pivot=pivot.half();}
    let result=plain.add(correction).sub(wp.mul(inactive)).add(pivot);
    super::r22_tick("scalar.inactive_pivot_final");result
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
