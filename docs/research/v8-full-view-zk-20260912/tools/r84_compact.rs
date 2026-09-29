// New two-swap PROFILE only. Not an exact-output T163 replacement.
// Reuse the existing chord/block recurrence with the XOR-12 block moved to 4.
#[inline(never)]
fn r84_prepare(audit:&[K;11],abc:[K;3],alpha:[K;4],beta:K,finals:&[K;4],entries:&mut[K;4])->K {
    let z=core::array::from_fn(|i|audit[i]);
    let points=corelib::v6_transcript::v6_statement_points(&z);
    let k=audit[10];let k2=k.square();let k3=k2.mul(k);let first=K::ONE.sub(beta).mul(k);
    let powers=alpha.map(|x|{let square=x.square();(square,square.mul(x))});
    let mut plain=K::ZERO;entries.fill(K::ZERO);
    for r in 0..2 {
        let original:[K;10]=core::array::from_fn(|b|points[r][9-b]);
        let p=[original[0],original[4],original[5],original[6],original[7],original[8],original[9],
            K::ONE.sub(original[1]),K::ONE.sub(original[2]),K::ONE.sub(original[3])];
        let pairs=core::array::from_fn(|b|[K::ONE.sub(p[b]),p[b]]);
        let mut blocks=[K::ZERO;20];
        for b in 0..5 {for d in 0..4 {blocks[4*b+d]=pairs[2*b][d&1].mul(pairs[2*b+1][d>>1]);}}
        let high:[K;4]=blocks[16..20].try_into().unwrap();
        for d in 0..4 {blocks[16+d]=if r==0 {
            corelib::field::qm31_sum_products2([first,k3],[high[d],high[d^3]])
        }else{k2.mul(high[d])};}
        plain=plain.add(r83_block_terminal(&pairs,alpha,abc,&blocks,&powers,finals));
        for (i,j) in [127usize,1023,126,1021].into_iter().enumerate() {
            let mut entry=blocks[j&3];
            for b in 1..5 {entry=entry.mul(blocks[4*b+((j>>(2*b))&3)]);}
            entries[i]=entries[i].add(entry);
        }
    }
    plain
}
#[inline(always)]
fn r84_coordinate(row:usize,normal:&[K;16],carry:&[K;3],hb:&[K])->K {
    let low=row&15;let group=row>>4;let mut value=normal[low].mul(hb[group]);
    if low<3 {value=value.add(carry[low].mul(hb[64+group]));}
    for _ in 0..8 {value=value.half();}value
}
#[inline(never)]
pub(super) fn terminal_scalar(audit:&[K;11],abc:[K;3],alpha:[K;4],beta:K,
    finals:&[K;4],workspace:&mut[K],kernel:&r17_weighted_groups::Kernel)->K {
    assert!(workspace.len()>=531);let hb=&mut workspace[403..531];
    let (normal,carry,high)=kernel.geometry_parts();scalar_geometry(high,finals,hb);
    let mut entries=[K::ZERO;4];let plain=r84_prepare(audit,abc,alpha,beta,finals,&mut entries);
    let coordinates=[127usize,1023,126,1021].map(|row|r84_coordinate(row,normal,carry,hb));
    let correction=corelib::field::qm31_sum_products2(
        [entries[1].sub(entries[0]),entries[3].sub(entries[2])],
        [coordinates[0].sub(coordinates[1]),coordinates[2].sub(coordinates[3])]);
    let mut inactive=[K::ZERO;19];r24_inactive_values(hb,&mut inactive);
    // Original pivot 1023 is BASE code coordinate 127, before either swap.
    plain.add(correction).sub(entries[0].mul(scalar_low(normal,carry,&inactive))).add(coordinates[1])
}
