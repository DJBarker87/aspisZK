//! Same compact ordinary functional in a consumed 1024-entry weight buffer.
//! No allocator calls after the source map has been initialized.
use super::{corelib,basis_transport,r17_weighted_groups};
use corelib::field::QM31 as K;
include!("r17_reused_block_terminal.rs");

#[inline(never)]
fn fill_tensor(pairs:&[[K;2];10],block1:[K;4],storage:&mut[K]) {
    assert_eq!(storage.len(),80);
    let blocks:[[K;4];5]=core::array::from_fn(|r|if r==1 {block1} else {
        core::array::from_fn(|d|pairs[2*r][d&1].mul(pairs[2*r+1][d>>1]))
    });
    for j in 0..16 {storage[j]=blocks[0][j&3].mul(blocks[1][j>>2]);}
    let common:[K;16]=core::array::from_fn(|j|blocks[2][j&3].mul(blocks[3][j>>2]));
    for j in 0..64 {storage[16+j]=common[j&15].mul(blocks[4][j>>4]);}
}
fn entry(factors:&[K],j:usize)->K {
    factors[j&15].mul(factors[16+(j>>4)])
        .add(factors[80+(j&15)].mul(factors[96+(j>>4)]))
}

#[inline(never)]
pub(super) fn terminal(audit:&[K;11],abc:[K;3],alpha:[K;4],workspace:&mut[K])->[K;4] {
    assert_eq!(workspace.len(),1024);
    let (delta,rest)=workspace.split_at_mut(479);
    let (factors,sums)=rest.split_at_mut(160);
    let t=basis_transport::transport();
    let z=core::array::from_fn(|i|audit[i]);
    let points=corelib::v6_transcript::v6_statement_points(&z);
    let pairs:[[[K;2];10];2]=core::array::from_fn(|r|
        core::array::from_fn(|i|[K::ONE.sub(points[r][9-i]),points[r][9-i]]));
    let raw:[[K;4];2]=core::array::from_fn(|r|
        core::array::from_fn(|d|pairs[r][2][d&1].mul(pairs[r][3][d>>1])));
    let k=audit[10];let k2=k.square();let k3=k2.mul(k);
    let blocks=[core::array::from_fn(|d|k.mul(raw[0][d]).add(k3.mul(raw[0][d^3]))),
        core::array::from_fn(|d|k2.mul(raw[1][d]))];
    fill_tensor(&pairs[0],blocks[0],&mut factors[..80]);
    fill_tensor(&pairs[1],blocks[1],&mut factors[80..]);
    let a=block_terminal_impl(&pairs[0],alpha,abc,Some(blocks[0])).0;
    let b=block_terminal_impl(&pairs[1],alpha,abc,Some(blocks[1])).0;
    for j in 0..479 {delta[j]=entry(factors,j);}
    // Same cycle traversal as the R33 candidate; only storage acquisition changed.
    let mut seen=[false;479];
    for start in 0..479 {
        if seen[start] {continue;}
        let saved=delta[start];let mut at=start;
        loop {
            let old=delta[at];let next=t.order[at];
            let successor=if next==start {saved}else{delta[next]};
            delta[at]=successor.sub(old);seen[at]=true;
            if next==start {break;}at=next;
        }
    }
    let kernel=r17_weighted_groups::Kernel::new(abc,alpha);
    let d=kernel.prefix_into(delta,sums);
    let masks=core::array::from_fn(|group| {
        let mut mask=0u16;
        for j in 0..16 {let r=t.order[16*group+j];if r!=1023 && t.inactive[r] {mask|=1<<j;}}
        mask
    });
    let other=kernel.binary_masks_into(&masks,sums);
    let pivot=kernel.coordinate(1023);
    let wp=entry(factors,1023);
    core::array::from_fn(|i|a[i].add(b[i]).add(d[i]).sub(wp.mul(other[i])).add(pivot[i]))
}
