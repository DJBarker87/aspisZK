//! R18 shared ordinary and first-point terminal, research profile only.
//!
//! `A` is the retained ordinary functional (inactive correction, kappa-scaled
//! three-point MLE, current T, pivot correction); `E` is the same map with the
//! first statement-point MLE and no inactive `+1`. The caller provides one
//! reused 1024-entry workspace. No allocation after source map initialization.
use super::{corelib, basis_transport, r17_weighted_groups};
use corelib::field::QM31 as K;
include!("r17_reused_block_terminal.rs");

#[inline(never)]
fn fill_tensor(pairs:&[[K;2];10], block1:[K;4], storage:&mut[K]) {
    assert_eq!(storage.len(),80);
    let blocks:[[K;4];5]=core::array::from_fn(|r|if r==1 {block1} else {
        core::array::from_fn(|d|pairs[2*r][d&1].mul(pairs[2*r+1][d>>1]))
    });
    for j in 0..16 { storage[j]=blocks[0][j&3].mul(blocks[1][j>>2]); }
    let common:[K;16]=core::array::from_fn(|j|blocks[2][j&3].mul(blocks[3][j>>2]));
    for j in 0..64 { storage[16+j]=common[j&15].mul(blocks[4][j>>4]); }
}
#[inline(always)] fn entry(f:&[K],off:usize,j:usize)->K {
    let first=f[off+(j&15)].mul(f[off+16+(j>>4)]);
    if off==0 {first.add(f[80+(j&15)].mul(f[96+(j>>4)]))}else{first}
}

fn prepare_rows(audit:&[K;11],abc:[K;3],alpha:[K;4],factors:&mut[K])->([K;4],[K;4]) {
    assert_eq!(factors.len(),240);
    let z=core::array::from_fn(|i|audit[i]);
    let points=corelib::v6_transcript::v6_statement_points(&z);
    let pairs:[[[K;2];10];2]=core::array::from_fn(|r|core::array::from_fn(|i|[
        K::ONE.sub(points[r][9-i]),points[r][9-i]]));
    let raw:[[K;4];2]=core::array::from_fn(|r|core::array::from_fn(|d|
        pairs[r][2][d&1].mul(pairs[r][3][d>>1])));
    let k=audit[10]; let k2=k.square(); let k3=k2.mul(k);
    let blocks=[core::array::from_fn(|d|k.mul(raw[0][d]).add(k3.mul(raw[0][d^3]))),
        core::array::from_fn(|d|k2.mul(raw[1][d]))];
    fill_tensor(&pairs[0],blocks[0],&mut factors[..80]);
    fill_tensor(&pairs[1],blocks[1],&mut factors[80..160]);
    // E is exactly the first source MLE, with no kappa or inactive +1.
    fill_tensor(&pairs[0],raw[0],&mut factors[160..240]);
    let a=block_terminal_impl(&pairs[0],alpha,abc,Some(blocks[0])).0;
    let b=block_terminal_impl(&pairs[1],alpha,abc,Some(blocks[1])).0;
    let e=block_terminal_impl(&pairs[0],alpha,abc,None).0;
    (core::array::from_fn(|i|a[i].add(b[i])),e)
}

fn cycle(delta:&mut[K], order:&[usize]) {
    assert_eq!(delta.len(),479);
    assert_eq!(order.len(),1024);
    let mut seen=[false;479];
    for start in 0..479 { if seen[start] {continue;}
        let saved=delta[start]; let mut at=start;
        loop { let old=delta[at]; let next=order[at];
            let successor=if next==start {saved}else{delta[next]};
            delta[at]=successor.sub(old); seen[at]=true;
            if next==start {break;} at=next;
        }
    }
}

fn one_terminal(factors:&[K], off:usize, plain:[K;4],
    delta:&mut[K], sums:&mut[K], kernel:&r17_weighted_groups::Kernel,
    inactive:[K;4], pivot:[K;4], add_pivot:bool)->[K;4] {
    let t=basis_transport::transport();
    for j in 0..479 {delta[j]=entry(factors,off,j);}
    cycle(delta,&t.order);
    let d=kernel.prefix_into(delta,sums);
    let wp=entry(factors,off,1023);
    core::array::from_fn(|i|plain[i].add(d[i]).sub(wp.mul(inactive[i]))
        .add(if add_pivot {pivot[i]} else {K::ZERO}))
}

/// Return exactly four folded coefficients for A and E, with shared geometry
/// and fixed-mask contraction. Both permutation corrections use the same T.
#[inline(never)]
pub(super) fn terminal_pair(
    audit: &[K; 11],
    abc: [K; 3],
    alpha: [K; 4],
    workspace: &mut [K],
) -> [[K; 4]; 2] {
    assert!(workspace.len()>=1024);
    let t=basis_transport::transport();
    let (delta,rest)=workspace.split_at_mut(479);
    let (factors,sums)=rest.split_at_mut(240);
    assert!(sums.len()>=128);
    let (plain_a,plain_e)=prepare_rows(audit,abc,alpha,&mut factors[..240]);
    let kernel=r17_weighted_groups::Kernel::new(abc,alpha);
    let masks=core::array::from_fn(|group|{let mut m=0u16;
        for j in 0..16 {let r=t.order[16*group+j];if r!=1023&&t.inactive[r]{m|=1<<j;}}m});
    let inactive=kernel.binary_masks_into(&masks,&mut sums[..128]);
    let pivot=kernel.coordinate(1023);
    let a=one_terminal(factors,0,plain_a,delta,&mut sums[..128],&kernel,inactive,pivot,true);
    let e=one_terminal(factors,160,plain_e,delta,&mut sums[..128],&kernel,inactive,pivot,false);
    [a,e]
}
