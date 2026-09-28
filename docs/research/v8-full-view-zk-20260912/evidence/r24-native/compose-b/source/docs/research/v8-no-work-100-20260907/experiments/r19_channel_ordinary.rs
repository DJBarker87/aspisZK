//! R18 shared ordinary and first-point terminal, research profile only.
//!
//! `A` is the retained ordinary functional (inactive correction, kappa-scaled
//! three-point MLE, current T, pivot correction); `E` is the same map with the
//! first statement-point MLE and no inactive `+1`. The caller provides one
//! reused 1024-entry workspace. No allocation after source map initialization.
use super::{corelib, basis_transport, r17_weighted_groups};
use corelib::field::QM31 as K;
include!("r17_reused_block_terminal.rs");
include!("r18_minimal_support.rs");

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

fn prepare_rows(audit:&[K;11],abc:[K;3],alpha:[K;4],beta:K,factors:&mut[K])->[K;4] {
    assert_eq!(factors.len(),240);
    let z=core::array::from_fn(|i|audit[i]);
    let points=corelib::v6_transcript::v6_statement_points(&z);
    let pairs:[[[K;2];10];2]=core::array::from_fn(|r|core::array::from_fn(|i|[
        K::ONE.sub(points[r][9-i]),points[r][9-i]]));
    let raw:[[K;4];2]=core::array::from_fn(|r|core::array::from_fn(|d|
        pairs[r][2][d&1].mul(pairs[r][3][d>>1])));
    let k=audit[10]; let k2=k.square(); let k3=k2.mul(k);
    let blocks=[core::array::from_fn(|d|K::ONE.sub(beta).mul(k).mul(raw[0][d]).add(k3.mul(raw[0][d^3]))),
        core::array::from_fn(|d|k2.mul(raw[1][d]))];
    fill_tensor(&pairs[0],blocks[0],&mut factors[..80]);
    fill_tensor(&pairs[1],blocks[1],&mut factors[80..160]);
    // E is exactly the first source MLE, with no kappa or inactive +1.
    let a=block_terminal_impl(&pairs[0],alpha,abc,Some(blocks[0])).0;
    let b=block_terminal_impl(&pairs[1],alpha,abc,Some(blocks[1])).0;
    core::array::from_fn(|i|a[i].add(b[i]))
}

fn cycle(delta:&mut[K], order:&[usize]) {
    assert_eq!(delta.len(),163);
    assert_eq!(order.len(),1024);
    let mut seen=[false;163];
    for start in 0..163 { if seen[start] {continue;}
        let saved=delta[start]; let mut at=start;
        loop { let old=delta[at]; let next=NEXT[at];
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
    for j in 0..163 {delta[j]=entry(factors,off,SUPPORT[j]);}
    cycle(delta,&t.order);
    let d=kernel.selected_into(&SUPPORT,delta,sums);
    let wp=entry(factors,off,1023);
    core::array::from_fn(|i|plain[i].add(d[i]).sub(wp.mul(inactive[i]))
        .add(if add_pivot {pivot[i]} else {K::ZERO}))
}

/// Return exactly four folded coefficients for A and E, with shared geometry
/// and fixed-mask contraction. Both permutation corrections use the same T.
#[inline(never)]
pub(super) fn terminal(
    audit: &[K; 11],
    abc: [K; 3],
    alpha: [K; 4],
    beta: K,
    workspace: &mut [K],
) -> [K;4] {
    assert!(workspace.len()>=1024);
    let t=basis_transport::transport();
    let (delta,rest)=workspace.split_at_mut(163);
    let (factors,sums)=rest.split_at_mut(240);
    assert!(sums.len()>=128);
    let plain_a=prepare_rows(audit,abc,alpha,beta,&mut factors[..240]);
    let kernel=r17_weighted_groups::Kernel::new(abc,alpha);
    let masks=core::array::from_fn(|group|{let mut m=0u16;
        for j in 0..16 {let r=t.order[16*group+j];if r!=1023&&t.inactive[r]{m|=1<<j;}}m});
    let inactive=kernel.binary_masks_into(&masks,&mut sums[..128]);
    let pivot=kernel.coordinate(1023);
    let a=one_terminal(factors,0,plain_a,delta,&mut sums[..128],&kernel,inactive,pivot,true);
    a
}

#[inline(never)]
pub(super) fn terminal_shared(
    audit: &[K; 11],
    abc: [K; 3],
    alpha: [K; 4],
    beta: K,
    workspace: &mut [K],
    kernel: &r17_weighted_groups::Kernel,
) -> [K;4] {
    assert!(workspace.len()>=1024);
    let t=basis_transport::transport();
    let (delta,rest)=workspace.split_at_mut(163);
    let (factors,sums)=rest.split_at_mut(240);
    assert!(sums.len()>=128);
    let plain_a=prepare_rows(audit,abc,alpha,beta,&mut factors[..240]);
    let masks=core::array::from_fn(|group|{let mut m=0u16;
        for j in 0..16 {let r=t.order[16*group+j];if r!=1023&&t.inactive[r]{m|=1<<j;}}m});
    let inactive=kernel.binary_masks_into(&masks,&mut sums[..128]);
    let pivot=kernel.coordinate(1023);
    let a=one_terminal(factors,0,plain_a,delta,&mut sums[..128],kernel,inactive,pivot,true);
    a
}

#[inline(never)]
fn block_terminal_scalar_impl(w: &[[K; 2]; 10], alpha: [K; 4], [a,b,c]:[K;3],block1:Option<[K;4]>,finals:&[K;4])->K{
    let mut count = 0usize;
    macro_rules! m {
        ($x:expr,$y:expr) => {{
            count += 1;
            ($x).mul($y)
        }};
    }
    let powers: [(K, K); 4] = core::array::from_fn(|j| {
        let a2 = m!(alpha[j], alpha[j]);
        (a2, m!(a2, alpha[j]))
    });
    let (a2, a3) = powers[0];
    let ax = alpha[0];
    let [x0, x1] = w[1];
    let [y0, y1] = w[0];
    let i0 = x0.add(m!(a2, x1));
    let c0 = m!(a2, x0).half();
    let s0 = x1.add(c0);
    let i1 = m!(a3, x0).add(m!(ax, x1));
    let c1 = m!(ax, x0).half();
    let s1 = m!(a3, x1).add(c1);
    let y0i1 = m!(y0, i1);
    let u = m!(a, m!(y0, i0).add(m!(y1, i1)))
        .add(m!(b, m!(y0, s0).add(m!(y1, s1))))
        .add(m!(c, m!(y1, i0).add(y0i1.half())));
    let v = m!(b, m!(y0, c0).add(m!(y1, c1))).sub(m!(c, y0i1).half());
    let mut identity = K::ONE;
    let mut ended = K::ZERO;
    let mut carry = K::ONE;
    for round in 1..4 {
        let k = 2 * round;
        let z = if round==1 && block1.is_some(){block1.unwrap()}else{[
            m!(w[k][0], w[k + 1][0]),
            m!(w[k][1], w[k + 1][0]),
            m!(w[k][0], w[k + 1][1]),
            m!(w[k][1], w[k + 1][1]),
        ]};
        let (a2, a3) = powers[round];
        let ax = alpha[round];
        let same = z[0].add(m!(a3, z[1])).add(m!(a2, z[2])).add(m!(ax, z[3]));
        let stop = z[1]
            .add(m!(a3, z[0].add(z[2])).half())
            .add(m!(a2, z[3]))
            .add(m!(ax, z[2].half().add(z[0].half().half())));
        let next = m!(ax, z[0]).half().half();
        identity = m!(identity, same);
        ended = m!(ended, same).add(m!(carry, stop));
        carry = m!(carry, next);
    }
    let common = m!(u, identity).add(m!(v, ended));
    let active = m!(v, carry);
    let z = [
        m!(w[8][0], w[9][0]),
        m!(w[8][1], w[9][0]),
        m!(w[8][0], w[9][1]),
        m!(w[8][1], w[9][1]),
    ];
    let stop = [
        z[1],
        z[0].add(z[2]).half(),
        z[3],
        z[2].half().add(z[0].half().half()),
    ];
    let mut result=common.mul(corelib::field::qm31_sum_products4(z,*finals))
        .add(active.mul(corelib::field::qm31_sum_products4(stop,*finals)));
    for _ in 0..8 {result=result.half();}
    let _=count;result
}
#[inline(never)]
fn prepare_rows_scalar(audit:&[K;11],abc:[K;3],alpha:[K;4],beta:K,factors:&mut[K],finals:&[K;4])->K {
    assert_eq!(factors.len(),240);
    let z=core::array::from_fn(|i|audit[i]);
    let points=corelib::v6_transcript::v6_statement_points(&z);
    let pairs:[[[K;2];10];2]=core::array::from_fn(|r|core::array::from_fn(|i|[
        K::ONE.sub(points[r][9-i]),points[r][9-i]]));
    let raw:[[K;4];2]=core::array::from_fn(|r|core::array::from_fn(|d|
        pairs[r][2][d&1].mul(pairs[r][3][d>>1])));
    let k=audit[10]; let k2=k.square(); let k3=k2.mul(k);
    let blocks=[core::array::from_fn(|d|K::ONE.sub(beta).mul(k).mul(raw[0][d]).add(k3.mul(raw[0][d^3]))),
        core::array::from_fn(|d|k2.mul(raw[1][d]))];
    fill_tensor(&pairs[0],blocks[0],&mut factors[..80]);
    fill_tensor(&pairs[1],blocks[1],&mut factors[80..160]);
    // E is exactly the first source MLE, with no kappa or inactive +1.
    let a=block_terminal_scalar_impl(&pairs[0],alpha,abc,Some(blocks[0]),finals);
    let b=block_terminal_scalar_impl(&pairs[1],alpha,abc,Some(blocks[1]),finals);
    a.add(b)
}
include!("r22_scalar.rs");
