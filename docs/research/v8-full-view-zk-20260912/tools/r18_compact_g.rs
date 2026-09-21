//! Compact sparse-G helpers. Current T; no probabilistic/security premise.
use super::{basis_transport,corelib};
use corelib::field::{M31,QM31 as K};
include!("r17_reused_group_geometry.rs");

/// First ordinary point's transported constant/linear entries. The sparse G
/// functional has zero entries 0,1,2 and no pivot correction in code space.
pub(super) fn first_pair(z:&[K;10],use_x:bool)->[K;2] {
    let t=basis_transport::transport();
    let point=corelib::v6_transcript::v6_statement_points(z)[0];
    let entry=|r:usize| (0..10).fold(K::ONE,|v,b|
        v.mul(if r&(1<<(9-b))==0 {K::ONE.sub(point[b])}else{point[b]}));
    let pivot=entry(1023);
    [0,if use_x {2}else{1}].map(|j| {
        let r=t.order[j];let v=entry(r);
        if r!=1023 && t.inactive[r] {v.sub(pivot)}else{v}
    })
}
#[inline(never)]
pub(super) fn terminal(z:&[K;10],abc:[K;3],alpha:[K;4],workspace:&mut[K])->[K;4] {
    assert!(workspace.len()>=399);
    let (coins,sums)=workspace.split_at_mut(271);
    super::r18_sparse_coded_g::coin_weights_into(z,coins);
    let (normal,carry,high)=geometry(abc,alpha);
    super::r18_sparse_coded_g::sparse_terminal(coins,&normal,&carry,&high,sums)
}
