//! Same 271-node G functional: prefix correction plus full geometric terminal.
//! The first 479 weights alone are NOT the G functional. All 271 full-length
//! geometric rows and the original pivot are retained explicitly below.
use super::{corelib,basis_transport,r17_mask_workspace,r17_weighted_groups,r17_g_geometric};
use corelib::field::{QM31 as K,M31};
include!("r17_reused_block_terminal.rs");

#[inline(never)]
fn fill_base(audit:&[K;11],storage:&mut[K])->([[[K;2];10];2],[[K;4];2]) {
    let z=core::array::from_fn(|i|audit[i]);
    let points=corelib::v6_transcript::v6_statement_points(&z);
    let pairs=core::array::from_fn(|r|core::array::from_fn(|i|
        [K::ONE.sub(points[r+1][9-i]),points[r+1][9-i]]));
    let k=audit[10];let k2=k.square();let scales=[k2,k2.mul(k)];
    let blocks=core::array::from_fn(|r|core::array::from_fn(|d|
        scales[r].mul(pairs[r][2][d&1].mul(pairs[r][3][d>>1]))));
    super::r17_compact_workspace::fill_tensor(&pairs[0],blocks[0],&mut storage[..80]);
    super::r17_compact_workspace::fill_tensor(&pairs[1],blocks[1],&mut storage[80..160]);
    (pairs,blocks)
}
#[inline(never)]
fn base_plain(audit:&[K;11],abc:[K;3],alpha:[K;4],storage:&mut[K])->[K;4] {
    let (pairs,blocks)=fill_base(audit,storage);
    let a=block_terminal_impl(&pairs[0],alpha,abc,Some(blocks[0])).0;
    let b=block_terminal_impl(&pairs[1],alpha,abc,Some(blocks[1])).0;
    core::array::from_fn(|i|a[i].add(b[i]))
}

pub(super) struct Description { coins:Vec<K>,workspace:Vec<K>,pivot:K }
impl Description {
    #[inline(never)]
    pub(super) fn new(audit:&[K;11])->Self {
        let mut coins=vec![K::ZERO;271];let mut workspace=vec![K::ZERO;1024];
        let z=core::array::from_fn(|i|audit[i]);
        r17_mask_workspace::compact_prefix(&z,coins.as_mut_slice().try_into().unwrap(),workspace.as_mut_slice().try_into().unwrap());
        let g_pivot=r17_mask_workspace::compact_pivot(coins.as_slice().try_into().unwrap());
        let k=audit[10];
        for coin in &mut coins {*coin=coin.mul(k);}
        let (prefix,rest)=workspace.split_at_mut(479);
        fill_base(audit,&mut rest[..160]);
        let pivot=g_pivot.mul(k).add(super::r17_compact_workspace::entry(&rest[..160],1023));
        for j in 0..479 {
            prefix[j]=prefix[j].mul(k).add(super::r17_compact_workspace::entry(&rest[..160],j));
        }
        Self{coins,workspace,pivot}
    }
    pub(super) fn dual_pair(&self,use_x:bool)->[K;2] {
        let t=basis_transport::transport();
        [0,if use_x {2}else{1}].map(|j| {
            let r=t.order[j];assert!(r<479);
            let v=self.workspace[r];
            // Both inactive indicators cancel at every non-pivot inactive row.
            if t.inactive[r] {v.sub(self.pivot)}else{v}
        })
    }
    #[inline(never)]
    pub(super) fn terminal(mut self,audit:&[K;11],abc:[K;3],alpha:[K;4])->[K;4] {
        let (delta,rest)=self.workspace.split_at_mut(479);
        let (factors,sums)=rest.split_at_mut(160);
        let mut plain=base_plain(audit,abc,alpha,factors);
        let geometric=r17_g_geometric::Kernel::new(alpha,abc);
        for start in (0..271).step_by(4) {
            let coins=core::array::from_fn(|i|self.coins.get(start+i).copied().unwrap_or(K::ZERO));
            let values:[[K;4];4]=core::array::from_fn(|i|if start+i<271 {
                geometric.terminal(M31((start+i+1) as u32))
            }else{[K::ZERO;4]});
            for j in 0..4 {plain[j]=plain[j].add(corelib::field::qm31_sum_products4(
                coins,core::array::from_fn(|i|values[i][j])));}
        }
        let t=basis_transport::transport();
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
        let masks=core::array::from_fn(|g| {
            let mut mask=0u16;
            for j in 0..16 {let r=t.order[16*g+j];if r!=1023 && t.inactive[r] {mask|=1<<j;}}
            mask
        });
        let other=kernel.binary_masks_into(&masks,sums);
        let pivot=kernel.coordinate(1023);
        core::array::from_fn(|j|plain[j].add(d[j]).sub(self.pivot.mul(other[j])).add(pivot[j]))
    }
}
