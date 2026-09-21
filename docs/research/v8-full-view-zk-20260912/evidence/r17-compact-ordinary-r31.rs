//! Compact ordinary-channel functional using the retained baseline kernels.
//! No new transcript profile or production caller. G remains a separate channel.
use super::{corelib,basis_transport,r17_weighted_groups};
use corelib::field::QM31 as K;
include!("r17_reused_block_terminal.rs");

struct Tensor {low:[K;16],high:[K;64]}
impl Tensor {
    fn new(pairs:&[[K;2];10],block1:[K;4])->Self {
        let blocks:[[K;4];5]=core::array::from_fn(|r|if r==1 {block1} else {
            core::array::from_fn(|d|pairs[2*r][d&1].mul(pairs[2*r+1][d>>1]))
        });
        let low=core::array::from_fn(|j|blocks[0][j&3].mul(blocks[1][j>>2]));
        let common:[K;16]=core::array::from_fn(|j|blocks[2][j&3].mul(blocks[3][j>>2]));
        let high=core::array::from_fn(|j|common[j&15].mul(blocks[4][j>>4]));
        Self{low,high}
    }
    fn entry(&self,j:usize)->K {self.low[j&15].mul(self.high[j>>4])}
}

pub(super) struct Description {
    pairs:[[[K;2];10];2],blocks:[[K;4];2],tensors:[Tensor;2],
}
impl Description {
    pub(super) fn new(z:&[K;10],kappa:K)->Self {
        let points=corelib::v6_transcript::v6_statement_points(z);
        let pairs:[[[K;2];10];2]=core::array::from_fn(|r|
            core::array::from_fn(|i|[K::ONE.sub(points[r][9-i]),points[r][9-i]]));
        // The retained source XOR12 relationship is checked separately.
        // This is exactly the old fused-row block, not a rank-one assumption.
        let raw:[[K;4];2]=core::array::from_fn(|r|
            core::array::from_fn(|d|pairs[r][2][d&1].mul(pairs[r][3][d>>1])));
        let k2=kappa.square();let k3=k2.mul(kappa);
        let blocks=[core::array::from_fn(|d|kappa.mul(raw[0][d]).add(k3.mul(raw[0][d^3]))),
            core::array::from_fn(|d|k2.mul(raw[1][d]))];
        let tensors=core::array::from_fn(|r|Tensor::new(&pairs[r],blocks[r]));
        Self{pairs,blocks,tensors}
    }
    fn without_inactive(&self,j:usize)->K {
        assert!(j<1024);
        self.tensors[0].entry(j).add(self.tensors[1].entry(j))
    }
    pub(super) fn original_entry(&self,j:usize)->K {
        let value=self.without_inactive(j);
        if basis_transport::transport().inactive[j] {value.add(K::ONE)}else{value}
    }
    pub(super) fn dual_entry(&self,j:usize)->K {
        assert!(j<1024);
        let t=basis_transport::transport();let r=t.order[j];
        let value=self.original_entry(r);
        if r!=1023 && t.inactive[r] {value.sub(self.original_entry(1023))}else{value}
    }
    pub(super) fn terminal(&self,abc:[K;3],alpha:[K;4])->[K;4] {
        let t=basis_transport::transport();
        let a=block_terminal_impl(&self.pairs[0],alpha,abc,Some(self.blocks[0])).0;
        let b=block_terminal_impl(&self.pairs[1],alpha,abc,Some(self.blocks[1])).0;
        // Only the changed prefix is materialized, not a dense/chord/fold vector.
        let prefix:Vec<_>=(0..479).map(|j|self.without_inactive(j)).collect();
        let delta:Vec<_>=(0..479).map(|j|prefix[t.order[j]].sub(prefix[j])).collect();
        let kernel=r17_weighted_groups::Kernel::new(abc,alpha);
        let d=kernel.prefix(&delta);
        let masks=core::array::from_fn(|group| {
            let mut mask=0u16;
            for j in 0..16 {let r=t.order[16*group+j];if r!=1023 && t.inactive[r] {mask|=1<<j;}}
            mask
        });
        let other=kernel.binary_masks(&masks);
        let pivot=kernel.coordinate(1023);
        let wp=self.without_inactive(1023);
        core::array::from_fn(|i|a[i].add(b[i]).add(d[i]).sub(wp.mul(other[i])).add(pivot[i]))
    }
}
